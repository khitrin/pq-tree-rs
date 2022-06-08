use crate::errors::*;
use crate::node::*;
use crate::rel::*;
use crate::sublist::SubCircularList;
use crate::{NodeLabel, NodeMark, PQTree, TreeNode, ABSENT, PSEUDONODE};
use enum_map::{enum_map, EnumMap};
use std::collections::{HashSet, VecDeque};
use std::hash::Hash;

impl TreeNode {
    fn parent_of_unblocked(&self) -> usize {
        match self.rel {
            Rel::Root => ABSENT,
            Rel::P(ChildOfP { parent, .. })
            | Rel::LQ(LeftChildOfQ { parent, .. })
            | Rel::RQ(RightChildOfQ { parent, .. }) => parent,
            Rel::IQ(InteriorChildOfQ { parent_of_unblocked, .. }) => {
                debug_assert_ne!(self.red.mark, NodeMark::Blocked);
                parent_of_unblocked
            }
        }
    }
}

impl<T: Clone + Eq + Hash> PQTree<T> {
    pub(crate) fn bubble(&mut self, s_nodes: &[usize]) -> Result<(), ReductionError<T>> {
        self.nodes.iter_mut().for_each(|n| n.red = Default::default());

        let mut block_count = 0usize;
        let mut blocked = HashSet::new();
        let mut off_the_top = 0usize;

        let mut queue: VecDeque<usize> = s_nodes.to_vec().into();

        fn unblock_adjacent(
            nodes: &mut [TreeNode],
            parent: usize,
            first_blocked: Option<usize>,
            left: bool,
            blocked: &mut HashSet<usize>,
        ) -> Option<usize> {
            let mut last_unblocked = None;
            if let Some(mut b) = first_blocked {
                loop {
                    nodes[b].red.mark = NodeMark::Unblocked;
                    nodes[parent].red.pertinent_child_count += 1;
                    blocked.remove(&b);
                    last_unblocked = Some(b);

                    // only interior-of-q nodes can be blocked
                    if let Rel::IQ(iq) = &mut nodes[b].rel {
                        iq.parent_of_unblocked = parent;
                        b = if left { iq.left } else { iq.right };
                    } else {
                        break;
                    }

                    if nodes[b].red.mark != NodeMark::Blocked {
                        break;
                    }
                }
            }
            last_unblocked
        }

        while queue.len() + block_count + off_the_top > 1 {
            let x = if let Some(x_) = queue.pop_front() {
                x_
            } else {
                return self.irreducible_error();
            };

            let mut rel = self.nodes[x].rel;
            let (l_blocked, r_blocked) = if let Rel::IQ(iq) = &mut rel {
                let left_mark = self.nodes[iq.left].red.mark;
                let right_mark = self.nodes[iq.right].red.mark;

                if left_mark == NodeMark::Unblocked {
                    self.nodes[x].red.mark = NodeMark::Unblocked;
                    iq.parent_of_unblocked = self.nodes[iq.left].parent_of_unblocked();
                } else if right_mark == NodeMark::Unblocked {
                    self.nodes[x].red.mark = NodeMark::Unblocked;
                    iq.parent_of_unblocked = self.nodes[iq.right].parent_of_unblocked();
                } else {
                    self.nodes[x].red.mark = NodeMark::Blocked;
                }

                (
                    if left_mark == NodeMark::Blocked { Some(iq.left) } else { None },
                    if right_mark == NodeMark::Blocked { Some(iq.right) } else { None },
                )
            } else {
                self.nodes[x].red.mark = NodeMark::Unblocked;

                match &rel {
                    Rel::RQ(rq) => {
                        (if self.nodes[rq.left].red.mark == NodeMark::Blocked { Some(rq.left) } else { None }, None)
                    }
                    Rel::LQ(lq) => {
                        (None, if self.nodes[lq.right].red.mark == NodeMark::Blocked { Some(lq.right) } else { None })
                    }
                    _ => (None, None),
                }
            };
            self.nodes[x].rel = rel;

            let bs = {
                let mut bs = 0;
                if l_blocked.is_some() {
                    bs += 1
                };
                if r_blocked.is_some() {
                    bs += 1
                };
                bs
            };

            if self.nodes[x].red.mark == NodeMark::Unblocked {
                let y = self.nodes[x].parent_of_unblocked();

                unblock_adjacent(&mut self.nodes, y, l_blocked, true, &mut blocked);
                unblock_adjacent(&mut self.nodes, y, r_blocked, false, &mut blocked);

                if y == ABSENT {
                    off_the_top = 1;
                } else {
                    self.nodes[y].red.pertinent_child_count += 1;
                    if self.nodes[y].red.mark == NodeMark::Unmarked {
                        queue.push_back(y);
                        self.nodes[y].red.mark = NodeMark::Queued;
                    }
                }
                block_count -= bs;
            } else {
                blocked.insert(x);
                block_count += 1;
                block_count -= bs; // usize trick
            }
        }

        if block_count > 1 {
            return self.irreducible_error();
        }

        if let Some(&x) = blocked.iter().next() {
            // create pseudonode from block

            let left = unblock_adjacent(&mut self.nodes, PSEUDONODE, Some(x), true, &mut blocked)
                .expect("no nodes unblocked, but blocked nodes exists");
            let right = unblock_adjacent(&mut self.nodes, PSEUDONODE, Some(x), false, &mut blocked)
                .expect("no nodes unblocked, but blocked nodes exists");
            self.nodes[PSEUDONODE].node = Node::Q(QNode { left, right });
            self.nodes[PSEUDONODE].red.pertinent_child_count -= 1; // unblock_adjacent have touched central node two times
        }

        Ok(())
    }

    pub(crate) fn reduce(&mut self, s_nodes: &[usize]) -> Result<(), ReductionError<T>> {
        // todo: optimize?
        self.nodes.iter_mut().for_each(|n| n.red.label = NodeLabel::Empty);

        let mut queue: VecDeque<usize> = s_nodes.to_vec().into();

        s_nodes.iter().for_each(|&node| {
            self.nodes[node].red.pertinent_leaf_count = 1;
            self.label(node, NodeLabel::Full);
        });

        while let Some(x) = queue.pop_front() {
            let root = self.nodes[x].red.pertinent_leaf_count >= s_nodes.len();

            if !root {
                debug_assert_eq!(self.nodes[x].red.mark, NodeMark::Unblocked);

                let y = self.nodes[x].parent_of_unblocked();

                self.nodes[y].red.pertinent_leaf_count += self.nodes[x].red.pertinent_leaf_count;
                self.nodes[y].red.pertinent_child_count -= 1;

                if self.nodes[y].red.pertinent_child_count == 0 {
                    queue.push_back(y);
                }
            }

            if !match self.nodes[x].node {
                Node::P(PNode { child }) => self.apply_p_templates(x, child, root),
                Node::Q(QNode { left, right }) => self.apply_q_templates(x, left, right, root),
                Node::L => self.apply_l_templates(x, root),
            } {
                return self.irreducible_error();
            };
        }
        Ok(())
    }

    fn apply_p_templates(&mut self, x: usize, first_child: usize, root: bool) -> bool {
        let split = self.split_p_children(first_child);

        if !split[NodeLabel::DoublyPartial].is_empty() {
            return self.fail();
        }

        let full = split[NodeLabel::Full].len();
        let empty = split[NodeLabel::Empty].len();
        let singly = split[NodeLabel::SinglyPartial].len();

        if singly == 0 {
            if empty > 0 && full == 0 {
                // P0
                return self.label(x, NodeLabel::Empty);
            }

            if full > 0 && empty == 0 {
                // P1
                if root {
                    self.label(x, NodeLabel::Full);
                    return self.mark_as_pertinent_root(x);
                } else {
                    return self.label(x, NodeLabel::Full);
                }
            }

            if full > 0 && empty > 0 {
                let full_sub_node = self.add_sub_p_node(&split[NodeLabel::Full], NodeLabel::Full);

                if root {
                    // P2
                    self.recombine_p(x, &split[NodeLabel::Empty], full_sub_node);
                    return self.mark_as_pertinent_root(full_sub_node);
                } else {
                    // P3
                    let empty_sub_node = self.add_sub_p_node(&split[NodeLabel::Empty], NodeLabel::Empty);
                    self.nodes[x].node = Node::Q(QNode { left: empty_sub_node, right: full_sub_node });

                    self.nodes[empty_sub_node].rel = Rel::LQ(LeftChildOfQ { parent: x, right: full_sub_node });
                    self.nodes[full_sub_node].rel = Rel::RQ(RightChildOfQ { parent: x, left: empty_sub_node });
                    return self.label(x, NodeLabel::SinglyPartial);
                }
            }
        } else if singly == 1 {
            // P4 or P5
            let sp = split[NodeLabel::SinglyPartial].first();
            let full_left = self.nodes[self.nodes[sp].node.as_q().left].red.label == NodeLabel::Full;

            if full > 0 {
                let full_sub_node = self.add_sub_p_node(&split[NodeLabel::Full], NodeLabel::Full);
                self.attach_to_q(sp, full_sub_node, full_left);
            }

            if root {
                // P4
                debug_assert!(full != 0, "root with single 'singly partial' child must have at least one full child !");
                if empty > 0 {
                    self.recombine_p(x, &split[NodeLabel::Empty], sp);
                    return self.mark_as_pertinent_root(sp);
                } else {
                    self.replace_p_by_q(x, sp);
                    return self.mark_as_pertinent_root(x);
                }
            } else {
                // P5
                if empty > 0 {
                    let full_empty_node = self.add_sub_p_node(&split[NodeLabel::Empty], NodeLabel::Empty);
                    self.attach_to_q(sp, full_empty_node, !full_left);
                }

                self.replace_p_by_q(x, sp);
                return self.confirm_p5_replacement(x);
            }
        } else if root && singly == 2 {
            // P6
            let (left, right) = {
                let sp1 = split[NodeLabel::SinglyPartial].first();
                let sp2 = split[NodeLabel::SinglyPartial].last();

                let sp1_empty_left = self.nodes[self.nodes[sp1].node.as_q().left].red.label == NodeLabel::Empty;
                let sp2_empty_left = self.nodes[self.nodes[sp2].node.as_q().left].red.label == NodeLabel::Empty;

                match (sp1_empty_left, sp2_empty_left) {
                    (true, false) => (sp1, sp2),
                    (false, true) => (sp2, sp1),
                    (true, true) => {
                        self.reverse_q(sp2);
                        (sp1, sp2)
                    }
                    (false, false) => {
                        self.reverse_q(sp1);
                        (sp1, sp2)
                    }
                }
            };

            debug_assert_ne!(left, PSEUDONODE);

            if full > 0 {
                let full_sub_node = self.add_sub_p_node(&split[NodeLabel::Full], NodeLabel::Full);
                self.attach_to_q(left, full_sub_node, false);
            }

            let rightmost_in_left = self.nodes[left].node.as_q().right;
            let leftmost_in_right = self.nodes[right].node.as_q().left;

            self.nodes[rightmost_in_left].rel = self.nodes[rightmost_in_left].rel.as_rq().to_iq(leftmost_in_right);
            self.nodes[leftmost_in_right].rel = self.nodes[leftmost_in_right].rel.as_lq().to_iq(rightmost_in_left);

            // right will be recycled, not changes needed
            let rightmost_in_right = self.nodes[right].node.as_q().right;

            self.nodes[left].node.as_mut_q().right = rightmost_in_right;
            self.nodes[rightmost_in_right].rel.as_mut_rq().parent = left;

            self.label(left, NodeLabel::DoublyPartial);

            self.recycle_node(right);

            if empty > 0 {
                self.recombine_p(x, &split[NodeLabel::Empty], left);
                return self.mark_as_pertinent_root(left);
            } else {
                self.replace_p_by_q(x, left);
                return self.mark_as_pertinent_root(x);
            }
        }

        self.fail()
    }

    fn apply_q_templates(&mut self, x: usize, left: usize, right: usize, root: bool) -> bool {
        enum State {
            Initial,
            E,
            F,
            SP(usize),
            EF,
            FE,
            EFE,
            // FEF -- prohibited state, fail immediately
        }

        let mut state = State::Initial;
        let mut next = Some(left);
        while let Some(current) = next {
            next = if current == right { None } else { Some(self.nodes[current].rel.right()) };

            let label = self.nodes[current].red.label;

            state = match (state, label) {
                (_, NodeLabel::DoublyPartial) => return self.fail(),
                (State::Initial, NodeLabel::Empty) => State::E,
                (State::Initial, NodeLabel::Full) => State::F,
                (State::Initial, NodeLabel::SinglyPartial) => State::SP(current),

                (s @ (State::E | State::FE | State::EFE), NodeLabel::Empty)
                | (s @ (State::F | State::EF), NodeLabel::Full) => s,

                (State::E, NodeLabel::Full) => State::EF,
                (State::F, NodeLabel::Empty) => State::FE,

                (State::EF, NodeLabel::Empty) => State::EFE,

                (State::EFE | State::FE, NodeLabel::Full | NodeLabel::SinglyPartial) => return self.fail(),

                (State::SP(left_sp), NodeLabel::Empty) => {
                    self.merge_sp_to_parent_q(left_sp, false);

                    State::FE
                }

                (s @ (State::F | State::EF), NodeLabel::SinglyPartial) => {
                    self.merge_sp_to_parent_q(current, false);

                    match s {
                        State::F => State::FE,
                        State::EF => State::EFE,
                        _ => unreachable!(),
                    }
                }

                (State::SP(left_sp), NodeLabel::Full) => {
                    self.merge_sp_to_parent_q(left_sp, true);

                    State::EF
                }

                (State::E, NodeLabel::SinglyPartial) => {
                    self.merge_sp_to_parent_q(current, true);

                    State::EF
                }

                (State::SP(left_sp), NodeLabel::SinglyPartial) => {
                    self.merge_sp_to_parent_q(left_sp, true);
                    self.merge_sp_to_parent_q(current, false);

                    State::EFE
                }
            };
        }

        if root {
            self.mark_as_pertinent_root(x);
        }

        return match state {
            State::Initial => unreachable!(),
            State::SP(_) => panic!("single child in Q node"),

            State::E => self.label(x, NodeLabel::Empty), // Q0
            State::F => self.label(x, NodeLabel::Full),  // Q1
            State::EF | State::FE => self.label(x, NodeLabel::SinglyPartial), // Q2
            State::EFE => self.label(x, NodeLabel::DoublyPartial), // Q3
        };
    }

    fn apply_l_templates(&mut self, x: usize, root: bool) -> bool {
        if root {
            self.mark_as_pertinent_root(x)
        } else {
            self.confirm_l1(x)
        }
    }

    fn confirm_l1(&mut self, _x: usize) -> bool {
        true
    }

    fn label(&mut self, x: usize, label: NodeLabel) -> bool {
        self.nodes[x].red.label = label;
        true
    }

    fn mark_as_pertinent_root(&mut self, pertinent: usize) -> bool {
        self.pertinent_root = Some(pertinent);
        true
    }

    fn confirm_p5_replacement(&mut self, _x: usize) -> bool {
        true
    }

    fn fail(&mut self) -> bool {
        false
    }

    fn irreducible_error(&mut self) -> Result<(), ReductionError<T>> {
        Err(ReductionError::IrreducibleTree)
    }

    fn split_p_children(&mut self, first_child: usize) -> EnumMap<NodeLabel, SubCircularList> {
        let mut map = enum_map! {
            NodeLabel::Empty => SubCircularList::new(),
            NodeLabel::Full => SubCircularList::new(),
            NodeLabel::SinglyPartial => SubCircularList::new(),
            NodeLabel::DoublyPartial => SubCircularList::new(),
        };

        // half-and-one loop
        let mut prev_label = self.nodes[first_child].red.label;
        map[prev_label].add(first_child);

        let mut current = self.nodes[first_child].rel.as_p().next;

        while current != first_child {
            let label = self.nodes[current].red.label;
            if label != prev_label {
                // prev pointer targets to current, but it isn't good, wrap previous list
                self.nodes[map[prev_label].last()].rel.as_mut_p().next = map[prev_label].first();

                // continue old wrapped list to current
                if !map[label].is_empty() {
                    self.nodes[map[label].last()].rel.as_mut_p().next = current;
                }
                prev_label = label;
            }

            map[label].add(current);
            current = self.nodes[current].rel.as_p().next;
        }

        // wrap last accessed list
        self.nodes[map[prev_label].last()].rel.as_mut_p().next = map[prev_label].first();

        map
    }

    fn add_sub_p_node(&mut self, children: &SubCircularList, label: NodeLabel) -> usize {
        if children.len() == 1 {
            children.first() // parent must be changed by caller
        } else {
            let new_p = self.add_node(TreeNode {
                rel: Rel::Root, // parent must be changed by caller
                node: Node::P(PNode { child: children.first() }),
                red: Default::default(),
            });

            self.label(new_p, label);

            let mut current = children.first();

            loop {
                self.nodes[current].rel.as_mut_p().parent = new_p;
                current = self.nodes[current].rel.as_p().next;
                if current == children.first() {
                    break;
                }
            }

            new_p
        }
    }

    fn recombine_p(&mut self, p: usize, empty: &SubCircularList, full: usize) {
        self.nodes[p].node.as_mut_p().child = empty.first();
        self.nodes[empty.last()].rel.as_mut_p().next = full;
        self.nodes[full].rel = Rel::P(ChildOfP { parent: p, next: empty.first() });
    }

    fn attach_to_q(&mut self, q: usize, child: usize, to_left: bool) {
        if to_left {
            let old_left = self.nodes[q].node.as_q().left;
            self.nodes[child].rel = Rel::LQ(LeftChildOfQ { parent: q, right: old_left });
            self.nodes[old_left].rel = self.nodes[old_left].rel.as_lq().to_iq(child);
            self.nodes[q].node.as_mut_q().left = child;
        } else {
            let old_right = self.nodes[q].node.as_q().right;
            self.nodes[child].rel = Rel::RQ(RightChildOfQ { parent: q, left: old_right });
            self.nodes[old_right].rel = self.nodes[old_right].rel.as_rq().to_iq(child);
            self.nodes[q].node.as_mut_q().right = child;
        }
    }

    fn reverse_q(&mut self, q: usize) {
        debug_assert_ne!(q, PSEUDONODE);
        let mut current = self.nodes[self.nodes[q].node.as_q().left].rel.as_lq().right;
        while let Rel::IQ(iq) = &mut self.nodes[current].rel {
            current = iq.right;
            (iq.left, iq.right) = (iq.right, iq.left);
        }

        let (left, right) = {
            let node = self.nodes[q].node.as_mut_q();
            (node.left, node.right) = (node.right, node.left);
            (node.left, node.right)
        };

        let tmp1 = self.nodes[left].rel.as_rq().left;
        let tmp2 = self.nodes[right].rel.as_lq().right;
        self.nodes[left].rel = Rel::LQ(LeftChildOfQ { parent: q, right: tmp1 });
        self.nodes[right].rel = Rel::RQ(RightChildOfQ { parent: q, left: tmp2 });
    }

    fn replace_p_by_q(&mut self, target: usize, source: usize) {
        debug_assert_ne!(target, PSEUDONODE); // pseudonode is always Q-node

        self.nodes[target].node = self.nodes[source].node;
        self.nodes[target].red.label = self.nodes[source].red.label;

        let leftmost = self.nodes[target].node.as_q().left;
        let rightmost = self.nodes[target].node.as_q().right;

        self.nodes[leftmost].rel.as_mut_lq().parent = target;
        self.nodes[rightmost].rel.as_mut_rq().parent = target;

        self.recycle_node(source);
    }

    fn ensure_q_empty_left(&mut self, q: usize) {
        if self.nodes[self.nodes[q].node.as_q().left].red.label != NodeLabel::Empty {
            self.reverse_q(q);
        }
    }

    fn ensure_q_empty_right(&mut self, q: usize) {
        if self.nodes[self.nodes[q].node.as_q().right].red.label != NodeLabel::Empty {
            self.reverse_q(q);
        }
    }

    fn merge_sp_to_parent_q(&mut self, child: usize, empty_then_full: bool) {
        if empty_then_full {
            self.ensure_q_empty_left(child);
        } else {
            self.ensure_q_empty_right(child);
        }

        let rel_to_parent = self.nodes[child].rel;
        let leftmost = self.nodes[child].node.as_q().left;
        let rightmost = self.nodes[child].node.as_q().right;

        match rel_to_parent {
            Rel::LQ(lq) => {
                // child is leftmost child of parent
                self.nodes[lq.parent].node.as_mut_q().left = leftmost;
                self.nodes[leftmost].rel.as_mut_lq().parent = lq.parent;

                self.nodes[rightmost].rel = self.nodes[rightmost].rel.as_rq().to_iq(lq.right);
                *self.nodes[lq.right].rel.mut_left() = rightmost;
            }
            Rel::RQ(rq) => {
                self.nodes[rq.parent].node.as_mut_q().right = rightmost;
                self.nodes[rightmost].rel.as_mut_rq().parent = rq.parent;

                self.nodes[leftmost].rel = self.nodes[leftmost].rel.as_lq().to_iq(rq.left);
                *self.nodes[rq.left].rel.mut_right() = leftmost;
            }
            Rel::IQ(iq) => {
                self.nodes[leftmost].rel = self.nodes[leftmost].rel.as_lq().to_iq(iq.left);
                *self.nodes[iq.left].rel.mut_right() = leftmost;
                self.nodes[rightmost].rel = self.nodes[rightmost].rel.as_rq().to_iq(iq.right);
                *self.nodes[iq.right].rel.mut_left() = rightmost;
            }
            other => panic!("Not a Q-child: {:?} !", other),
        }
        self.recycle_node(child);
    }
}
