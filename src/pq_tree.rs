use bimap::BiMap;
use std::collections::{HashSet, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::iter;

use enum_map::{enum_map, Enum, EnumMap};

#[derive(Debug, Clone)]
pub struct PQTree<T>
where
    T: Copy + Eq + Hash,
{
    root: usize,
    nodes: Vec<TreeNode>,
    freelist: VecDeque<usize>,
    leafs: BiMap<T, usize>,
    pertinent_root: Option<usize>,
}

#[derive(Debug, Copy, Clone)]
struct ChildOfP {
    parent: usize,
    next: usize,
}

#[derive(Debug, Copy, Clone)]
struct LeftChildOfQ {
    parent: usize,
    right: usize,
}

#[derive(Debug, Copy, Clone)]
struct RightChildOfQ {
    parent: usize,
    left: usize,
}

#[derive(Debug, Copy, Clone)]
struct InteriorChildOfQ {
    parent_of_unblocked: usize,
    left: usize,
    right: usize,
}

#[derive(Debug, Copy, Clone)]
enum Rel {
    Root,
    P(ChildOfP),
    LQ(LeftChildOfQ),
    RQ(RightChildOfQ),
    IQ(InteriorChildOfQ),
}

impl RightChildOfQ {
    #[must_use]
    fn to_iq(&self, right: usize) -> Rel {
        Rel::IQ(InteriorChildOfQ { parent_of_unblocked: self.parent, left: self.left, right })
    }
}

impl LeftChildOfQ {
    #[must_use]
    fn to_iq(&self, left: usize) -> Rel {
        Rel::IQ(InteriorChildOfQ { parent_of_unblocked: self.parent, left, right: self.right })
    }
}

#[allow(dead_code)]
impl Rel {
    fn as_p(&self) -> &ChildOfP {
        if let Rel::P(p) = self {
            p
        } else {
            panic!("Not P: {:?}", self);
        }
    }

    fn as_mut_p(&mut self) -> &mut ChildOfP {
        if let Rel::P(p) = self {
            p
        } else {
            panic!("Not P: {:?}", self);
        }
    }

    fn as_lq(&self) -> &LeftChildOfQ {
        if let Rel::LQ(lq) = self {
            lq
        } else {
            panic!("Not LQ: {:?}", self);
        }
    }

    fn as_mut_lq(&mut self) -> &mut LeftChildOfQ {
        if let Rel::LQ(lq) = self {
            lq
        } else {
            panic!("Not LQ: {:?}", self);
        }
    }

    fn as_rq(&self) -> &RightChildOfQ {
        if let Rel::RQ(rq) = self {
            rq
        } else {
            panic!("Not RQ: {:?}", self);
        }
    }

    fn as_mut_rq(&mut self) -> &mut RightChildOfQ {
        if let Rel::RQ(rq) = self {
            rq
        } else {
            panic!("Not RQ: {:?}", self);
        }
    }

    fn as_iq(&self) -> &InteriorChildOfQ {
        if let Rel::IQ(iq) = self {
            iq
        } else {
            panic!("Not IQ: {:?}", self);
        }
    }

    fn as_mut_iq(&mut self) -> &mut InteriorChildOfQ {
        if let Rel::IQ(iq) = self {
            iq
        } else {
            panic!("Not IQ: {:?}", self);
        }
    }

    fn mut_left(&mut self) -> &mut usize {
        match self {
            Rel::RQ(RightChildOfQ { left, .. }) => left,
            Rel::IQ(InteriorChildOfQ { left, .. }) => left,
            _ => panic!("Not RQ or IQ: {:?}", self),
        }
    }

    fn mut_right(&mut self) -> &mut usize {
        match self {
            Rel::LQ(LeftChildOfQ { right, .. }) => right,
            Rel::IQ(InteriorChildOfQ { right, .. }) => right,
            _ => panic!("Not LQ or IQ: {:?}", self),
        }
    }

    fn left(&self) -> usize {
        *match self {
            Rel::RQ(RightChildOfQ { left, .. }) => left,
            Rel::IQ(InteriorChildOfQ { left, .. }) => left,
            _ => panic!("Not RQ or IQ: {:?}", self),
        }
    }

    fn right(&self) -> usize {
        *match self {
            Rel::LQ(LeftChildOfQ { right, .. }) => right,
            Rel::IQ(InteriorChildOfQ { right, .. }) => right,
            _ => panic!("Not LQ or IQ: {:?}", self),
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct PNode {
    child: usize,
}

#[derive(Debug, Copy, Clone)]
struct QNode {
    left: usize,
    right: usize,
}

#[derive(Copy, Clone, Debug)]
enum Node {
    P(PNode),
    Q(QNode),
    L,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum NodeMark {
    Unmarked,
    Blocked,
    Unblocked,
    Queued,
}

#[derive(Debug, Enum, Eq, PartialEq, Copy, Clone)]
enum NodeLabel {
    Empty,
    Full,
    SinglyPartial,
    DoublyPartial,
}

#[derive(Debug, Clone)]
struct ReductionInfo {
    mark: NodeMark,
    label: NodeLabel,
    pertinent_child_count: usize,
    pertinent_leaf_count: usize,
}

impl Default for ReductionInfo {
    fn default() -> Self {
        ReductionInfo {
            mark: NodeMark::Unmarked,
            label: NodeLabel::Empty,
            pertinent_child_count: 0,
            pertinent_leaf_count: 0,
        }
    }
}

#[derive(Debug, Clone)]
struct TreeNode {
    rel: Rel,
    node: Node,
    red: ReductionInfo,
}

impl TreeNode {
    fn parent_of_unblocked(&self) -> usize {
        match self.rel {
            Rel::Root => usize::MAX,
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

#[allow(dead_code)]
impl Node {
    fn as_p(&self) -> &PNode {
        if let Node::P(p) = self {
            p
        } else {
            panic!("Not a P-node: {:?}!", self);
        }
    }

    fn as_mut_p(&mut self) -> &mut PNode {
        if let Node::P(p) = self {
            p
        } else {
            panic!("Not a P-node: {:?}!", self);
        }
    }

    fn as_q(&self) -> &QNode {
        if let Node::Q(q) = self {
            q
        } else {
            panic!("Not a Q-node: {:?}!", self);
        }
    }

    fn as_mut_q(&mut self) -> &mut QNode {
        if let Node::Q(q) = self {
            q
        } else {
            panic!("Not a Q-node: {:?}!", self);
        }
    }
}

impl<T: Copy + Eq + Hash> PQTree<T> {
    pub fn new(initial: &[T]) -> PQTree<T> {
        let initial_count = initial.len();

        let pseudonode =
            TreeNode { rel: Rel::Root, node: Node::Q(QNode { left: 0, right: 0 }), red: ReductionInfo::default() };

        let root = TreeNode { rel: Rel::Root, node: Node::P(PNode { child: 2 }), red: ReductionInfo::default() };
        let leafs = (0..initial_count).map(|i| TreeNode {
            rel: Rel::P(ChildOfP { parent: 1, next: ((i + 1) % initial_count) + 2 }),
            node: Node::L,
            red: ReductionInfo::default(),
        });

        PQTree {
            root: 1,
            nodes: iter::once(pseudonode).chain(iter::once(root)).chain(leafs).collect(),
            leafs: initial.iter().enumerate().map(|(i, &l)| (l, i + 2)).collect(),
            freelist: VecDeque::new(),
            pertinent_root: None,
        }
    }

    fn recycle_node(&mut self, idx: usize) {
        // TODO: remove last node and truncate freelist if possible?
        debug_assert!(!self.freelist.contains(&idx));
        self.freelist.push_back(idx);
    }

    fn add_node(&mut self, node: TreeNode) -> usize {
        if let Some(free) = self.freelist.pop_front() {
            self.nodes[free] = node;
            free
        } else {
            self.nodes.push(node);
            self.nodes.len() - 1
        }
    }

    pub fn reduction(mut self, s: &[T]) -> Option<PQTree<T>> {
        if self.bubble(s) && self.reduce(s) {
            Some(self)
        } else {
            None
        }
    }

    fn bubble(&mut self, s: &[T]) -> bool {
        self.nodes.iter_mut().for_each(|n| n.red = Default::default());

        let mut block_count = 0usize;
        let mut blocked = HashSet::new();
        let mut off_the_top = 0usize;

        let mut queue = VecDeque::with_capacity(s.len());
        s.iter().for_each(|leaf| queue.push_back(*self.leafs.get_by_left(leaf).unwrap()));

        fn unblock_adjacent(
            nodes: &mut Vec<TreeNode>,
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
            let x;
            if let Some(x_) = queue.pop_front() {
                x = x_;
            } else {
                return self.fail();
            }

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

                if y == usize::MAX {
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
            return self.fail();
        }

        if let Some(&x) = blocked.iter().next() {
            // create pseudonode from block

            let left = unblock_adjacent(&mut self.nodes, 0, Some(x), true, &mut blocked).unwrap();
            let right = unblock_adjacent(&mut self.nodes, 0, Some(x), false, &mut blocked).unwrap();
            self.nodes[0].node = Node::Q(QNode { left, right }); // 0 is pseudonode
            self.nodes[0].red.pertinent_child_count -= 1; // unblock_adjacent have touched central node two times
        }

        true
    }

    fn reduce(&mut self, s: &[T]) -> bool {
        // todo: optimize?
        self.nodes.iter_mut().for_each(|n| n.red.label = NodeLabel::Empty);

        let mut queue = VecDeque::with_capacity(s.len());

        s.iter().for_each(|leaf| {
            let leaf_node = *self.leafs.get_by_left(leaf).unwrap();
            self.nodes[leaf_node].red.pertinent_leaf_count = 1;
            self.label(leaf_node, NodeLabel::Full);
            queue.push_back(leaf_node);
        });

        while let Some(x) = queue.pop_front() {
            let root = self.nodes[x].red.pertinent_leaf_count >= s.len();

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
                return self.fail();
            };
        }
        true
    }
}

#[derive(Debug)]
struct SubCircularList {
    first: usize,
    last: usize,
    len: usize,
}

impl SubCircularList {
    fn new() -> SubCircularList {
        SubCircularList { first: 0, last: 0, len: 0 }
    }

    fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn len(&self) -> usize {
        self.len
    }

    fn first(&self) -> usize {
        debug_assert_ne!(self.len, 0);
        self.first
    }

    fn last(&self) -> usize {
        debug_assert_ne!(self.len, 0);
        self.last
    }

    fn add(&mut self, idx: usize) {
        if self.len == 0 {
            self.first = idx;
            self.last = idx;
            self.len = 1;
        } else {
            self.last = idx;
            self.len += 1;
        }
    }
}

impl<T: Copy + Eq + Hash> PQTree<T> {
    fn apply_p_templates(&mut self, x: usize, first_child: usize, root: bool) -> bool {
        let split = self.split_p_children(first_child);

        if split[NodeLabel::DoublyPartial].len() != 0 {
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
                return self.label(x, NodeLabel::Full);
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

            debug_assert_ne!(left, 0);

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

    fn add_sub_p_node(&mut self, children: &SubCircularList, label: NodeLabel) -> usize {
        if children.len == 1 {
            children.first() // parent must be changed by caller
        } else {
            let new_p = self.add_node(TreeNode {
                rel: Rel::Root, // parent must be changed by caller
                node: Node::P(PNode { child: children.first() }),
                red: ReductionInfo { label, ..Default::default() },
            });

            let mut current = children.first();

            loop {
                debug_assert_ne!(new_p, 0);
                self.nodes[current].rel.as_mut_p().parent = new_p;
                current = self.nodes[current].rel.as_p().next;
                if current == children.first() {
                    break;
                }
            }

            new_p
        }
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
        debug_assert_ne!(q, 0);
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
        debug_assert_ne!(target, 0);

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
            return self.mark_as_pertinent_root(x);
        } else {
            return self.confirm_l1(x);
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
}

impl<T: Copy + Eq + Hash> PQTree<T> {
    fn collect_frontier(&self, mut v: Vec<T>, root: usize) -> Vec<T> {
        match self.nodes[root].node {
            Node::P(p) => {
                let mut c = p.child;
                loop {
                    v = self.collect_frontier(v, c);
                    c = self.nodes[c].rel.as_p().next;
                    if c == p.child {
                        break;
                    }
                }
            }
            Node::Q(q) => {
                let mut c = q.left;
                loop {
                    v = self.collect_frontier(v, c);
                    // TODO: iterator for Q children?
                    c = match self.nodes[c].rel {
                        Rel::LQ(lq) => lq.right,
                        Rel::IQ(iq) => iq.right,
                        Rel::RQ(_) => break,
                        other => panic!("Not a Q-child: {:?} !", other),
                    };
                }
            }
            Node::L => v.push(*self.leafs.get_by_right(&root).unwrap()),
        };
        v
    }

    pub fn frontier(&self) -> Vec<T> {
        self.collect_frontier(Vec::with_capacity(self.leafs.len()), self.root)
    }
}

impl<T: Copy + Eq + Hash + Display> Display for PQTree<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fn node_fmt<T>(tree: &PQTree<T>, idx: usize, f: &mut Formatter<'_>) -> std::fmt::Result
        where
            T: Copy + Eq + Hash + Display,
        {
            let TreeNode { node, .. } = &tree.nodes[idx];
            match node {
                Node::P(p) => {
                    write!(f, "(")?;

                    let mut p_idx = p.child;
                    loop {
                        node_fmt(tree, p_idx, f)?;
                        p_idx = tree.nodes[p_idx].rel.as_p().next;
                        if p_idx == p.child {
                            break;
                        }
                    }

                    write!(f, ")")?;
                }
                Node::Q(q) => {
                    write!(f, "[")?;

                    let mut q_idx = q.left;
                    loop {
                        node_fmt(tree, q_idx, f)?;
                        let TreeNode { rel, .. } = &tree.nodes[q_idx];
                        match rel {
                            Rel::LQ(LeftChildOfQ { right, .. }) | Rel::IQ(InteriorChildOfQ { right, .. }) => {
                                q_idx = *right
                            }
                            _ => break,
                        }
                    }

                    write!(f, "]")?;
                }
                Node::L => {
                    write!(f, " {} ", tree.leafs.get_by_right(&idx).unwrap())?;
                }
            };

            return Ok(());
        }

        node_fmt(&self, self.root, f)
    }
}
