use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::iter;

use bimap::BiMap;
use enum_map::Enum;

use crate::errors::*;
use crate::node::*;
use crate::rel::*;

#[derive(Debug, Clone)]
pub struct PQTree<T>
where
    T: Copy + Eq + Hash,
{
    empty: bool,
    pub(crate) nodes: Vec<TreeNode>,
    freelist: VecDeque<usize>,
    pub(crate) leaves: BiMap<T, usize>,
    pub(crate) pertinent_root: Option<usize>,
}

pub(crate) const PSEUDONODE: usize = 0;
pub(crate) const ROOT: usize = 1;
pub(crate) const ABSENT: usize = usize::MAX;

#[derive(Debug, Clone)]
pub(crate) struct TreeNode {
    pub(crate) rel: Rel,
    pub(crate) node: Node,
    pub(crate) red: ReductionInfo,
}

#[derive(Debug, Clone)]
pub(crate) struct ReductionInfo {
    pub(crate) mark: NodeMark,
    pub(crate) label: NodeLabel,
    pub(crate) pertinent_child_count: usize,
    pub(crate) pertinent_leaf_count: usize,
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

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub(crate) enum NodeMark {
    Unmarked,
    Blocked,
    Unblocked,
    Queued,
}

#[derive(Debug, Enum, Eq, PartialEq, Copy, Clone)]
pub(crate) enum NodeLabel {
    Empty,
    Full,
    SinglyPartial,
    DoublyPartial,
}

impl<T: Copy + Eq + Hash> PQTree<T> {
    pub fn new(initial: &[T]) -> PQTree<T> {
        let initial_count = initial.len();
        assert_ne!(initial_count, 0);
        // TODO: single leaf !
        assert_ne!(initial_count, 1);

        let pseudonode =
            TreeNode { rel: Rel::Root, node: Node::Q(QNode { left: 0, right: 0 }), red: ReductionInfo::default() };

        let root = TreeNode { rel: Rel::Root, node: Node::P(PNode { child: 2 }), red: ReductionInfo::default() };
        let leaves = (0..initial_count).map(|i| TreeNode {
            rel: Rel::P(ChildOfP { parent: 1, next: ((i + 1) % initial_count) + 2 }),
            node: Node::L,
            red: ReductionInfo::default(),
        });

        PQTree {
            empty: false,
            nodes: iter::once(pseudonode).chain(iter::once(root)).chain(leaves).collect(),
            leaves: initial.iter().enumerate().map(|(i, &l)| (l, i + 2)).collect(),
            freelist: VecDeque::new(),
            pertinent_root: None,
        }
    }

    pub fn reduction(mut self, s: &[T]) -> Result<PQTree<T>, ReductionError<T>> {
        if s.is_empty() {
            return Err(ReductionError::EmptyLeafSet);
        }

        let mut s_nodes = Vec::with_capacity(s.len());
        for leaf in s {
            match self.leaves.get_by_left(leaf) {
                Some(&node) => s_nodes.push(node),
                None => return Err(ReductionError::LeafNotFound(*leaf)),
            };
        }

        self.bubble(&s_nodes)?;
        self.reduce(&s_nodes)?;
        Ok(self)
    }

    pub(crate) fn recycle_node(&mut self, idx: usize) {
        // TODO: remove last node and truncate freelist if possible?
        debug_assert!(!self.freelist.contains(&idx));
        self.nodes[idx].rel = Rel::Root;
        self.freelist.push_back(idx);
    }

    pub(crate) fn add_node(&mut self, node: TreeNode) -> usize {
        if let Some(free) = self.freelist.pop_front() {
            self.nodes[free] = node;
            free
        } else {
            self.nodes.push(node);
            self.nodes.len() - 1
        }
    }

    fn destroy_node(&mut self, idx: usize, recycle: bool) {
        if idx == ROOT {
            self.empty = true;
            return;
        }
        debug_assert_ne!(idx, PSEUDONODE);

        match self.nodes[idx].node {
            Node::P(p) => {
                let mut next = Some(p.child);
                while let Some(current) = next {
                    next = {
                        let next = self.nodes[current].rel.next();
                        if next != p.child {
                            Some(next)
                        } else {
                            None
                        }
                    };
                    self.destroy_node(current, true);
                }
            }
            Node::Q(q) => {
                let mut next = Some(q.left);
                while let Some(current) = next {
                    next = if current != q.right { Some(self.nodes[current].rel.right()) } else { None };
                    self.destroy_node(current, true);
                }
            }
            Node::L => {
                self.leaves.remove_by_right(&idx).expect("broken leaves map");
            }
        }

        if recycle {
            self.recycle_node(idx);
        }
    }

    fn remove_node(&mut self, idx: usize) -> Option<(usize, usize)> {
        let replacement = match self.nodes[idx].rel {
            Rel::Root => {
                self.empty = true; // cannot be undone, tree is destroyed
                None
            }
            Rel::P(p) => {
                if self.nodes[p.next].rel.as_p().next == idx {
                    // last child remains in parent, replace node by child
                    self.replace_node(p.parent, p.next);
                    Some((p.next, p.parent))
                } else {
                    None
                }
            }
            Rel::LQ(lq) => {
                let right_right = self.nodes[lq.right].rel.right();

                if let Rel::RQ(_) = self.nodes[right_right].rel {
                    self.replace_with_pair_p(lq.parent, lq.right, right_right);
                } else {
                    self.nodes[lq.parent].node.as_mut_q().left = lq.right;
                    self.nodes[lq.right].rel = Rel::LQ(LeftChildOfQ { parent: lq.parent, right: right_right });
                }
                None
            }
            Rel::RQ(rq) => {
                let left_left = self.nodes[rq.left].rel.left();

                if let Rel::LQ(_) = self.nodes[left_left].rel {
                    self.replace_with_pair_p(rq.parent, rq.left, left_left);
                } else {
                    self.nodes[rq.parent].node.as_mut_q().right = rq.left;
                    self.nodes[rq.left].rel = Rel::RQ(RightChildOfQ { parent: rq.parent, left: left_left });
                }
                None
            }
            Rel::IQ(iq) => {
                if let (Rel::LQ(lq), Rel::RQ(_)) = (self.nodes[iq.left].rel, self.nodes[iq.right].rel) {
                    self.replace_with_pair_p(lq.parent, iq.left, iq.right);
                } else {
                    *self.nodes[iq.left].rel.mut_right() = iq.right;
                    *self.nodes[iq.right].rel.mut_left() = iq.left;
                }
                None
            }
        };

        self.destroy_node(idx, true);
        replacement
    }

    fn replace_with_pair_p(&mut self, idx: usize, left: usize, right: usize) {
        self.nodes[idx].node = Node::P(PNode { child: left });
        self.nodes[left].rel = Rel::P(ChildOfP { parent: idx, next: right });
        self.nodes[right].rel = Rel::P(ChildOfP { parent: idx, next: left });
    }

    fn replace_by_new_leaves(&mut self, idx: usize, leaves: &[T]) -> Result<Option<usize>, ReplacementError<T>> {
        debug_assert!(!self.freelist.contains(&idx));
        if leaves.is_empty() {
            self.remove_node(idx);
            Ok(None)
        } else if leaves.len() == 1 {
            self.destroy_node(idx, false);
            self.nodes[idx].node = Node::L;
            self.leaves.insert_no_overwrite(leaves[0], idx).map_err(|e| ReplacementError::DuplicateLeaf(e.0))?;
            Ok(Some(idx))
        } else {
            self.destroy_node(idx, false);
            let first_last = leaves.iter().rev().try_fold((None, None), |first_last, &leaf| {
                let leaf_node = self.add_node(TreeNode {
                    rel: Rel::P(ChildOfP { parent: idx, next: first_last.1.unwrap_or(0) }),
                    node: Node::L,
                    red: Default::default(),
                });
                // TODO: T: Debug
                self.leaves.insert_no_overwrite(leaf, leaf_node).map_err(|e| ReplacementError::DuplicateLeaf(e.0))?;

                Ok((first_last.0.or(Some(leaf_node)), Some(leaf_node)))
            })?;

            let (first, last) = (
                first_last.0.expect("impossible, no first inserted node"),
                first_last.1.expect("impossible, no last inserted node"),
            );
            // wrap circular list
            self.nodes[first].rel.as_mut_p().next = last;
            self.nodes[idx].node = Node::P(PNode { child: last });
            Ok(Some(idx))
        }
    }

    pub fn replace_pertinent_by_new_leaves(mut self, leaves: &[T]) -> Result<PQTree<T>, ReplacementError<T>> {
        let pertinent_root = self.pertinent_root.ok_or(ReplacementError::NoPertinentRoot)?;
        self.pertinent_root = match self.nodes[pertinent_root].node {
            Node::P(_) | Node::L => self.replace_by_new_leaves(pertinent_root, leaves),
            Node::Q(q) => {
                if pertinent_root != PSEUDONODE && self.nodes[pertinent_root].red.label == NodeLabel::Full {
                    // full non-pseudo Q-node
                    self.replace_by_new_leaves(pertinent_root, leaves)
                } else {
                    // partial Q-node or pseudonode
                    // TODO: optimize for SinglyPartial case
                    let mut next = Some(q.left);
                    let mut first = None;
                    while let Some(current) = next {
                        next = if current == q.right { None } else { Some(self.nodes[current].rel.right()) };

                        if self.nodes[current].red.label == NodeLabel::Full {
                            if let Some(first_unwrapped) = first {
                                let replacement = self.remove_node(current);
                                if let Some((old, new)) = replacement {
                                    if old == first_unwrapped {
                                        first = Some(new);
                                    }
                                }
                            } else {
                                first = Some(current);
                            }
                        }
                    }

                    self.replace_by_new_leaves(first.expect("full child not found in pertinent root"), leaves)
                }
            }
        }?;
        Ok(self)
    }

    fn replace_node(&mut self, target: usize, source: usize) {
        self.nodes[target].node = self.nodes[source].node;
        self.nodes[target].red = self.nodes[source].red.clone();

        match self.nodes[target].node {
            Node::P(p) => {
                let mut next = Some(p.child);
                while let Some(current) = next {
                    let r = self.nodes[current].rel.as_mut_p();
                    next = if r.next != p.child { Some(r.next) } else { None };
                    r.parent = target;
                }
            }
            Node::Q(q) => {
                self.nodes[q.left].rel.as_mut_lq().parent = target;
                self.nodes[q.right].rel.as_mut_rq().parent = target;
            }
            Node::L => {
                let leaf = self.leaves.remove_by_right(&source).expect("broken leaves map").0;
                self.leaves.insert_no_overwrite(leaf, target).ok().expect("broken leaves map");
            }
        }

        self.recycle_node(source);
    }

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
            Node::L => v.push(*self.leaves.get_by_right(&root).expect("broken leaves map")),
        };
        v
    }

    pub fn frontier(&self) -> Vec<T> {
        self.collect_frontier(Vec::with_capacity(self.leaves.len()), ROOT)
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
                    write!(f, " {} ", tree.leaves.get_by_right(&idx).expect("broken leaves map"))?;
                }
            };

            Ok(())
        }

        if self.empty {
            write!(f, "()")
        } else {
            node_fmt(self, ROOT, f)
        }
    }
}
