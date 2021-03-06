use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use bimap::BiMap;
use enum_map::Enum;

use crate::errors::*;
use crate::node::*;
use crate::rel::*;

#[derive(Debug, Clone)]
pub struct PQTree<T>
where
    T: Clone + Eq + Hash,
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

impl<T: Clone + Eq + Hash> PQTree<T> {
    /// Creates an empty `PQTree`.
    pub fn new() -> PQTree<T> {
        let root = TreeNode { rel: Rel::Root(ABSENT.into()), node: Node::L, red: ReductionInfo::default() };
        let pseudonode = TreeNode { rel: Rel::Root(ABSENT.into()), node: Node::L, red: ReductionInfo::default() };

        PQTree {
            empty: true,
            nodes: vec![root, pseudonode],
            freelist: Default::default(),
            leaves: BiMap::new(),
            pertinent_root: None,
        }
    }

    /// Creates PQTree from list of leaves.
    ///
    /// First creates an empty tree, then replaces whole tree by new leaves:
    ///
    /// ```PQTree::new().replace_tree_by_new_leaves(initial)```
    ///
    /// # Errors
    /// Returns `Err(ReplacementError::DuplicateLeaf(leaf))` if `leaf` presents in `initial` more than one time.
    pub fn from_leaves(initial: &[T]) -> Result<Self, ReplacementError<T>> {
        PQTree::new().replace_tree_by_new_leaves(initial)
    }

    /// Applies reduction to the tree enforcing leaves from `s` to be consequent
    /// and marks pertinent subroot.
    /// # Errors
    /// Returns `Err(ReductionError::EmptyLeafSet)` if `s` is empty.
    ///
    /// Returns `Err(ReductionError::LeafNotFound(leaf))` if `leaf` from `s` not found in the tree.
    ///
    /// Returns `Err(ReductionError::IrreducibleTree)` if tree cannot be reduced over new constraint.
    pub fn reduction(mut self, s: &[T]) -> Result<Self, ReductionError<T>> {
        if s.is_empty() {
            return Err(ReductionError::EmptyLeafSet);
        }

        let mut s_nodes = Vec::with_capacity(s.len());
        for leaf in s {
            match self.leaves.get_by_left(leaf) {
                Some(&node) => s_nodes.push(node),
                None => return Err(ReductionError::LeafNotFound(leaf.clone())),
            };
        }

        self.bubble(&s_nodes)?;
        self.reduce(&s_nodes)?;
        Ok(self)
    }

    /// Replaces whole tree by new leaves.
    ///
    /// Same as [`PQTree::from_leaves`] but without reallocation.
    /// # Errors
    /// Returns `Err(ReplacementError::DuplicateLeaf(leaf))` if `leaf` presents in `leaves` more than one time.
    pub fn replace_tree_by_new_leaves(mut self, leaves: &[T]) -> Result<Self, ReplacementError<T>> {
        self.destroy_tree(false);
        self.pertinent_root = None;

        self.replace_by_new_leaves(ROOT, leaves)?;

        Ok(self)
    }

    /// Replaces single `leaf` by new `leaves`.
    /// Can be called with empty `leaves` to remove `leaf` from tree.
    ///
    /// First removes `leaf` from tree, then adds new leaves.
    ///
    /// Clears pertinent root mark if any.
    ///
    /// # Errors
    /// Returns `Err(ReplacementError::LeafNotFound(leaf))` if `leaf` not found in the tree.
    ///
    /// Returns `Err(ReplacementError::DuplicateLeaf(leaf))` if `leaf` already exists in the tree or presents in `leaves` more than one time.

    pub fn replace_leaf_by_new_leaves(mut self, leaf: &T, leaves: &[T]) -> Result<Self, ReplacementError<T>> {
        match self.leaves.get_by_left(leaf) {
            None => Err(ReplacementError::LeafNotFound(leaf.clone())),
            Some(&node) => self.replace_by_new_leaves(node, leaves),
        }?;
        self.pertinent_root = None; // TODO: think about it
        Ok(self)
    }

    /// Replaces full children of the pertinent root by new `leaves`.
    /// Can be called with empty `leaves` to remove all full children from the tree.
    ///
    /// First removes all full nodes and leaves from the tree, then adds new leaves.
    ///
    /// Marks added subtree root as the pertinent root if `leaves` is not empty or clears the mark.
    ///
    /// # Errors
    /// Returns `Err(ReplacementError::DuplicateLeaf(leaf))` if `leaf` already exists in the tree or presents in `leaves` more than one time.
    ///
    /// Returns `Err(ReplacementError::NoPertinentRoot))` if no pertinent root is marked in the tree.

    pub fn replace_pertinent_by_new_leaves(mut self, leaves: &[T]) -> Result<Self, ReplacementError<T>> {
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
                                // remove_node can demote Q-node to P-node and even remove P and hoist sole child
                                // but: Q node have at least three children and first is retained here
                                //      and Q is partial (or pseudonode witch also part of partial Q node,
                                //      so at least one empty child will remain and first cannot be moved inside tree
                                self.remove_node(current);

                                // still keep debug_assert! here
                                debug_assert!(!&self.freelist.contains(&first_unwrapped));
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

    /// Returns the tree frontier: a vector of leaves ordered in an allowed way for the tree.
    pub fn frontier(&self) -> Vec<T> {
        if self.empty {
            return vec![];
        }
        self.collect_frontier(Vec::with_capacity(self.leaves.len()), ROOT)
    }

    pub(crate) fn recycle_node(&mut self, idx: usize) {
        // TODO: remove last node and truncate freelist if possible?
        debug_assert!(!self.freelist.contains(&idx));
        self.nodes[idx].rel = Rel::Root(ABSENT.into());
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

    fn destroy_tree(&mut self, recycle: bool) {
        if !self.empty {
            self.nodes.truncate(2); // pseunonode and root must be kept
            self.freelist.clear();
            self.leaves.clear();
        }
        self.empty = recycle;
        // self.pertinent_root must be set or unset by caller
    }

    fn destroy_node(&mut self, idx: usize, recycle: bool) {
        if idx == ROOT {
            self.destroy_tree(recycle);
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

    fn remove_node(&mut self, idx: usize) {
        match self.nodes[idx].rel {
            Rel::Root(_) => {
                self.destroy_tree(true);
                return;
            }
            Rel::P(p) => {
                if self.nodes[p.next].rel.as_p().next == idx {
                    // last child remains in parent, replace node by child
                    self.replace_node(p.parent, p.next);
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
            }
            Rel::RQ(rq) => {
                let left_left = self.nodes[rq.left].rel.left();

                if let Rel::LQ(_) = self.nodes[left_left].rel {
                    self.replace_with_pair_p(rq.parent, rq.left, left_left);
                } else {
                    self.nodes[rq.parent].node.as_mut_q().right = rq.left;
                    self.nodes[rq.left].rel = Rel::RQ(RightChildOfQ { parent: rq.parent, left: left_left });
                }
            }
            Rel::IQ(iq) => {
                if let (Rel::LQ(lq), Rel::RQ(_)) = (self.nodes[iq.left].rel, self.nodes[iq.right].rel) {
                    self.replace_with_pair_p(lq.parent, iq.left, iq.right);
                } else {
                    *self.nodes[iq.left].rel.mut_right() = iq.right;
                    *self.nodes[iq.right].rel.mut_left() = iq.left;
                }
            }
        };

        self.destroy_node(idx, true);
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
            self.leaves
                .insert_no_overwrite(leaves[0].clone(), idx)
                .map_err(|e| ReplacementError::DuplicateLeaf(e.0))?;
            Ok(Some(idx))
        } else {
            self.destroy_node(idx, false);

            self.leaves.reserve(leaves.len());
            if self.freelist.len() < leaves.len() {
                self.nodes.reserve(leaves.len() - self.freelist.len());
            }

            let first_last = leaves.iter().rev().try_fold((None, None), |first_last, leaf| {
                let leaf_node = self.add_node(TreeNode {
                    rel: Rel::P(ChildOfP { parent: idx, next: first_last.1.unwrap_or(0) }),
                    node: Node::L,
                    red: Default::default(),
                });
                // TODO: T: Debug
                self.leaves
                    .insert_no_overwrite(leaf.clone(), leaf_node)
                    .map_err(|e| ReplacementError::DuplicateLeaf(e.0))?;

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
            Node::L => v.push(self.leaves.get_by_right(&root).expect("broken leaves map").clone()),
        };
        v
    }
}

// TODO: optimize, reduce allocations, refs and so on
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SortPair<T: Ord + Clone>(T, usize);

impl<T: Clone + Eq + Hash + Ord> PQTree<T> {
    /// Sorts the tree by "minimal order"
    pub fn sort_minimal(&mut self) {
        if !self.empty {
            self.sort(ROOT, false);
        }
    }

    /// Sorts the tree "lexicographically"
    pub fn sort_lexicographically(&mut self) {
        if !self.empty {
            self.sort(ROOT, true);
        }
    }

    fn sort(&mut self, idx: usize, lexicographically: bool) -> T {
        match self.nodes[idx].node {
            Node::P(PNode { child }) => self.sort_p(idx, child, lexicographically),
            Node::Q(QNode { left, right }) => self.sort_q(idx, left, right, lexicographically),
            Node::L => self.leaves.get_by_right(&idx).unwrap().clone(),
        }
    }

    fn sort_p(&mut self, idx: usize, first_child: usize, lexicographically: bool) -> T {
        let mut scratch = vec![];

        let mut next = Some(first_child);
        while let Some(current) = next {
            next = {
                let next = self.nodes[current].rel.next();
                if next != first_child {
                    Some(next)
                } else {
                    None
                }
            };
            scratch.push(SortPair(self.sort(current, lexicographically), current));
        }

        scratch.sort_unstable();
        let first = scratch[0].clone();

        let last = scratch
            .into_iter()
            .map(|p| p.1)
            .reduce(|a, b| {
                self.nodes[a].rel.as_mut_p().next = b;
                b
            })
            .unwrap();

        self.nodes[last].rel.as_mut_p().next = first.1;
        self.nodes[idx].node.as_mut_p().child = first.1;

        first.0
    }

    fn sort_q(&mut self, idx: usize, left_child: usize, right_child: usize, lexicographically: bool) -> T {
        // for even number of children we have to deal with case with middle min

        let mut left = left_child;
        let mut right = right_child;
        let left_min = self.sort(left, lexicographically);
        let right_min = self.sort(right, lexicographically);
        let (mut min, need_reverse) = if right_min.gt(&left_min) { (left_min, false) } else { (right_min, true) };

        loop {
            // left and right already processed
            left = self.nodes[left].rel.right();
            if left == right {
                // even case
                break;
            }

            right = self.nodes[right].rel.left();
            if left == right {
                // odd case
                let middle_min = self.sort(left, lexicographically);
                if !lexicographically {
                    min = min.min(middle_min);
                }
                break;
            }

            let left_min = self.sort(left, lexicographically);
            let right_min = self.sort(right, lexicographically);
            if !lexicographically {
                min = min.min(left_min).min(right_min);
            }
        }

        if need_reverse {
            self.reverse_q(idx);
        }

        min
    }
}

impl<T: Clone + Eq + Hash + Display> Display for PQTree<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fn node_fmt<T>(
            tree: &PQTree<T>,
            idx: usize,
            f: &mut Formatter<'_>,
            mut mark_full: bool,
            non_first: bool,
        ) -> std::fmt::Result
        where
            T: Clone + Eq + Hash + Display,
        {
            if non_first {
                write!(f, " ")?;
            }

            let marked_full = if mark_full && tree.nodes[idx].red.label == NodeLabel::Full {
                mark_full = false;
                write!(f, "<")?;
                true
            } else {
                false
            };

            let TreeNode { node, .. } = &tree.nodes[idx];
            match node {
                Node::P(p) => {
                    write!(f, "(")?;

                    let mut p_idx = p.child;
                    let mut not_first = false;
                    loop {
                        node_fmt(tree, p_idx, f, mark_full, not_first)?;
                        p_idx = tree.nodes[p_idx].rel.as_p().next;
                        if p_idx == p.child {
                            break;
                        }
                        // not_first = !marked;
                        not_first = true;
                    }

                    write!(f, ")")?;
                }
                Node::Q(q) => {
                    write!(f, "[")?;

                    let mut q_idx = q.left;
                    let mut not_first = false;

                    loop {
                        node_fmt(tree, q_idx, f, mark_full, not_first)?;
                        let TreeNode { rel, .. } = &tree.nodes[q_idx];
                        match rel {
                            Rel::LQ(LeftChildOfQ { right, .. }) | Rel::IQ(InteriorChildOfQ { right, .. }) => {
                                not_first = true;
                                q_idx = *right
                            }
                            _ => break,
                        }
                    }

                    write!(f, "]")?;
                }
                Node::L => {
                    write!(f, "{}", tree.leaves.get_by_right(&idx).expect("broken leaves map"))?;
                }
            };

            if marked_full {
                write!(f, ">")?;
            }

            Ok(())
        }

        if self.empty {
            write!(f, "()")
        } else {
            node_fmt(self, ROOT, f, self.pertinent_root.is_some(), false).map(|_| ())
        }
    }
}
