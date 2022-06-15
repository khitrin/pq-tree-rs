//! A PQ-tree[^1] is a data structure that represents all possible permutations of some elements
//! limited by a set of constraints. Each constraint enforces consecutive ordering of a subset of
//! elements in the leaf set of the tree.
//!
//! PQ-tree based algorithms can be used for solving various problems, including consecutive ones property testing
//! for matrices, graph planarity testing, interval graph recognition and so on.
//!
//! A PQ-tree consists of three types of nodes: P-nodes, allowing arbitrary permutations of children, Q-nodes, allowing
//! only reversions and L-nodes that represent tree leaves.
//!
//! # Operations
//!
//! ## Reduction
//! Applying a constraint is called "tree *reduction*".
//! It takes a subset of tree leaves as an argument and updates the tree to enforce consecutive ordering of these leaves.
//!
//! Successful reduction returns modified tree with a
//! new constraint embedded into the tree structure and marks the root of the subtree with minimal height that contains all
//! specified leaves as the *pertinent root*. Chosen leaves and nodes containing only these leaves are labelled *full*.
//!
//! If a constraint is inapplicable, then reduction will fail.
//! Failed reduction will destroy the tree.
//!
//! ## Replacement
//!
//! Full children of pertinent root, specific leaf or entire tree can be replaced with by a new set of leaves
//! or removed from the tree.
//!
//! Replacement by empty set will remove subtree entirely and sets pertinent root to None.
//!
//! Pertinent subtree replacement is possible only if pertinent root was found by tree reduction. If pertinent subtree is
//! replaced by a non-empty set, then the pertinent root will be set to the root of inserted subtree.
//!
//! ## Frontier
//!
//! Reading leaves of a tree from left-to-right yields its *frontier*.
//!
//! Tree frontier is one of the allowed leaves' permutations. Although any of such permutations is sufficient for most tasks,
//! if leaves implement [`Ord`], then tree can be sorted and allow to choose unambiguous frontier.
//!
//! Two sorting functions are present: [`PQTree::sort_minimal`] and [`PQTree::sort_lexicographically`].
//!
//! Both of them performing node sorting from bottom to top, but the first using minimal children leaf as key for parent,
//! and the second uses leftmost leaf (where there is no difference for P-nodes, for Q-nodes it is important).
//!
//! Let's see it on simple example
//! ```none
//! unsorted tree:           ([[7 (1 4) 6] 3 2] 0 5)
//! sort_lexicographically:  (0 [2 3 [6 (1 4) 7]] 5)
//! sort_minimal:            (0 [[6 (1 4) 7] 3 2] 5)
//! ```
//! (P-nodes denoted by `()` and Q-nodes denoted by `[]`).
//!
//! Look at Q-node `[6 (1 4) 7]`: for [`PQTree::sort_minimal`] leaf `1` was picked as a node sorting key but
//! for [`PQTree::sort_lexicographically`] leaf `6` was picked as being leftmost.
//!
//! Informally speaking, minimal sort ensures that minimal leaf is placed to the leftmost possible position in a frontier and
//! lexicographical sort ensures that the leftmost leaf in a frontier is the minimal possible leaf.
//!
//! # Examples
//!
//! ## Consecutive ones example
//! Let `matrix` be
//! ```
//! let matrix = vec![
//!         vec![1, 1, 0, 1, 1],
//!         vec![0, 0, 0, 1, 0],
//!         vec![1, 1, 1, 1, 0],
//!         vec![1, 1, 1, 1, 1],
//!         vec![1, 0, 1, 1, 0],
//!     ];
//!```
//!
//! If it is possible to rearrange matrix rows in a way that every column has a single run of ones, we can say
//! that the matrix has a "consecutive ones" property.
//!
//! We can build a PQ-tree for matrix rows and apply a constraint for each column
//!```
//! use pq_tree::PQTree;
//!
//! let mut tree = PQTree::from_leaves(&[1, 2, 3, 4, 5]).unwrap();
//! tree = tree.reduction(&[1, 3, 4, 5]).unwrap();
//! tree = tree.reduction(&[1, 3, 4]).unwrap();
//! tree = tree.reduction(&[3, 4, 5]).unwrap();
//! tree = tree.reduction(&[1, 2, 3, 4, 5]).unwrap();
//! tree = tree.reduction(&[1, 4]).unwrap();
//! ```
//! Then take tree frontier and reorder matrix rows according to it
//! ```
//! # use pq_tree::PQTree;
//! #
//! # let mut tree = PQTree::from_leaves(&[1, 2, 3, 4, 5]).unwrap();
//! # tree = tree.reduction(&[1, 3, 4, 5]).unwrap();
//! # tree = tree.reduction(&[1, 3, 4]).unwrap();
//! # tree = tree.reduction(&[3, 4, 5]).unwrap();
//! # tree = tree.reduction(&[1, 2, 3, 4, 5]).unwrap();
//! # tree = tree.reduction(&[1, 4]).unwrap();
//! # let matrix = vec![
//! #        vec![1, 1, 0, 1, 1],
//! #        vec![0, 0, 0, 1, 0],
//! #        vec![1, 1, 1, 1, 0],
//! #        vec![1, 1, 1, 1, 1],
//! #        vec![1, 0, 1, 1, 0],
//! #    ];
//! #
//! tree.frontier().into_iter().for_each(|r| println!("{:?}", matrix[r - 1]));
//! ```
//! And obtain reordered matrix
//! ```none
//! [1, 1, 0, 1, 1]
//! [1, 1, 1, 1, 1]
//! [1, 1, 1, 1, 0]
//! [1, 0, 1, 1, 0]
//! [0, 0, 0, 1, 0]
//! ```
//!
//! Tree is successfully reduced and we can conclude that `matrix` has a consecutive ones property.
//!
//! ## Irreducible tree example
//!```
//! use pq_tree::{PQTree, ReductionError};
//!
//! let mut tree = PQTree::from_leaves(&[1, 2, 3, 4]).unwrap();
//! tree = tree.reduction(&[1, 2]).unwrap();
//! tree = tree.reduction(&[2, 3]).unwrap();
//! assert_eq!(tree.reduction(&[2, 4]).unwrap_err(), ReductionError::IrreducibleTree);
//! ```
//!
//! ## Graph planarity testing
//!
//! Planarity testing requires some preliminary steps (decomposition to biconnected components and st-numbering every component)
//! and then the PQ-tree can be used to check planarity of each component.
//!
//! Consider graph
//! ```none
//! 1
//! |\
//! | \
//! |  \
//! |   \
//! |    \
//! |     2
//! |    / \
//! |   /   \
//! |  /     3
//! | /     /
//! |/     /
//! 4     /
//!  \   /
//!   \ /
//!    5
//! ```
//!
//! It can be presented as a sequence of "bush forms": one for each vertex from top to bottom.
//! ```none
//! 1              1              1              1              1
//! |\             |\             |\             |\             |\
//! | \            | \            | \            | \            | \
//! |  \           |  \           |  \           |  \           |  \
//! |   \          |   \          |   \          |   \          |   \
//! 4    2         |    \         |    \         |    \         |    \
//!                |     2        |     2        |     2        |     2
//!                |     |\       |     |\       |    / \       |    / \
//!                4     3 4      |     | \      |   /   \      |   /   \
//!                               |     3  \     |  /     3     |  /     3
//!                               |     |   \    | /      |     | /     /
//!                               4     5    4   |/       |     |/     /
//!                                              4        |     4     /
//!                                              |        |      \   /
//!                                              5        5       \ /
//!                                                                5
//! ```
//!
//! Dangling labels denote incoming edges to unprocessed vertices.
//! All incoming edges to the same vertex must be consequent and we will enforce it by reductions.
//!
//! We can process our graph vertex-by-vertex by reducing the tree by incoming edge set and replacing it by
//! outgoing edges on each step.
//!
//! If this process succeeds for all vertices then, the graph is planar.
//!```
//! use pq_tree::PQTree;
//!
//! #[derive(Hash, PartialEq, Eq, Debug, Copy, Clone)]
//! struct Edge(i32, i32);
//!
//! let mut tree = PQTree::from_leaves(&[Edge(1, 2), Edge(1, 4)]).unwrap();
//!
//! tree = tree.reduction(&[Edge(1, 2)]).unwrap();
//! tree = tree.replace_pertinent_by_new_leaves(&[Edge(2, 3), Edge(2, 4)]).unwrap();
//!
//! tree = tree.reduction(&[Edge(2, 3)]).unwrap();
//! tree = tree.replace_pertinent_by_new_leaves(&[Edge(3, 5)]).unwrap();
//!
//! tree = tree.reduction(&[Edge(1, 4), Edge(2, 4)]).unwrap();
//! tree = tree.replace_pertinent_by_new_leaves(&[Edge(4, 5)]).unwrap();
//!
//! tree = tree.reduction(&[Edge(3, 5), Edge(4, 5)]).unwrap();
//! ```
//! Note:
//!
//! Single leaf reduction and replacement can be done in one operation like
//!
//!```
//! # use pq_tree::PQTree;
//! #
//! # #[derive(Hash, PartialEq, Eq, Debug, Copy, Clone)]
//! # struct Edge(i32, i32);
//! #
//! # let mut tree = PQTree::from_leaves(&[Edge(1, 2), Edge(1, 4)]).unwrap();
//! #
//! tree = tree.replace_leaf_by_new_leaves(&Edge(1, 2), &[Edge(2, 3), Edge(2, 4)]).unwrap();
//! # tree = tree.replace_leaf_by_new_leaves(&Edge(2, 3), &[Edge(3, 5)]).unwrap();
//! #
//! # tree = tree.reduction(&[Edge(1, 4), Edge(2, 4)]).unwrap();
//! # tree = tree.replace_pertinent_by_new_leaves(&[Edge(4, 5)]).unwrap();
//! #
//! # tree = tree.reduction(&[Edge(3, 5), Edge(4, 5)]).unwrap();
//! ```
//! because no new information can be obtained from single leaf ordering and a pertinent root is the leaf itself.
//! But it will lack pertinent root tracking.
//!
//! For further information see Booth and Lueker paper referred below.
//!
//! # Error handling
//!
//! Functions that can fail on some input are consume `self` and return [`Result<Self, _>`].
//!
//! If necessary, a tree can be cloned before calling such functions.
//!
//! Panics are considered bugs (with obvious exceptions like unrelated OOM)
//! and should be reported along with minimal reproducible example if possible.
//!
//! # Rerefences
//! [^1] Booth, K.S., & Lueker, G.S. (1976).
//! Testing for the Consecutive Ones Property, Interval Graphs, and Graph Planarity Using PQ-Tree Algorithms.
//! J. Comput. Syst. Sci., 13, 335-379. <https://doi.org/10.1016/s0022-0000(76)80045-1>

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;

pub use self::errors::*;
pub use self::tree::*;

mod errors;
mod node;
mod reduction;
mod rel;
mod sublist;
mod tree;

#[cfg(test)]
mod tests {
    use std::fmt::{Debug, Display, Formatter};
    use std::hash::Hash;

    use crate::PQTree;

    #[derive(Hash, PartialEq, Eq, Copy, Clone)]
    struct Edge(i32, i32);

    impl Display for Edge {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}-{}", self.0, self.1)
        }
    }

    impl Debug for Edge {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            Display::fmt(self, f)
        }
    }

    fn reduce<T: Eq + Hash + Clone + Debug + Display>(mut tree: PQTree<T>, s: &[T]) -> PQTree<T> {
        tree = tree.reduction(s).unwrap();
        println!("reduction   {:<22} {tree}", format!("{:?}:", s));
        tree
    }

    fn replace<T: Eq + Hash + Clone + Debug + Display>(mut tree: PQTree<T>, s: &[T]) -> PQTree<T> {
        tree = tree.replace_pertinent_by_new_leaves(s).unwrap();
        println!("replacement {:<22} {tree}", format!("{:?}:", s));
        tree
    }

    #[test]
    fn simple_planarity_test() {
        let mut tree = PQTree::from_leaves(&[Edge(1, 2), Edge(1, 3), Edge(1, 5)]).unwrap();
        println!("initial:                           {tree}");

        tree = reduce(tree, &[Edge(1, 2)]);
        tree = replace(tree, &[Edge(2, 3), Edge(2, 4), Edge(2, 5)]);

        tree = reduce(tree, &[Edge(1, 3), Edge(2, 3)]);
        tree = replace(tree, &[Edge(3, 4), Edge(3, 5)]);

        tree = reduce(tree, &[Edge(2, 4), Edge(3, 4)]);
        tree = replace(tree, &[Edge(4, 5)]);

        tree = reduce(tree, &[Edge(1, 5), Edge(2, 5), Edge(3, 5), Edge(4, 5)]);
        tree = replace(tree, &[]);

        drop(tree);
    }

    #[test]
    fn consecutive_ones_test() {
        let matrix = vec![
            vec![1, 1, 0, 1, 1],
            vec![0, 0, 0, 1, 0],
            vec![1, 1, 1, 1, 0],
            vec![1, 1, 1, 1, 1],
            vec![1, 0, 1, 1, 0],
        ];

        let mut tree = PQTree::from_leaves(&[1, 2, 3, 4, 5]).unwrap();
        tree.frontier().into_iter().for_each(|r| println!("{:?}", matrix[r - 1]));
        println!("initial:                           {tree}");
        tree = reduce(tree, &[1, 3, 4, 5]);
        tree = reduce(tree, &[1, 3, 4]);
        tree = reduce(tree, &[3, 4, 5]);
        tree = reduce(tree, &[1, 2, 3, 4, 5]);
        tree = reduce(tree, &[1, 4]);
        println!("frontier:                           {:?}", tree.frontier());

        tree.frontier().into_iter().for_each(|r| println!("{:?}", matrix[r - 1]));
    }
}
