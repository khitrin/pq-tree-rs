pub use self::pq_tree::*;

mod errors;
mod node;
mod pq_tree;
mod reduction;
mod rel;
mod sublist;

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

        tree.frontier().into_iter().for_each(|r| println!("{:?}", matrix[r - 1]));
    }
}
