mod errors;
mod node;
mod pq_tree;
mod reduction;
mod rel;
mod sublist;

pub use self::pq_tree::*;

#[cfg(test)]
mod tests {
    use crate::PQTree;
    use std::fmt::{Display, Formatter};

    #[derive(Hash, PartialEq, Eq, Debug, Copy, Clone)]
    struct Edge(i32, i32);

    impl Display for Edge {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}-{}", self.0, self.1)
        }
    }

    #[test]
    fn simple_planarity_test() {
        let mut tree = PQTree::new(&[Edge(1, 2), Edge(1, 3), Edge(1, 5)]);
        println!("initial         : {}", &tree);

        tree = tree.reduction(&[Edge(1, 2)]).unwrap();
        println!("reduction   *-2 : {}", &tree);

        tree = tree.replace_pertinent_by_new_leaves(&[Edge(2, 3), Edge(2, 4), Edge(2, 5)]).unwrap();
        println!("replacement 2-* : {}", &tree);

        tree = tree.reduction(&[Edge(1, 3), Edge(2, 3)]).unwrap();
        println!("reduction   *-3 : {}", &tree);

        tree = tree.replace_pertinent_by_new_leaves(&[Edge(3, 4), Edge(3, 5)]).unwrap();
        println!("replacement 3-* : {}", &tree);

        tree = tree.reduction(&[Edge(2, 4), Edge(3, 4)]).unwrap();
        println!("reduction   *-4 : {}", &tree);

        tree = tree.replace_pertinent_by_new_leaves(&[Edge(4, 5)]).unwrap();
        println!("replacement 4-* : {}", &tree);

        tree = tree.reduction(&[Edge(1, 5), Edge(2, 5), Edge(3, 5), Edge(4, 5)]).unwrap();
        println!("reduction   *-5 : {}", &tree);

        tree = tree.replace_pertinent_by_new_leaves(&[]).unwrap();
        println!("replacement 5-* : {}", &tree);
    }
}
