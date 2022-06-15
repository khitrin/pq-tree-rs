# pq-tree

A PQ-tree is a data structure that represents all possible permutations of some elements
limited by a set of constraints. Each constraint enforces consecutive ordering of a subset of
elements in the leaf set of the tree.

PQ-tree based algorithms can be used for solving various problems, including consecutive ones property testing
for matrices, graph planarity testing, interval graph recognition and so on.

A PQ-tree tree consists of three types of nodes: P-nodes, allowing arbitrary permutations of children, Q-nodes, allowing
only reversions and L-nodes that represent tree leaves.

## Demo

```rust
use pq_tree::PQTree;

// is this matrix C1P ?

let matrix = vec![
    vec![1, 1, 0, 1, 1],
    vec![0, 0, 0, 1, 0],
    vec![1, 1, 1, 1, 0],
    vec![1, 1, 1, 1, 1],
    vec![1, 0, 1, 1, 0],
];

let mut tree = PQTree::from_leaves(&[1, 2, 3, 4, 5]).unwrap();
tree = tree.reduction(&[1, 3, 4, 5]).unwrap();
tree = tree.reduction(&[1, 3, 4]).unwrap();
tree = tree.reduction(&[3, 4, 5]).unwrap();
tree = tree.reduction(&[1, 2, 3, 4, 5]).unwrap();
tree = tree.reduction(&[1, 4]).unwrap();

tree.frontier().into_iter().for_each(|r| println!("{:?}", matrix[r - 1]));

// [1, 1, 0, 1, 1]
// [1, 1, 1, 1, 1]
// [1, 1, 1, 1, 0]
// [1, 0, 1, 1, 0]
// [0, 0, 0, 1, 0]

// Yes, it is!
```