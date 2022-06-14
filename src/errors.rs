/// Reduction failure
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum ReductionError<T> {
    /// No leaves specified for reduction.
    EmptyLeafSet,
    /// The tree cannot be reduced.
    IrreducibleTree,
    /// Leaf not found in the tree.
    LeafNotFound(T),
}

/// Replacement failure
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum ReplacementError<T> {
    /// The pertinent root isn't marked in the tree.
    NoPertinentRoot,
    /// Leaf is already present in the tree.
    DuplicateLeaf(T),
    /// Leaf not found in the tree.
    LeafNotFound(T),
}
