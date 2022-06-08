#[derive(Debug, Clone)]
pub enum ReductionError<T> {
    EmptyLeafSet,
    IrreducibleTree,
    LeafNotFound(T),
}

#[derive(Debug, Clone)]
pub enum ReplacementError<T> {
    NoPertinentRoot,
    DuplicateLeaf(T),
}
