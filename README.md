### smt-halo2

A Sparse Merkle tree is a type of Merkle tree, but it is much easier to
prove non-membership in a sparse Merkle tree than in an arbitrary Merkle
tree. For an explanation of sparse Merkle trees, see [here](
`<https://medium.com/@kelvinfichter/whats-a-sparse-merkle-tree-acda70aeb837>).

This repo provides a circuit implementation of the Sparse Merkle Tree with
Halo2's PLONKish arithmetization and Poseidon hash primitives.

The implementation of the native smt data structure and the Path chip is
adapted from Webb and Arkworks: https://github.com/webb-tools/arkworks-gadgets
