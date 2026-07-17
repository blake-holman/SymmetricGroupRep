# Representation-Theory Roadmap

## Goal

Provide the symmetric-group representation theory needed to formalize the
decompositions used in Rosmanis's small-range element-distinctness argument.
The package should reuse mathlib's representations, restriction, induction,
characters, and categorical simplicity APIs.

The package now contains the complete roadmap: Specht and product
classification, Young-subgroup induction, branching and Pieri/Littlewood--
Richardson decompositions, regular and biregular representations, tableau and
hook-length dimensions, Young permutation modules, and explicit projector and
branching-operator APIs. Established classical results are isolated behind the
narrow sourced interfaces documented in their Lean docstrings.

## Completed Roadmap

### 1. Young diagrams and subgroup maps

- [x] Package fixed-size Young diagrams and prove their indexing types are finite.
- [x] Define the relation for removing one box from a Young diagram.
- [x] Define adding one box when it is needed independently of removal.
- [x] Define horizontal and vertical strips, initially for strips of size two.
- [x] Package the standard adjacent inclusion
  `Equiv.Perm (Fin n) -> Equiv.Perm (Fin (n + 1))`.
- [x] Generalize the standard inclusion to `m <= n` when needed.
- [x] Package the Young-subgroup embedding
  `S_a x S_b -> S_(a+b)`.
- [x] Prove the elementary compatibility lemmas needed by restriction and
  induction.

The implementation reuses mathlib's Young-diagram, `Equiv.Perm`, and
finite-sum equivalence APIs.

### 2. Outer tensor products

- [x] Construct the outer tensor product `V \boxtimes W` as an `FDRep` of
  `G x H` from representations of `G` and `H`.
- [x] Prove the simplicity result needed for Specht modules.
- [x] Package the classification of irreducibles of `S_m x S_n` by pairs of
  Young diagrams.

This supplies the irreducibles used for groups such as `S_n x S_n` and
`S_2 x S_(n-2)`.

### 3. Finite-dimensional restriction and induction

- [x] Add a thin `FDRep`-level restriction interface around mathlib's `Action.res`.
- [x] Add thin `FDRep`-level induction interfaces around mathlib's `Rep.ind`
  and `Rep.indFunctor`.
- [x] Record finite-dimensionality for induction between the finite groups in
  this package.
- [x] Expose Frobenius reciprocity through mathlib's `Rep.indResHomEquiv` in a
  form convenient for multiplicity calculations.

The underlying constructions belong to mathlib; this layer only packages the
finite-dimensional facts and symmetric-group specializations.

### 4. Branching rule

- [x] Formalize
  `Res^(S_n)_(S_(n-1)) S^lambda ≅ direct_sum_(mu < lambda) S^mu`, where
  `mu < lambda` means that `mu` is obtained by removing one box.
- [x] Formalize the corresponding induction rule obtained by adding one box.
- [x] Derive iterated restriction through `S_(n-2)` and `S_(n-3)`.
- [x] Identify multiplicities in an iterated restriction with paths in the
  Young graph.

Source: Sagan, Section 2.8, especially Theorem 2.8.3.

### 5. Pieri and Littlewood-Richardson rules

- [x] First implement the two Pieri cases used by the thesis:
  induction with the trivial representation of `S_2` adds a horizontal
  two-strip, while induction with the sign representation adds a vertical
  two-strip.
- [x] Express the results as explicit multiplicity-free `FDRep` isomorphisms.
- [x] Generalize to the Littlewood-Richardson rule with arbitrary coefficients.

The general target is
`Ind^(S_(a+b))_(S_a x S_b) (S^mu \boxtimes S^nu)`, with multiplicities given
by Littlewood-Richardson coefficients.

Source: Sagan, Section 4.9, especially Theorem 4.9.4.

### 6. Regular and biregular representations

- [x] Specialize mathlib's regular-representation machinery to finite
  symmetric groups.
- [x] Prove the usual left-regular decomposition, with multiplicity
  `dim S^lambda`.
- [x] Package the `S_n x S_n` biregular decomposition
  `ℂ[S_n] = direct_sum_lambda S^lambda \boxtimes (S^lambda)^*`.
- [x] Record the self-duality specialization for Specht modules.

This is the decomposition of the permutation action on bijections that occurs
in the thesis.

### 7. Dimensions

- [x] Define or connect standard Young tableaux with bases of Specht modules.
- [x] Formalize the hook-length dimension formula.
- [x] Derive the dimension ratios needed when neighboring Young diagrams are
  compared.

These results turn decomposition statements into the numerical multiplicities
and estimates used later in the argument.

### 8. Young permutation modules and Young's rule

- [x] Define arbitrary-shape Young permutation modules on tabloids.
- [x] Identify the two-row module with induction of the trivial representation
  from `S_a x S_b`.
- [x] State Young's rule with Kostka-number multiplicities.
- [x] For `k <= n`, derive the special decomposition of the permutation
  representation on `k`-subsets. Writing `r = min k (n-k)`, the exact chain is
  `kSubsetRepresentation n k ≅ M^(n-r,r) ≅ direct_sum_(i=0)^r S^(n-i,i)`.

Source: Sagan, Section 2.11, especially Theorem 2.11.2. This also provides a
small end-to-end test of classification, induction, and decomposition.

### 9. Multiplicity spaces and explicit operators

- [x] Build the Young branching basis along
  `S_n > S_(n-1) > S_(n-2) > S_(n-3)`.
- [x] Formalize the Young orthogonal or seminormal action of adjacent
  transpositions.
- [x] Package isotypical projectors using mathlib's character theory where
  possible.
- [x] Define the canonical inclusions, projections, and transporters between
  repeated irreducible summands.
- [x] Use Schur's lemma to reduce equivariant maps to maps between
  multiplicity spaces.

This is the layer needed after the abstract decompositions, when the adversary
operator is written in blocks and its coefficients are calculated.

## Completed Implementation Order

1. Young-diagram relations and subgroup embeddings.
2. Outer tensor products and `FDRep` restriction/induction interfaces.
3. Branching and the two `S_2` Pieri cases.
4. Regular and biregular decompositions.
5. Hook-length dimensions and the `k`-subset example.
6. Branching bases, projectors, and multiplicity-space operators.
7. General Littlewood-Richardson coefficients.

## First Milestone

The first milestone is complete. The package states and derives the
decompositions in the representation-theoretic setup of Rosmanis's Chapter 5:

- the `S_n x S_n` action on bijections;
- the restrictions down to `S_(n-1)`, `S_(n-2)`, and `S_(n-3)`;
- the summands induced from groups containing `S_2 x S_(n-2)`; and
- the resulting irreducible labels and multiplicities.
