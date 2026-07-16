# Representation-Theory Roadmap

## Goal

Provide the symmetric-group representation theory needed to formalize the
decompositions used in Rosmanis's small-range element-distinctness argument.
The package should reuse mathlib's representations, restriction, induction,
characters, and categorical simplicity APIs.

The current package contains an explicit complex Specht-classification interface in
`SymmetricGroupRep/Classification.lean` and the first branching-rule interface in
`SymmetricGroupRep/Branching.lean`, based on Sagan, Theorems 2.4.6 and 2.8.3.

## Remaining Work

### 1. Young diagrams and subgroup maps

- [x] Define the relation for removing one box from a Young diagram.
- [ ] Define adding one box when it is needed independently of removal.
- [ ] Define horizontal and vertical strips, initially for strips of size two.
- [x] Package the standard adjacent inclusion
  `Equiv.Perm (Fin n) -> Equiv.Perm (Fin (n + 1))`.
- [ ] Generalize the standard inclusion to `m <= n` when needed.
- [ ] Package the Young-subgroup embedding
  `S_a x S_b -> S_(a+b)`.
- [ ] Prove the elementary compatibility lemmas needed by restriction and
  induction.

Before adding definitions, check mathlib's Young-diagram, `Equiv.Perm`, and
finite-sum equivalence APIs for existing versions.

### 2. Outer tensor products

- [ ] Construct the outer tensor product `V \boxtimes W` as an `FDRep` of
  `G x H` from representations of `G` and `H`.
- [ ] Prove the simplicity result needed for Specht modules.
- [ ] Package the classification of irreducibles of `S_m x S_n` by pairs of
  Young diagrams.

This supplies the irreducibles used for groups such as `S_n x S_n` and
`S_2 x S_(n-2)`.

### 3. Finite-dimensional restriction and induction

- [x] Add a thin `FDRep`-level restriction interface around mathlib's `Action.res`.
- [ ] Add thin `FDRep`-level induction interfaces around mathlib's `Rep.ind`
  and `Rep.indFunctor`.
- [ ] Record finite-dimensionality for induction between the finite groups in
  this package.
- [ ] Expose Frobenius reciprocity through mathlib's `Rep.indResHomEquiv` in a
  form convenient for multiplicity calculations.

The underlying constructions already belong to mathlib; this item should only
package the finite-dimensional facts and symmetric-group specializations.

### 4. Branching rule

- [x] Formalize
  `Res^(S_n)_(S_(n-1)) S^lambda ≅ direct_sum_(mu < lambda) S^mu`, where
  `mu < lambda` means that `mu` is obtained by removing one box.
- [ ] Formalize the corresponding induction rule obtained by adding one box.
- [ ] Derive iterated restriction through `S_(n-2)` and `S_(n-3)`.
- [ ] Identify multiplicities in an iterated restriction with paths in the
  Young graph.

Source: Sagan, Section 2.8, especially Theorem 2.8.3.

### 5. Pieri and Littlewood-Richardson rules

- [ ] First implement the two Pieri cases used by the thesis:
  induction with the trivial representation of `S_2` adds a horizontal
  two-strip, while induction with the sign representation adds a vertical
  two-strip.
- [ ] Express the results as explicit `FDRep` isomorphisms with multiplicities.
- [ ] Generalize to the Littlewood-Richardson rule only when a downstream
  decomposition needs arbitrary coefficients.

The general target is
`Ind^(S_(a+b))_(S_a x S_b) (S^mu \boxtimes S^nu)`, with multiplicities given
by Littlewood-Richardson coefficients.

Source: Sagan, Section 4.9, especially Theorem 4.9.4.

### 6. Regular and biregular representations

- [ ] Specialize mathlib's regular-representation machinery to finite
  symmetric groups.
- [ ] Prove the usual left-regular decomposition, with multiplicity
  `dim S^lambda`.
- [ ] Package the `S_n x S_n` biregular decomposition
  `ℂ[S_n] = direct_sum_lambda S^lambda \boxtimes (S^lambda)^*`.
- [ ] Record the self-duality specialization for Specht modules.

This is the decomposition of the permutation action on bijections that occurs
in the thesis.

### 7. Dimensions

- [ ] Define or connect standard Young tableaux with bases of Specht modules.
- [ ] Formalize the hook-length dimension formula.
- [ ] Derive the dimension ratios needed when neighboring Young diagrams are
  compared.

These results turn decomposition statements into the numerical multiplicities
and estimates used later in the argument.

### 8. Young permutation modules and Young's rule

- [ ] Define the Young permutation module induced from a Young subgroup.
- [ ] State Young's rule with Kostka-number multiplicities.
- [ ] Derive the special decomposition of the permutation representation on
  `k`-subsets:
  `M^(n-k,k) = direct_sum_(i=0)^(min k (n-k)) S^(n-i,i)`.

Source: Sagan, Section 2.11, especially Theorem 2.11.2. This also provides a
small end-to-end test of classification, induction, and decomposition.

### 9. Multiplicity spaces and explicit operators

- [ ] Build the Young branching basis along
  `S_n > S_(n-1) > S_(n-2) > S_(n-3)`.
- [ ] Formalize the Young orthogonal or seminormal action of adjacent
  transpositions.
- [ ] Package isotypical projectors using mathlib's character theory where
  possible.
- [ ] Define the canonical inclusions, projections, and transporters between
  repeated irreducible summands.
- [ ] Use Schur's lemma to reduce equivariant maps to maps between
  multiplicity spaces.

This is the layer needed after the abstract decompositions, when the adversary
operator is written in blocks and its coefficients are calculated.

## Implementation Order

1. Young-diagram relations and subgroup embeddings.
2. Outer tensor products and `FDRep` restriction/induction interfaces.
3. Branching and the two `S_2` Pieri cases.
4. Regular and biregular decompositions.
5. Hook-length dimensions and the `k`-subset example.
6. Branching bases, projectors, and multiplicity-space operators.
7. General Littlewood-Richardson coefficients if later proofs require them.

## First Milestone

The first milestone is complete when the package can state and derive the
decompositions in the representation-theoretic setup of Rosmanis's Chapter 5:

- the `S_n x S_n` action on bijections;
- the restrictions down to `S_(n-1)`, `S_(n-2)`, and `S_(n-3)`;
- the summands induced from groups containing `S_2 x S_(n-2)`; and
- the resulting irreducible labels and multiplicities.
