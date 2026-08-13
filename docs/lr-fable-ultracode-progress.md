# LR Fable Ultracode Progress

## Current State

- Baseline: `12d3c9b76056eb503fbd842d824ac226d17b6642`
- Branch: `agent/complete-symmetric-group-roadmap`
- Starting tree: clean before the guide, loop command, and this journal were added
- In-scope target: `spechtModule_littlewoodRichardson`
- Deferred target: `twoRowKroneckerCoefficient_eq_roundTrip_sub`
- Last known full build: 3259 jobs, zero errors at the baseline

## Compiled Inputs

- `littlewoodRichardsonCoefficient_eq_stembridgeCount`
- `schurPoly_mul_schurPoly_eq_littlewoodRichardson`
- `coeff_schurPoly_eq_kostkaNumber`
- `kostkaNumber_self`
- `kostkaNumber_eq_zero_of_not_dominates`
- `YoungTableau.finrank_hom_eq_kostkaNumber`
- `youngsRule`
- `FDRep.exists_iso_biproduct_multiplicity`
- `FDRep.nonempty_iso_of_finrank_hom_eq`
- `FDRep.finrank_hom_symm`
- `FDRep.indResHomEquiv`
- `FDRep.outerTensor_character`
- `FDRep.indTrivialIso`

## Audited Decision

Use the Young-permutation/Kostka-convolution route in
`docs/lr-fable-ultracode-guide.md`. The direct tableau, full character,
principal Schur-Weyl, iterated Pieri, and Grothendieck-ring routes were audited
and are longer with the current APIs.

## Work Package A: COMPLETE (commit 7f7230d)

All in `SymmetricGroupRep/YoungPermutationProduct.lean` (516 lines):

- `YoungDiagramOfSize.combine`, `rowLens_combine`, `length_rowLens_combine`.
- `combineRowEquiv : Fin #rows(α) ⊕ Fin #rows(β) ≃ Fin #rows(combine)` via
  Batteries `List.Perm.idxBij`, with `rowLen_combineRowEquiv_inl/inr`.
- `Representation.indPermFinsuppEquiv` + `FDRep.indOfMulActionIso`:
  generalized induced-permutation isomorphism. Hypotheses on `j : Y → X`:
  equivariance, `∀ x, ∃ h y, h⁻¹ • j y = x`, and relative stabilizer
  `h • j y' = j y → ∃ g, φ g = h ∧ g • y' = y`.
- `Tabloid.combine` (merged tabloid), the componentwise product `MulAction`
  instance, `outerTensorYoungPermutationIso` (A2), and the endpoint
  `youngPermutationCombineIso : Ind (M^α ⊠ M^β) ≅ M^(combine α β)`.

Key Lean lessons: never `rfl` through `Fin.addCases` on symbolic bounds
(whnf timeout — go through the `combineRowOf_castAdd/natAdd` value lemmas);
build `Sum.inl.inj`/`congrArg` chains bottom-up via intermediate `have`s;
build `Representation.Equiv` over PLAIN representations (not `.ρ` of FDRep
objects) or simp stalls on category-wrapped carriers.

## Next Exact Goal

Work Package B (representation-side convolution), per guide §6:

1. Small API: `FDRep.character_biproduct` (trace of finite biproduct is sum
   of characters) via the private `FDRep.biproductLinearEquivPi`
   (Decomposition.lean:311), following `FDRep.char_iso`.
2. The chain: `finrank Hom(S^ξ, Ind(M^α ⊠ M^β)) = K(ξ, combine α β)` via
   `finrank_hom_eq_kostkaNumber` transported across
   `youngPermutationCombineIso`, then expand with `finrank_hom_symm`,
   `indResHomEquiv`, `youngsRule` on both factors, `outerTensor_character`,
   `scalar_product_char_eq_finrank_equivariant` to get the convolution
   `∑ μ,ν K(μ,α) K(ν,β) cRep(μ,ν,ξ) = K(ξ, combine α β)`.

Work Package D research (from wf_2ab03570-519, agent 3): strict dominance
`r α lam := α ≠ lam ∧ lam.val.Dominates α.val`; `Dominates.antisymm` exists
unconditionally (YoungDiagrams.lean:58); use
`Finite.wellFounded_of_trans_of_irrefl` (needs `Std.Irrefl`) + its `.fix`;
verify the inverse column with `Finset.add_sum_erase` +
`sum_filter_add_sum_filter_not` + `kostkaNumber_self` +
`kostkaNumber_eq_zero_of_not_dominates` — no induction needed.

Work Package C notes: use `BoundedSemistandardTableau.fiberEquiv`
(SchurWeyl.lean) for the h-product identity, keep `a+b` variables.

## Verification Log

- 2026-08-13: b9029a7 (A1), 9f8d069 (row equiv + A2 linearization),
  97bb7c5 (generalized induction), 7f7230d (merged tabloid + endpoint).
  Each layer: zero lean-lsp diagnostics; final layer also
  `lake env lean SymmetricGroupRep/YoungPermutationProduct.lean` OK;
  `verify_build_coverage.py` and `verify_frozen_signatures.py` pass
  (25/27 converted; LR + deferred Kronecker still axioms, as expected).
