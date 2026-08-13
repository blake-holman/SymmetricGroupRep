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

## Work Package B: COMPLETE (commit a8cdc20)

`SymmetricGroupRep/LittlewoodRichardsonRepresentation.lean`:

- `FDRep.character_biproduct` — bicone/trace proof (`biproduct.total`,
  extraction AddMonoidHom with `map_add' := rfl`, `trace_comp_comm'`,
  `biproduct.ι_π_self`); the private `biproductLinearEquivPi` was NOT needed.
- `character_youngPermutationModule` — char M^α = ∑_μ K(μ,α)·char S^μ.
- `sum_kostka_mul_finrank_hom_ind` —
  `∑_{μ,ν} K(μ,α)·K(ν,β)·finrank(S^ξ ⟶ Ind(S^μ ⊠ S^ν)) = K(ξ, combine α β)`.
  Chain: `finrank_hom_eq_kostkaNumber` ← `homCongrTarget` across
  `youngPermutationCombineIso.symm` ← `hterm` (finrank_hom_symm +
  indFunctor_obj + indResHomEquiv + scalar_product) ← `hexpand`
  (outerTensor_character + Young character rule + sum_mul_sum + sum_comm) ←
  cast via `Nat.cast_inj` + `push_cast`.

Lesson: with a `set X := (Action.res ...).obj ...`, write
`FDRep.character X` (FDRep is an Action abbrev, so dot notation fails).

## Work Package D: COMPLETE (commit 1632b6f)

`SymmetricGroupRep/KostkaInverse.lean`: `exists_kostka_inverse` (strict
dominance + `Finite.wellFounded_of_trans_of_irrefl` + `WellFounded.fix`;
verification splits the sum with `Finset.add_sum_erase` + `Finset.sum_subset`
+ `kostkaNumber_self` + `kostkaNumber_eq_zero_of_not_dominates`), and
`kostka_convolution_cancel` (`∀ α, ∑ μ K(μ,α)·c μ = 0` forces `c = 0`, via
the inverse column + `Finset.sum_ite_eq'`).

## Next Exact Goal

Work Package C (guide §7). KEY REALIZATION: C2 needs NO Schur-independence
lemma — extracting `MvPolynomial.coeff (expo (a+b) ξw.val.rowLen)` from the
h-identity turns everything into Kostka-weighted sums, and
`kostka_convolution_cancel` (WP D) recovers the pointwise convolution
`∑_{μ,ν} K(μ,α)K(ν,β)·c^ρ_{μν} = K(ρ, combine α β)`. The only real work is
C1: `hProd q α := (α.partition.parts.map (single-row schurPoly q)).prod =
∑_μ C(K(μ,α)) · schurPoly q μ.val` in q := a+b variables (then
`hProd α · hProd β = hProd (combine)` is `Multiset.prod_add` via
`rowLens_combine`). Watch: C1's Kostka number has size-a indices but q = a+b
variables — may need a q-padded version of `coeff_schurPoly_eq_kostkaNumber`
(via `WeightedSemistandardTableau.boundedEquiv`).

Ultracode planning workflow `lr-wpc-plan` (run wf_4225e3fc-1ff) is producing
the exact C1/C2 signature-checked plan (agent 1: SchurWeyl peeling machinery
+ single-row infrastructure + expo/boundedEquiv generality; agent 2: C2
assembly lemma names + cancellation orientation). Read its report first,
then implement C in `SymmetricGroupRep/LittlewoodRichardsonBridge`-adjacent
new file or extend LittlewoodRichardsonRepresentation.lean.

After C: Work Package E — `finrank_hom_ind_spechtOuterTensor_eq_lr` from
B + C + `kostka_convolution_cancel` (twice, once per index), then the frozen
assembly (guide §4), AxiomAudit entry, docs update, full gate (guide §14).

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
