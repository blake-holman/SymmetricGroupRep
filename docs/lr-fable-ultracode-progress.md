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

## Next Exact Goal

Work Package A continues. `YoungDiagramOfSize.combine` (A1) is compiled in
`SymmetricGroupRep/YoungPermutationProduct.lean` with `rowLens_combine` and
`length_rowLens_combine`. Next:

1. Build the row-index equiv: for `l.Perm l'` an `σ : Fin l.length ≃
   Fin l'.length` with `l.get i = l'.get (σ i)` (mathlib had no direct hit via
   loogle for `List.Perm _ _, Fin _ ≃ Fin _`; fall back to induction on
   `List.Perm` if the research workflow finds nothing). Specialize to
   `(α.rowLens ++ β.rowLens).Perm (combine α β).rowLens`.
2. A2: `M^α ⊠ M^β ≅ ℂ[Tabloid α × Tabloid β]` via `finsuppTensorFinsupp` and
   `Action.mkIso` on `Finsupp.single` generators.
3. A3/A4: generalize `indTrivialFinsuppEquiv` (YoungPermutation.lean) to a
   permutation representation: hypotheses on `j : Y → X` are (i) equivariance
   `j (g • y) = φ g • j y`, (ii) surjectivity `∀ x, ∃ h y, h⁻¹ • j y = x`
   (from tabloid pretransitivity), (iii) relative stabilizer
   `h • j y' = j y → ∃ g, φ g = h ∧ g • y' = y` (via
   `mem_youngSubgroupInclusion_range_iff`, block preservation).

An Ultracode research workflow (`lr-api-research`, run wf_2ab03570-519) is
surveying: List.Perm index equivs + rowLens API, the A2 linearization route,
and Work Package D inversion APIs. Read its report before implementing A2.

## Verification Log

- 2026-08-13: `SymmetricGroupRep/YoungPermutationProduct.lean` (A1: combine,
  rowLens_combine, length_rowLens_combine) — zero diagnostics via lean-lsp;
  imported from the root module; `python3 docs/verify_build_coverage.py` and
  `python3 docs/verify_frozen_signatures.py` both pass (25/27 converted, LR
  and Kronecker still axioms, as expected).
