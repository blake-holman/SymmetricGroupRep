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

## Work Package C: COMPLETE (commits 0339ee6, 6cdf3dd, d5e436a)

`SymmetricGroupRep/KostkaConvolution.lean` (526 lines), imported into
`SymmetricGroupRep.lean`. Endpoint:

```lean
theorem sum_kostka_mul_littlewoodRichardson {a b : ℕ}
    (α : YoungDiagramOfSize a) (β : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) :
    ∑ μ : YoungDiagramOfSize a, ∑ ν : YoungDiagramOfSize b,
        kostkaNumber μ α * kostkaNumber ν β *
          littlewoodRichardsonCoefficient μ ν ξ =
      kostkaNumber ξ (α.combine β)
```

Layers, in dependency order:

- One-row shapes: `singleRowPartition_rowLen`, `mem_singleRowPartition`,
  `colLen_singleRowPartition`, `singleRowPartition_zero`, plus
  `schurPoly_bot` and `YoungDiagram.eq_bot_of_card_eq_zero`.
- One-row tableaux: `singleRow_ext` (a one-row tableau is determined by its
  weight) and `exists_singleRow_weight` (every admissible weight occurs).
  Both reuse the `rowFill`/`SkewFilling`/`GoodTableau.ofMatrix` machinery
  already in `LittlewoodRichardsonBridge.lean`; no new word construction was
  needed. `GoodTableau.ofMatrix` forced `N = a + r`, obtained by
  `obtain ⟨a, rfl⟩ : ∃ a, N = a + r`; its `mu`-indexed companions
  (`isGood_ofMatrix`, `addWeight_ofMatrix`) were NOT usable because they tie
  `mu`'s size to the variable count, so goodness and `addWeight` are proved
  directly instead.
- `schurPoly_mul_schurPoly_singleRow`: the one-row Pieri rule in `N ≥ n + r`
  variables, from `Stembridge.schurPoly_mul_schurPoly` by `Finset.sum_bij`
  onto the horizontal strips. Goodness ⟹ strip cuts the row just before its
  first entry above `i` (`Nat.find`), giving `colWeight j i = 0` and
  `colWeight j (i+1) = weight (i+1)`; strip ⟹ goodness is
  `Stembridge.isGood_iff` plus `colWeight ≤ weight`.
- `card_weight_fiber`: the peeling recursion, `Equiv.sigmaFiberEquiv` over
  `T ↦ T.tableau.below ℓ` plus `Nat.card_sigma` and
  `BoundedSemistandardTableau.fiberEquiv`; the top weight is recovered from
  `sum_weight`.
- `prod_schurPoly_singleRow`: induction on `ℓ` generalizing `n`.
- `hProd`, `hProd_eq_prod_range`, `hProd_eq_sum_kostka`, `hProd_combine`.
- `eq_of_sum_C_mul_schurPoly_eq`: fixed-size Schur independence over `ℤ`, via
  `Stembridge.alt_staircase_mul_schurPoly` and
  `Stembridge.eq_of_sum_alt_staircase_eq`. The `kostka_convolution_cancel`
  fallback route was therefore not needed here.

No blockers. `#print axioms sum_kostka_mul_littlewoodRichardson` is
`[propext, Classical.choice, Quot.sound]`; likewise for `hProd_eq_sum_kostka`
and `eq_of_sum_C_mul_schurPoly_eq`.

Lean lessons: `Finset.range_subset` is `range n ⊆ s ↔ ∀ x < n, x ∈ s` — for
`range ⊆ range` use `Finset.range_subset_range`; `YoungDiagram.get_rowLens`
would not fire under `simp only`, `simp [YoungDiagram.rowLens]` does; pair
projections `(0, c).1` block `omega`, so restate through
`have : T.tableau 0 c = i := hval`; a `rw [← h]` that also occurs inside
`restrict T h` breaks the motive, so rewrite the membership statement in a
separate `have`.

## Work Package C Planning Notes (superseded by the section above)

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

## Next Exact Goal

Work Package E (guide §4, §9). Combine `sum_kostka_mul_finrank_hom_ind`
(WP B) with `sum_kostka_mul_littlewoodRichardson` (WP C) and apply
`kostka_convolution_cancel` (WP D) twice, once in `α` and once in `β`, to get
`finrank_hom_ind_spechtOuterTensor_eq_lr`; then the frozen assembly, the
`AxiomAudit.lean` entry, the docs update, and the full gate (guide §14).
Import direction to watch: `KostkaConvolution.lean` imports
`LittlewoodRichardsonBridge.lean` and `Kronecker.lean`, both of which already
import `LittlewoodRichardson.lean`.

## Verification Log

- 2026-08-13: b9029a7 (A1), 9f8d069 (row equiv + A2 linearization),
  97bb7c5 (generalized induction), 7f7230d (merged tabloid + endpoint).
  Each layer: zero lean-lsp diagnostics; final layer also
  `lake env lean SymmetricGroupRep/YoungPermutationProduct.lean` OK;
  `verify_build_coverage.py` and `verify_frozen_signatures.py` pass
  (25/27 converted; LR + deferred Kronecker still axioms, as expected).
- 2026-08-13: 0339ee6 (one-row Pieri), 6cdf3dd (product of one-row Schur
  polynomials), d5e436a (Kostka convolution). Each layer: zero lean-lsp
  diagnostics and `lake env lean SymmetricGroupRep/KostkaConvolution.lean` OK.
  Final: `lake build` 3263 jobs zero errors; `verify_build_coverage.py`
  (71/71 modules) and `verify_frozen_signatures.py` (25/27, all frozen
  signatures preserved) pass; no `sorry`/`admit`/`native_decide`/`unsafe` in
  the new module.

## Work Package E: COMPLETE — THE LR AXIOM IS A THEOREM

Import restructure: the tableau/coefficient definitions moved verbatim to the
new `SymmetricGroupRep/LittlewoodRichardsonCoefficient.lean`;
`LittlewoodRichardsonBridge.lean` and `Kronecker.lean` now import that module,
freeing `LittlewoodRichardson.lean` (which the frozen-signature verifier pins
as the theorem's home) to import the whole proof stack
(`KostkaConvolution`, `KostkaInverse`, `LittlewoodRichardsonRepresentation`).

`LittlewoodRichardson.lean` now contains:
- `finrank_hom_ind_spechtOuterTensor_eq_lr` (private): the two convolution
  identities (WP B and WP C) agree against every pair of Young weights, so
  `kostka_convolution_cancel` applied in the first and then the second index
  forces `finrank (S^ξ ⟶ Ind (S^μ ⊠ S^ν)) = littlewoodRichardsonCoefficient μ ν ξ`.
- `spechtModule_littlewoodRichardson` as a `theorem` with the frozen
  signature, assembled exactly as in guide §4 (the `youngsRule` pattern).

Verification (final gate, all passing):
- `python3 docs/verify_frozen_signatures.py` — 26/27 converted; all frozen
  signatures preserved (only the deferred Kronecker target remains an axiom).
- `python3 docs/verify_build_coverage.py` — every module reachable.
- `lake build` — 3264 jobs, zero errors.
- `rg '^\s*axiom'` — only `twoRowKroneckerCoefficient_eq_roundTrip_sub`
  (Kronecker.lean:176, explicitly deferred and out of scope).
- No `sorry`/`admit`/`native_decide`/`unsafe` anywhere.
- `#print axioms spechtModule_littlewoodRichardson` =
  `[propext, Classical.choice, Quot.sound]` — no project axiom; the theorem
  does not depend on the deferred Kronecker axiom. Guarded in
  `SymmetricGroupRep/AxiomAudit.lean`.
- `docs/axiom-elimination-status.md` LR row set to **verified**;
  `docs/proof-dag.json` LR target node state set to `theorem`, line 81.

Note: some other rows of the status table were already stale before this
loop (they predate the baseline) and were deliberately left untouched.
