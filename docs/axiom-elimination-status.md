# Axiom elimination status

Frozen baseline: `5f00453e209977aa0a6a8845e646e080b4a45676` on branch
`agent/complete-symmetric-group-roadmap`.

Independently confirmed target count: **27**. The inventory below was produced by
scanning `rg -n '^\s*axiom\s+' --glob '*.lean' .` against the frozen baseline and
extracting each declaration verbatim with `git show 5f00453:<file>`.

Baseline `lake build`: succeeds (3210 jobs). Current: succeeds (3232 jobs).

Progress: **12 of 27 verified**, 15 `axiom` declarations remain in the tree.

The classification of the complex irreducibles of `S_n` by Young diagrams is
fully proved — irreducibility, distinctness and completeness — and so is the
classification of the irreducibles of `S_m × S_n` as outer tensor products. Every
target that is a *decomposition into Specht modules with computed multiplicities*
is now closed as well: the Kronecker product, the left-regular representation,
and the biregular representation. Self-duality is closed too.

The engine behind all of them is the isotypic decomposition in multiplicity form,
`FDRep.exists_iso_biproduct_multiplicity`, together with its two corollaries
`FDRep.nonempty_iso_of_finrank_hom_eq` and
`FDRep.nonempty_iso_of_character_eq_of_complete`. These are now stated for an
arbitrary finite group rather than only for symmetric groups, which is what lets
the same argument run over `S_n × S_n` for the biregular decomposition.

Every remaining target needs genuinely new mathematics: induction and restriction
(branching, Pieri, Littlewood--Richardson, Young's rule), the standard tableau
basis, or hook-length combinatorics.

## Build coverage

`lake build` only compiles what is reachable from the root module. Seven modules
were outside that graph — `CharacterProjectorAlgebra`, `CharacterProjectorReal`,
`ElementDistinctness`, `PaddedDiagrams`, `PaddedHookBounds`,
`SpechtCharacterReal`, `TwoStepBranchingBasis` — so "build green" was never full
coverage of the tree. All 43 modules are now imported from the root, so the
build checks everything.

That gap had concealed a real regression. Making `spechtModule` a concrete
definition rather than an axiom gave terms mentioning it actual definitional
content, and two proofs in `TwoStepBranchingBasis.lean` then exceeded the
default `whnf` heartbeat budget. A build-coverage audit initially recorded this
as pre-existing because it compared against `HEAD`, which already contained the
concrete definition; comparing against the frozen baseline `5f00453` in a
detached worktree showed the module compiling cleanly there. The regression was
therefore introduced by this project and is fixed by raising the heartbeat limit
in that file — a resource bound, not an assumption, and the same device already
used in `Induction.lean` and `PaddedHookBounds.lean`.

`TwoStepBranchingBasis.lean` carries nine pre-existing lint hints (`simpa` that
could be `simp`, and unused simp arguments). These are present verbatim at the
frozen baseline and are left alone, since rewriting them would modify code
unrelated to axiom elimination. The build has **zero errors**.

## Mechanised completion checks

Two of the completion checks are now enforced rather than inspected by hand, so
that drift fails loudly instead of silently:

- **Signature preservation.** `python3 docs/verify_frozen_signatures.py` extracts
  each of the 27 targets from the frozen baseline and from the working tree,
  strips the leading keyword, normalises whitespace, and requires the working
  tree text to be the frozen signature followed by nothing but a `:=` body
  marker. It also rejects any conversion to a declaration form other than
  `theorem` or `noncomputable def`. The script was negative-tested: it catches
  both an added hypothesis and an altered conclusion. Current status: 7/27
  converted, all 27 signatures preserved.
- **Axiom closure.** `SymmetricGroupRep/AxiomAudit.lean` records the
  `#print axioms` closure of every converted target inside `#guard_msgs`, and is
  imported from the root module, so `lake build` fails if any closure changes.

## Declaration forms

Twenty-four targets are proposition-valued and become `theorem`. Three are
data-valued and, because Lean rejects `theorem` for data, become
`noncomputable def` with their signatures preserved exactly:

| Target | Result type | Module |
|---|---|---|
| `spechtModule` | `SymmetricGroupRepresentation n` | `Classification.lean` |
| `twoRowKostkaIndexEquiv` | `… ≃ Fin (min k (n - k) + 1)` | `Kostka.lean` |
| `spechtBranchingBasisData` | `SpechtBranchingBasisData` | `BranchingBasis.lean` |

## Frozen signatures

Reproduced verbatim from the baseline. Any conversion must match these
character for character apart from the leading keyword.

### `Classification.lean`

```lean
axiom spechtModule {n : ℕ} (μ : YoungDiagramOfSize n) : SymmetricGroupRepresentation n

axiom spechtModule_irreducible {n : ℕ} (μ : YoungDiagramOfSize n) : Simple (spechtModule μ)

axiom spechtModule_iso_iff_eq {n : ℕ} (μ ν : YoungDiagramOfSize n) :
  Nonempty (spechtModule μ ≅ spechtModule ν) ↔ μ = ν

axiom exists_iso_spechtModule {n : ℕ} (V : SymmetricGroupRepresentation n) [Simple V] :
  ∃ μ : YoungDiagramOfSize n, Nonempty (V ≅ spechtModule μ)
```

### `Tableaux.lean`

```lean
axiom exists_spechtTableauBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ))
```

### `HookLength.lean`

```lean
axiom standardYoungTableau_card_mul_hookProduct {n : ℕ}
    (μ : YoungDiagramOfSize n) :
  Nat.card (StandardYoungTableau μ) * μ.val.hookProduct = n.factorial
```

### `Branching.lean`

```lean
axiom spechtModule_branching {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
  Nonempty ((SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val)

axiom spechtModule_induction_branching {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.induction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxAddition μ => spechtModule ν.val)
```

### `BranchingBasis.lean`

```lean
axiom spechtBranchingBasisData : SpechtBranchingBasisData
```

### `YoungPermutation.lean`

```lean
axiom youngPermutationModule_twoRow_induction (a b : ℕ) (h : b ≤ a) :
  Nonempty (youngPermutationModule (twoRowPartition (a + b) b (by omega)) ≅
    (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (𝟙_ (FDRep ℂ (SymmetricGroup a × SymmetricGroup b))))
```

### `Kostka.lean`

```lean
axiom youngsRule {n : ℕ} (weight : YoungDiagramOfSize n) :
  Nonempty (youngPermutationModule weight ≅
    ⨁ fun shape : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (kostkaNumber shape weight) => spechtModule shape)

axiom twoRowKostkaIndexEquiv (n k : ℕ) (hk : k ≤ n) :
  (Σ shape : YoungDiagramOfSize n,
    Fin (kostkaNumber shape (twoRowWeight n k hk))) ≃
      Fin (min k (n - k) + 1)

axiom twoRowKostkaIndexEquiv_shape (n k : ℕ) (hk : k ≤ n)
    (copy : Σ shape : YoungDiagramOfSize n,
      Fin (kostkaNumber shape (twoRowWeight n k hk))) :
    copy.1 = twoRowShape n k hk (twoRowKostkaIndexEquiv n k hk copy)
```

### `LittlewoodRichardson.lean`

```lean
axiom spechtModule_littlewoodRichardson {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b) :
  Nonempty
    ((SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (spechtOuterTensor μ ν) ≅
        ⨁ fun ξ : YoungDiagramOfSize (a + b) =>
          ⨁ fun _ : Fin (littlewoodRichardsonCoefficient μ ν ξ) =>
            spechtModule ξ)
```

### `Pieri.lean`

```lean
axiom spechtModule_pieri_horizontal {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.youngSubgroupInduction n 2).obj
    (FDRep.outerTensor (spechtModule μ) (𝟙_ (SymmetricGroupRepresentation 2))) ≅
      ⨁ fun ν : HorizontalTwoStrip μ => spechtModule ν.val)

axiom spechtModule_pieri_vertical {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.youngSubgroupInduction n 2).obj
    (FDRep.outerTensor (spechtModule μ) (SymmetricGroupRepresentation.sign 2)) ≅
      ⨁ fun ν : VerticalTwoStrip μ => spechtModule ν.val)
```

### `ProductClassification.lean`

```lean
axiom existsUnique_iso_spechtOuterTensor {m n : ℕ}
    (V : FDRep ℂ (SymmetricGroup m × SymmetricGroup n)) [Simple V] :
    ∃! p : YoungDiagramOfSize m × YoungDiagramOfSize n,
      Nonempty (V ≅ spechtOuterTensor p.1 p.2)
```

### `Kronecker.lean`

```lean
axiom spechtModule_kronecker {n : ℕ} (μ ν : YoungDiagramOfSize n) :
  Nonempty (spechtInnerTensor μ ν ≅
    ⨁ fun ξ : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (kroneckerCoefficient μ ν ξ) => spechtModule ξ)

axiom spechtModule_singleRow (n : ℕ) :
  Nonempty (spechtModule (singleRowPartition n) ≅
    𝟙_ (SymmetricGroupRepresentation n))

axiom spechtModule_tensor_sign {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (spechtModule (YoungDiagramOfSize.transpose μ) ≅
    spechtModule μ ⊗ SymmetricGroupRepresentation.sign n)

axiom twoRowKroneckerCoefficient_eq_roundTrip_sub
    (n i j : ℕ) (hi : 1 < i) (hj : 1 < j)
    (hin : 2 * i < n) (hjn : 2 * j < n)
    (ν : YoungDiagramOfSize n) :
  kroneckerCoefficient
      (twoRowPartition n i (by omega))
      (twoRowPartition n j (by omega)) ν =
    youngSubgroupRoundTripMultiplicity i (by omega)
        (twoRowPartition n j (by omega)) ν -
      youngSubgroupRoundTripMultiplicity (i - 1) (by omega)
        (twoRowPartition n j (by omega)) ν
```

### `Orthogonal.lean`

```lean
axiom spechtOrthogonalBasis_adjacentTransposition {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
        (spechtOrthogonalBasis μ T) =
      ((T.axialDistance i : ℂ)⁻¹) • spechtOrthogonalBasis μ T +
        Complex.sqrt (1 - ((T.axialDistance i : ℂ)⁻¹) ^ 2) •
          swappedOrthogonalBasisVector μ T i
```

### `SelfDuality.lean`

```lean
axiom spechtModule_selfDual {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (spechtModule μ ≅ (spechtModule μ)ᘁ)
```

### `RegularDecomposition.lean`

```lean
axiom symmetricGroupLeftRegular_decomposition (n : ℕ) :
  Nonempty
    (symmetricGroupLeftRegular n ≅
      ⨁ fun μ : YoungDiagramOfSize n =>
        ⨁ fun _ : Fin (Module.finrank ℂ (spechtModule μ)) => spechtModule μ)
```

### `Biregular.lean`

```lean
axiom symmetricGroupBiregular_decomposition (n : ℕ) :
  Nonempty
    (symmetricGroupBiregular n ≅
      ⨁ fun μ : YoungDiagramOfSize n =>
        FDRep.outerTensor (spechtModule μ) ((spechtModule μ)ᘁ))
```

### `SchurWeyl.lean`

```lean
axiom tensorPower_schurWeyl (q n : ℕ) (hn : 0 < n) :
  Nonempty (tensorPowerPermutationRepresentation q n ≅
    ⨁ fun shape : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (schurWeylMultiplicity q shape) => spechtModule shape)

axiom schurWeylMultiplicity_mul_hookProduct {n : ℕ}
    (q : ℕ) (shape : YoungDiagramOfSize n) :
  (schurWeylMultiplicity q shape : ℤ) * shape.val.hookProduct =
    shape.val.schurContentProduct q
```

## Verification state

Legend: `axiom` = untouched frozen target; `in-progress` = under active proof;
`verified` = converted, `lake build` green, `#print axioms` closure free of
project axioms.

Layers are computed from `docs/axiom-dependency-graph.json` as the longest
prerequisite chain ending at each node, so every edge strictly increases the
layer. The audit script confirms 27 nodes, no directed cycle, and no edge with
`layer(from) >= layer(to)`.

| Layer | Target | Form | State |
|---|---|---|---|
| 0 | `spechtModule` | noncomputable def | **verified** |
| 0 | `youngPermutationModule_twoRow_induction` | theorem | axiom |
| 0 | `twoRowKostkaIndexEquiv` | noncomputable def | **verified** |
| 0 | `standardYoungTableau_card_mul_hookProduct` | theorem | axiom |
| 0 | `schurWeylMultiplicity_mul_hookProduct` | theorem | axiom |
| 1 | `spechtModule_irreducible` | theorem | **verified** |
| 1 | `spechtModule_singleRow` | theorem | **verified** |
| 1 | `spechtModule_selfDual` | theorem | **verified** |
| 1 | `exists_spechtTableauBasis` | theorem | axiom |
| 1 | `twoRowKostkaIndexEquiv_shape` | theorem | **verified** |
| 2 | `spechtModule_iso_iff_eq` | theorem | **verified** |
| 3 | `exists_iso_spechtModule` | theorem | **verified** |
| 4 | `spechtModule_kronecker` | theorem | **verified** |
| 4 | `symmetricGroupLeftRegular_decomposition` | theorem | **verified** |
| 4 | `existsUnique_iso_spechtOuterTensor` | theorem | **verified** |
| 4 | `spechtModule_tensor_sign` | theorem | axiom |
| 4 | `spechtModule_branching` | theorem | axiom |
| 4 | `youngsRule` | theorem | axiom |
| 5 | `symmetricGroupBiregular_decomposition` | theorem | **verified** |
| 5 | `spechtModule_littlewoodRichardson` | theorem | axiom |
| 5 | `spechtModule_induction_branching` | theorem | axiom |
| 5 | `tensorPower_schurWeyl` | theorem | axiom |
| 5 | `spechtBranchingBasisData` | noncomputable def | axiom |
| 6 | `spechtModule_pieri_horizontal` | theorem | axiom |
| 6 | `spechtModule_pieri_vertical` | theorem | axiom |
| 6 | `twoRowKroneckerCoefficient_eq_roundTrip_sub` | theorem | axiom |
| 6 | `spechtOrthogonalBasis_adjacentTransposition` | theorem | axiom |

## Global blocker

Resolved: `spechtModule` is now a checked `noncomputable def`, so the 20 targets
that mention it in their statements are no longer blocked by it. The record of
why it was the critical path is kept below.

`spechtModule` is data-valued and appears in the statement of 20 of the other 26
targets. While it remains an `axiom`, every one of those 20 has a `#print axioms`
closure containing a project axiom, so none of them can be accepted. Converting
`spechtModule` to a checked `noncomputable def` is therefore the critical path
for the whole project, even though it is a graph root.

Four targets mention no axiom at all in their statements and so can be proved
independently of the Specht construction:
`youngPermutationModule_twoRow_induction`, `twoRowKostkaIndexEquiv` (with its
companion `twoRowKostkaIndexEquiv_shape`),
`standardYoungTableau_card_mul_hookProduct`, and
`schurWeylMultiplicity_mul_hookProduct`. The last two are self-contained
combinatorics — the hook-length and hook-content formulas — with no
representation theory in them.

## Import-order obstruction

`spechtModule` lives in `Classification.lean`, whose only project import is
`YoungDiagrams.lean`. The tabloid permutation module it must be carved out of is
defined in `YoungPermutation.lean`, which sits *above* `Classification.lean` in
the import order (`YoungPermutation` imports `Pieri` imports `Branching` imports
`Classification`). Constructing `spechtModule` therefore requires relocating the
tabloid construction (`Tabloid`, its `MulAction`, `youngPermutationModule`,
`twoRowPartition`) into a new module below `Classification.lean`, keeping every
name and type unchanged, and re-importing it from `YoungPermutation.lean`.

## Shared infrastructure missing from mathlib

Audited against the vendored `mathlib` rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6`
(toolchain `leanprover/lean4:v4.29.1`). Instance-availability claims below were
checked by elaborating probe files, not by reading names alone.

What mathlib already gives us, and which nodes it serves:

| Available | Declaration | Used by |
|---|---|---|
| Maschke | `MonoidAlgebra.instIsSemisimpleModule`, `Representation.instIsSemisimpleRepresentation` | every decomposition node |
| Schur | `FDRep.finrank_hom_simple_simple`, `CategoryTheory.endomorphism_simple_eq_smul_id` | layers 4–6 |
| Characters | `FDRep.scalar_product_char_eq_finrank_equivariant`, `FDRep.char_orthonormal`, `FDRep.char_iso`, `FDRep.char_conj`, `FDRep.char_dual` | self-duality, sign twist |
| Simplicity test | `FDRep.simple_iff_char_is_norm_one`, `FDRep.simple_iff_end_is_rank_one` | already used by `FDRep.simple_outerTensor` |
| Frobenius | `Rep.indResAdjunction`, `Rep.resIndAdjunction`, `Rep.coindResAdjunction`, `Rep.indCoindIso` | branching, Pieri, Littlewood–Richardson |
| Wedderburn | `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` | regular and biregular decompositions |
| Conjugacy | `Equiv.Perm.partition_eq_of_isConj`, `Equiv.Perm.exists_with_cycleType_iff` | classification completeness |
| Biproducts | `biproductBiproductIso`, `biproduct.reindex`, `Functor.mapBiproduct` | already used throughout |

What does **not** exist and must be built as shared infrastructure. None of these
is itself a frozen target, so each is an ordinary supporting development:

1. **Isotypic decomposition in `FDRep`** — **now proved locally**, in both the
   form mathlib's module theory hands over and the form the targets are stated
   in, for an arbitrary finite group. Mathlib has no `IsSemisimpleCategory` class and no theorem writing an
   object of an abelian category as a biproduct of simples; the route taken was
   the module-level one
   (`IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`) transported across
   `Representation.asModule`, giving `FDRep.exists_iso_biproduct_simples`,
   followed by `FDRep.exists_iso_biproduct_multiplicity`, which regroups the
   repetitions into multiplicities. Needed by
   `spechtModule_kronecker`, `youngsRule`, `spechtModule_littlewoodRichardson`,
   `spechtModule_branching`, `tensorPower_schurWeyl`, and both regular
   decompositions. This was the single largest piece of shared scaffolding.
2. **Equal characters imply isomorphic**, for `FDRep ℂ G` with `G` finite —
   **now proved locally**. Only the forward direction `FDRep.char_iso` is in
   mathlib. The real content is `FDRep.nonempty_iso_of_finrank_hom_eq`, which
   matches two representations that contain each simple equally often;
   `FDRep.nonempty_iso_of_character_eq_of_complete` derives the character form
   from it through `scalar_product_char_eq_finrank_equivariant`, and
   `SymmetricGroupRepresentation.nonempty_iso_of_character_eq` specialises that
   to the Specht family. Used by `spechtModule_selfDual`; still available for
   `spechtModule_tensor_sign`.
3. **At most as many simples as conjugacy classes** — **now proved locally**, as
   `FDRep.card_le_card_conjClasses` in `SimpleCount.lean`. Absent from mathlib;
   no `ConjClasses` appears anywhere in its representation theory. Needed by
   `exists_iso_spechtModule`.
4. **`ConjClasses (Equiv.Perm (Fin n)) ≃ Nat.Partition n`** — **now proved
   locally**, as `SymmetricGroup.conjClassesEquivPartition` in `Partitions.lean`.
   Both halves existed separately — `partition_eq_of_isConj` for injectivity and
   `exists_with_cycleType_iff` for surjectivity — but not the bijection.
5. **`YoungDiagramOfSize n ≃ Nat.Partition n`** — **now proved locally**, as
   `YoungDiagramOfSize.equivPartition` in `Partitions.lean`. `YoungDiagram` and
   `Nat.Partition` are never mentioned in the same mathlib file;
   `YoungDiagram.equivListRowLens` was the starting point.
6. **`(Vᘁ).character g = V.character g⁻¹` for the rigid dual** — **now proved
   locally** as `FDRep.char_rightDual` in `Semisimple.lean`. Mathlib states
   `FDRep.char_dual` only for `FDRep.of (Representation.dual V.ρ)` and its own
   source TODO asks for the rigid form. An earlier note here blamed a coercion
   mismatch; that diagnosis was wrong — the real gap was the missing
   identification of `FGModuleCat`'s right adjoint mate with
   `Module.Dual.transpose`, and the way through is
   `rightAdjointMate_comp_evaluation` read at an element.
7. **Character of an induced representation**, and `Rep.ind` along a
   finite-index inclusion as a coset-indexed direct sum. Neither exists.
   `Rep.coindToInd` is defined as a sum over right cosets and is the closest
   available starting point. Needed by
   `youngPermutationModule_twoRow_induction` and the Pieri and
   Littlewood–Richardson nodes.
8. **All Specht and tableau combinatorics.** A case-insensitive search of
   mathlib for `Specht`, `youngSymmetrizer`, `polytabloid`, and `tabloid`
   returns nothing, and there is no `StandardYoungTableau`, no hook length, and
   no hook-length formula. Everything on this front is project-local.

Two instance facts that constrain how proofs must be written:

- `HasFiniteBiproducts (FDRep k G)` is **not** a global instance;
  `Limits.HasFiniteBiproducts.of_hasFiniteProducts` and
  `Abelian.hasFiniteBiproducts` are theorems, not instances. The
  `attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts`
  line the project already opens biproduct-using files with is required, not
  incidental.
- `NeZero (Nat.card G : ℂ)` does not synthesize automatically and gates every
  Maschke-derived instance. It must be supplied explicitly for
  `SymmetricGroup n`.

## Source-pack findings

Every node's `sources` field in the graph now carries the PDF, the physical page
index to pass to `--pages`, the printed page number, and the numbered label,
extracted with the supplied `pdf_text.py` extractor rather than inferred from the
Lean comments. Page arithmetic for Sagan is physical = printed + 14 in Chapters
1–2 and printed + 13 from Chapter 3 on.

Four discrepancies between the reference pack and the Lean docstrings were found.
None of them requires editing a docstring, but each changes what a proof can lean
on.

1. **`rosmanis-2014-thesis.pdf` is the wrong document.** The bundled file is the
   22-page arXiv:1401.3826v3 paper *Quantum Adversary Lower Bound for Element
   Distinctness with Small Range*, not the 181-page thesis the pack's
   `README.md` describes. It has no Section 1.4.2 and no Lemma 1.12. Both cited
   passages were re-verified against a correct copy of the thesis found elsewhere
   on this machine; page references in the graph are for the real thesis.
2. **`twoRowKroneckerCoefficient_eq_roundTrip_sub` has no proof in its source.**
   Rosmanis states Lemma 1.12 without proof and explicitly declines to introduce
   the determinantal form or the general Littlewood–Richardson rule that a proof
   would need. This is the highest-risk node in the graph: it must be proved here
   from Littlewood–Richardson and branching. The thesis's Corollary 1.13, a
   special case, *is* proved from the branching rule and is the model to follow.
3. **The Etingof copy is the January 2011 draft** with flat per-chapter
   numbering, so the docstrings' published-edition labels do not resolve in it.
   The mapping is recorded per node: 4.1.1(ii) is Theorem 3.1(ii) p. 33; 4.2.4 is
   Corollary 3.7 p. 35; the product classification 3.10.2 is Theorem 4.25 p. 54;
   there is no analogue of 4.5.4, only an unnumbered Peter–Weyl remark on p. 68.
   Docstrings are left untouched because they cite the published edition
   correctly.
4. **Pieri is never named in Sagan 2e.** A full-text search over all 254 pages
   returns zero hits. Both Pieri nodes are therefore derived as the one-row and
   one-column specialisations of Theorem 4.9.4, which is how the graph already
   routes them.

One confirmation worth recording: `spechtModule_tensor_sign` is *not* in Sagan
either — the conjugate partition appears there only in the symmetric-function
chapters. James 1978, equation (6.6) and Theorem 6.7 (printed p. 25), is the
correct source, and the docstring already cites it.

## Source hunt outcome

A 14-agent hunt over the 12 recorded source gaps fetched 36 candidate documents;
18 were promoted into `.claude/reference-pdfs/` (added alongside the originals,
never overwriting). A completeness critic then re-verified every claimed download
and spot-checked page references. Full details live in
`docs/axiom-dependency-graph.json` under `source_pack_issues`, `prior_art` and
`strategy_revisions`. The consequential outcomes:

**Repairs.** The published Etingof edition resolves all four previously
unresolvable docstring labels. The real 181-page Rosmanis thesis makes six
citation sites across four modules resolvable. Both were added without
overwriting anything.

**One recommendation was wrong, and the critic caught it.** The hunt proposed
Ballantine–Orellana Theorem 2.1 as a proved replacement for the unproved Rosmanis
Lemma 1.12, claiming it holds for an arbitrary second partition. It does not: it
assumes `λ₁ − λ₂ ≥ 2p`, which the Lean target's hypotheses do not imply
(`i = j = ⌊n/2⌋ − 1` satisfies the target and violates the theorem). The proposed
replacement is *strictly narrower* than the statement it was meant to support, so
`twoRowKroneckerCoefficient_eq_roundTrip_sub` **regresses to unsourced** and must
be proved here. Two further cited page references were also shown to be
mislabelled, and one — Sagan Theorem 3.11.1 for the shared hook lemma — was shown
to be **circular**, since Sagan derives the determinantal formula *from* the hook
formula.

**A structural finding.** All 23 remaining targets are `Nonempty (X ≅ Y)` in
`FDRep ℂ`, but every recommended source for Pieri, Young's rule and
Littlewood–Richardson states a *character* or symmetric-function identity, and
mathlib has only the forward direction `FDRep.char_iso`. So "equal characters ⇒
isomorphic" is not an optional convenience; it is a **hard prerequisite** without
which those sources discharge no axiom at all. It is now recorded as revision R2
and sits ahead of seven targets.

**Prior art, verified independently.** `TauCetiProject/TauCeti` is Apache-2.0,
Lean 4 on mathlib, and I confirmed directly — not by relay — that the cited files
exist at the claimed sizes with zero `sorry`: the submodule theorem and
irreducibility (273 lines), distinctness, completeness, absolute irreducibility,
Kostka unitriangularity (331 lines), corner theory, bounded-SSYT interlacing, the
Weyl dimension formula, Frobenius reciprocity and Mackey, and a
`Comparison.lean` identifying the polytabloid Specht module with the
Young-symmetrizer ideal. It also has
`card_simpleSubmoduleClasses_le_card_conjClasses`, filling a genuine mathlib gap.
It is developed over `ℚ` in `Representation`/`Submodule` rather than `FDRep ℂ`,
so adopting it is a port with base change and a categorical wrapper, not a copy —
and every ported result still has to clear this project's own `#print axioms`
audit.

## Next step

Layers 1 to 4 are closed apart from `exists_spechtTableauBasis`,
`spechtModule_tensor_sign`, `spechtModule_branching` and `youngsRule`.

Nothing further comes out of the decomposition engine on its own. Every remaining
target names a multiplicity that the engine cannot compute from what is already
proved: `youngsRule` needs Kostka numbers, `spechtModule_littlewoodRichardson`
needs the Littlewood--Richardson rule, `spechtModule_branching` needs the
branching rule, `tensorPower_schurWeyl` needs Schur--Weyl. Each of those is a
theorem about induction and restriction, so item 7 of the missing-infrastructure
list — the character of an induced representation, and `Rep.ind` along a
finite-index inclusion — is now the critical path, and it feeds six targets.

Three targets remain independent of that path and are the cheapest available:

- `spechtModule_tensor_sign`, which now has both of its prerequisites — the
  classification and "equal characters imply isomorphic" — and reduces to
  computing the sign-twisted Specht character.
- `standardYoungTableau_card_mul_hookProduct` and
  `schurWeylMultiplicity_mul_hookProduct`, self-contained combinatorics with no
  representation theory in them.

## Resolved apparent cycles

The cycle audit in the graph records three, all broken by naming a lower-level
construction rather than letting one target justify another:

1. `exists_spechtTableauBasis` versus `spechtModule_branching`. Dimension
   counting derives the tableau basis from branching, while the classical proof
   of branching uses the tableau basis. Broken by proving the standard basis
   theorem directly from Garnir relations and straightening on the polytabloid
   module, so the edge runs only from the basis to branching.
2. The classification triple. Completeness of the Specht list can be argued from
   branching by induction, which would make layers 1 to 3 depend on layer 4.
   Broken by proving completeness from the independent count of conjugacy
   classes of `Equiv.Perm (Fin n)` against partitions of `n`.
3. `youngsRule` / `spechtModule_littlewoodRichardson` /
   `twoRowKroneckerCoefficient_eq_roundTrip_sub`, which all speak about
   restrict-then-induce multiplicities. Broken by deriving
   Littlewood--Richardson from the semistandard basis and Young's rule, and
   letting Rosmanis's reduction consume both.

## Verification log

### Layer 0 and 1: `twoRowKostkaIndexEquiv`, `twoRowKostkaIndexEquiv_shape`

Converted together, since the second is the shape component of the first.
`twoRowKostkaIndexEquiv` is one of the three data-valued targets and became a
`noncomputable def`; `twoRowKostkaIndexEquiv_shape` became a `theorem`. Both
signatures were diffed against `git show 5f00453:SymmetricGroupRep/Kostka.lean`
and are identical apart from the leading keyword.

The mathematics, following Sagan Definition 2.11.1 and Theorem 2.11.2 with the
conventions cross-checked against Tomczak Corollary 3.19, is purely
combinatorial and touches no representation theory. For the weight `(n - r, r)`
the content condition forces every entry to be `0` or `1`, column strictness
then caps the shape at two rows, and the second row is forced to be all ones
sitting under zeros. Counting zeros pins the shape to `(n - i, i)` with
`i ≤ r` and makes the filling unique, so each such shape contributes exactly one
Kostka copy and no other shape contributes any. The equivalence sends a copy to
the length of its shape's second row.

Supporting material added:

- `YoungDiagram.ext_of_rowLen` in `YoungDiagrams.lean`: a Young diagram is
  determined by its row lengths.
- `twoRowPartition_cells` and `YoungDiagramOfSize.eq_twoRowPartition` in
  `YoungPermutation.lean`, next to the existing `twoRowPartition_rowLen`.
- A `WeightedSemistandardTableau` section in `Kostka.lean` proving the structure
  facts above, an explicit witness tableau (kept `private`, since it exists only
  to prove the count), and the four public Kostka lemmas
  `kostkaNumber_twoRow_eq_one`, `kostkaNumber_twoRow_eq_one_of_pos`,
  `eq_twoRowPartition_of_kostkaNumber_pos`, and `shape_eq_of_rowLen_one_eq`.

Verification:

- `#print axioms` for both targets: `[propext, Classical.choice, Quot.sound]`.
  No project axiom, no `sorryAx`.
- Recorded in `SymmetricGroupRep/AxiomAudit.lean`, which wraps each
  `#print axioms` in `#guard_msgs` so the closure is checked by the build rather
  than only inspected once. The module is imported from `SymmetricGroupRep.lean`,
  so `lake build` fails if any recorded closure changes.
- `lake build`: `Build completed successfully (3211 jobs)`, no warnings.

### Layer 0: `spechtModule`

The critical-path target, and one of the three data-valued ones, so it became a
`noncomputable def`. Signature diffed against
`git show 5f00453:SymmetricGroupRep/Classification.lean` and identical apart
from the leading keyword.

The import-order obstruction recorded above was resolved by splitting two new
modules out *below* `Classification.lean`, preserving every existing name and
type: `SymmetricGroupRep/Basic.lean` (`SymmetricGroup`,
`SymmetricGroupRepresentation`) and `SymmetricGroupRep/Tabloids.lean` (the
tabloid development moved down from `YoungPermutation.lean`).
`Tabloid.nonempty` was refactored into a reusable `Tabloid.ofCellEquiv` rather
than duplicating its counting proof.

`SymmetricGroupRep/Polytabloid.lean` then carries the construction proper,
following Sagan Section 2.3: `YoungTableau` as a bijective filling, the
`columnGroup` of a tableau (Definition 2.3.1), `polytabloid` (Definition 2.3.2),
and `spechtSubrepresentation` as the span of the polytabloids inside the Young
permutation module (Definition 2.3.4). Invariance of that span is Sagan's Lemma
2.3.3(4), proved as `YoungTableau.smul_polytabloid` by conjugating the column
group, which is the only real content needed for the definition to typecheck as
a subrepresentation.

Because a wrong construction here would silently poison every downstream target,
the module is also proved non-degenerate rather than merely well-typed:
`YoungTableau.eq_one_of_mem_columnGroup_of_smul_tabloid_eq` shows a
column-preserving relabelling fixing the tabloid is the identity, so
`polytabloid_apply_tabloid` gives coefficient one on the tableau's own tabloid,
and `polytabloid_ne_zero` with `spechtSubrepresentation_ne_bot` show the Specht
module is nonzero.

Verification:

- `#print axioms spechtModule`: `[propext, Classical.choice, Quot.sound]`,
  recorded in `AxiomAudit.lean` under `#guard_msgs`.
- `lake build`: `Build completed successfully (3214 jobs)`, no warnings. The
  whole downstream tree still compiles against the concrete definition.

### Layer 1: `spechtModule_singleRow`

The one-row shape has `rowLen 0 = n` and every other row empty, so a tabloid's
`row_nonempty` field forces every label into row zero: the tabloid type is a
subsingleton, and `Tabloid.nonempty` makes it `Unique`. The permutation module is
therefore one dimensional and carries the trivial action.

`spechtSubrepresentation_singleRow_eq_top` shows the Specht submodule is all of
it, reusing `YoungTableau.polytabloid_apply_tabloid` from the construction layer:
with a unique tabloid the polytabloid is exactly `Finsupp.single default 1`, so
every vector is a scalar multiple of it. The last step is free —
`FDRep.of (Representation.trivial ℂ G ℂ)` is *definitionally* the monoidal unit
`𝟙_`, checked by `rfl`, so `Action.mkIso` on the resulting `Representation.Equiv`
closes the goal.

Verification: `#print axioms spechtModule_singleRow` is
`[propext, Classical.choice, Quot.sound]`, recorded under `#guard_msgs`;
`lake build` green at 3214 jobs with no warnings.

### Layer 1: `spechtModule_irreducible`

Sagan's Submodule Theorem 2.4.4 and Theorem 2.4.6, over `ℂ`, in the new module
`SymmetricGroupRep/SubmoduleTheorem.lean`. `FDRep.simple_of_isIrreducible`
reduces the target to `Representation.IsIrreducible` of
`(spechtSubrepresentation μ).toRepresentation`, so the whole proof lives at
submodule level and the conversion itself is a one-liner.

Three pieces make it up.

- **The counting lemma** `YoungTableau.column_lt_rowLen_of_injective`: if a label
  is determined by its row in a tabloid `U` together with its column in a tableau
  `t`, then those two indices are again the coordinates of a cell of `μ`. The
  labels in the first `k` columns of `t` number `∑ i, min (μ.rowLen i) k`, while
  row `i` of `U` holds at most `min (μ.rowLen i) k` of them — at most `rowLen i`
  because that is the length of the row, and at most `k` because the labels in
  one row of `U` have distinct columns in `t`. Upper bounds that add up to the
  total are equalities, and `k = μ.rowLen i` is the statement. This is the only
  real combinatorics in the file; the rest is bookkeeping.
- **Sagan's Corollary 2.4.3** `YoungTableau.columnAntisymmetriser_single_mem_span`:
  the column antisymmetriser `κ_t` sends a tabloid into the line spanned by the
  polytabloid `e_t`. Either two labels share a row of `U` and a column of `t`, and
  their transposition is an odd element of the column group fixing `U`, so `κ_t U`
  equals its own negative; or none do, and the counting lemma exhibits `U` as a
  column permutation of the tabloid of `t`, which `κ_t` absorbs through its sign.
- **The tabloid form** `tabloidForm`, taken Hermitian rather than bilinear. Over
  `ℚ` Sagan's form is positive definite for free; over `ℂ` a symmetric bilinear
  form can be degenerate on `S^μ` for all this argument says, and the submodule
  theorem alone does not exclude it, so the second argument is conjugated. The
  form is then positive definite, `S^μ ∩ (S^μ)^⊥ = 0` is immediate, and
  `G`-invariance survives because the permutation matrices are real.

`spechtSubrepresentation_le_or_forall_tabloidForm_eq_zero` is the submodule
theorem, and `isIrreducible_spechtSubrepresentation` reads it back as
`IsSimpleOrder (Subrepresentation …)` by pushing a subrepresentation of `S^μ`
forward along the inclusion into `M^μ`.

The mathematics follows `TauCetiProject/TauCeti` (Apache-2.0), files
`RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean`,
`RepresentationTheory/Symmetric/Vanishing.lean` and
`Combinatorics/Young/Tableau.lean`; the credit is recorded on each adapted
declaration. Nothing was copied: their development is over `ℚ`, states the
Specht module through a quotient-of-cosets tabloid and a group-algebra
symmetriser, and their form is bilinear, so every proof was rewritten against
this package's `Tabloid` structure, `YoungTableau.columnGroup` and the Hermitian
form.

Verification:

- `#print axioms spechtModule_irreducible`:
  `[propext, Classical.choice, Quot.sound]`, recorded in `AxiomAudit.lean` under
  `#guard_msgs`.
- `lake build`: `Build completed successfully (3217 jobs)`, no warnings.
- `python3 docs/verify_frozen_signatures.py`: exit 0, 5/27 converted.

### Layer 2: `spechtModule_iso_iff_eq`

Sagan's Proposition 2.4.5 and the distinctness half of Theorem 2.4.6, over `ℂ`,
in the new module `SymmetricGroupRep/Distinctness.lean`. The dominance order was
added next to `YoungDiagramOfSize` as `YoungDiagram.Dominates` — partial sums of
row lengths, compared termwise — together with
`YoungDiagram.Dominates.antisymm`, which is `YoungDiagram.ext_of_rowLen` applied
to consecutive differences of equal partial sums. The conversion itself then
reads: an isomorphism gives dominance each way, and antisymmetry gives equality.

Three pieces make up the dominance statement.

- **`YoungTableau.dominates_of_injective`**, the dominance lemma: if a label is
  determined by its row in a tabloid `S` of shape `ν` together with its column
  in a tableau `t` of shape `μ`, then `μ ⊵ ν`. The labels in the first `j` rows
  of `S` number `∑ i < j, ν.rowLen i`; each column `c` of `t` holds at most
  `min (μ.colLen c) j` of them, at most `μ.colLen c` because that is the length
  of the column and at most `j` because those labels have distinct rows in `S`;
  and summing that bound over the columns of `t` counts exactly the cells of `μ`
  in its first `j` rows, which is `∑ i < j, μ.rowLen i`. The last equality is
  read off the tableau itself rather than proved about diagrams: `t` is a
  bijection from labels to cells, so both sides are fiberwise counts of the same
  label set.
- **`YoungTableau.dominates_of_smul_eq_sign_smul`**, Proposition 2.4.5 in
  eigenvector form: a nonzero vector of `M^ν` that the column group of a
  `μ`-tableau scales by the sign forces `μ ⊵ ν`. Take a tabloid where the vector
  has a nonzero coefficient; two labels sharing a row of it and a column of `t`
  would give an odd column permutation fixing it, so the coefficient would equal
  its own negative. Hence no two do, and the dominance lemma applies.
- **`dominates_of_iso_spechtSubrepresentation`**, the transport to `FDRep`. An
  isomorphism is injective, so it sends the polytabloid of a tableau — nonzero
  by `polytabloid_ne_zero` — to a nonzero vector of `S^ν`, hence of `M^ν`; and
  equivariance turns `YoungTableau.smul_polytabloid_of_mem_columnGroup`, which
  is Sagan's Sign Lemma 2.4.1 for the column group, into the sign eigenvector
  property there. The statement is phrased with `FDRep.of (spechtSubrepresentation _)`
  rather than `spechtModule`, which is definitionally the same thing, so that
  the module can sit below `Classification.lean`.

One existing declaration was generalised rather than duplicated:
`YoungTableau.exists_mem_columnGroup_sign_eq_neg_one` in `SubmoduleTheorem.lean`
now allows the tabloid a shape of its own, since its proof reads only the rows
of the tabloid and the columns of the tableau. The two counting lemmas in
`Distinctness.lean` are `private` and are the transposes of the ones in
`SubmoduleTheorem.lean`; unifying the two pairs would need a transpose operation
on tableaux, which is more machinery than it would save.

`TauCetiProject/TauCeti` (Apache-2.0) proves the same theorem in
`RepresentationTheory/Symmetric/Specht/Distinctness.lean`, but by a different
route — a group-algebra column symmetriser transported along a permutation
congruence between the label sets of the two shapes — so nothing here is adapted
from it. The counting lemmas are transposes of ones in `SubmoduleTheorem.lean`,
whose credit to that package stands.

Verification:

- `#print axioms spechtModule_iso_iff_eq`:
  `[propext, Classical.choice, Quot.sound]`, recorded in `AxiomAudit.lean` under
  `#guard_msgs`.
- `lake build`: `Build completed successfully (3218 jobs)`, no warnings.
- `python3 docs/verify_frozen_signatures.py`: exit 0, 6/27 converted.

### Shared infrastructure: the multiplicity form of the decomposition

No target was converted in this step; the isotypic decomposition was completed
instead. `SymmetricGroupRepresentation.exists_iso_biproduct_simples` produces a
biproduct of simples listed *with repetitions*, indexed by `Fin k`, whereas every
consuming target names each simple once and records how often it occurs.
`SymmetricGroupRepresentation.exists_iso_biproduct_multiplicity` in
`Decomposition.lean` bridges the two, in the general form: for a family `S` of
pairwise non-isomorphic simples that exhausts the simples, every `V` satisfies

```lean
V ≅ ⨁ i, ⨁ _ : Fin (Module.finrank ℂ (S i ⟶ V)), S i
```

The proof classifies each summand `T j` by the member of `S` it is isomorphic to,
giving `c : Fin k → ι`, and then does two independent things with `c`. The
multiplicities are counted through Schur's lemma: `finrank ℂ (S i ⟶ V)` equals
`∑ j, finrank ℂ (S i ⟶ T j)` by `FDRep.homCongrTarget` and
`FDRep.homBiproductLinearEquiv`, each term is `1` or `0` by
`FDRep.finrank_hom_simple_simple`, and the resulting count is `Nat.card` of the
fibre of `c` over `i` — the two hypotheses on `S` are what make the term `1`
exactly when `c j = i`. The isomorphism itself is assembled by
`biproduct.reindex` along `Equiv.sigmaFiberEquiv c`, `biproductBiproductIso` to
regroup, and a second `biproduct.reindex` sending each fibre to `Fin` of its
cardinality, which is where the count is consumed.

The five general `FDRep` Hom lemmas the proof needed already existed in
`ElementDistinctness.lean` — `homFinrank`, `homCongrTarget`,
`homBiproductLinearEquiv`, `homFinrank_iso_target`, `homFinrank_biproduct` — but
that module sits far above `Decomposition.lean` in the import order, and it is
imported by nothing, so `lake build` never checked it. They were moved down into
`Decomposition.lean` unchanged, rather than duplicated; `ElementDistinctness.lean`
keeps `outerTensorIso`, which depends on modules above, and still compiles.

Verification:

- `#print axioms SymmetricGroupRepresentation.exists_iso_biproduct_multiplicity`:
  `[propext, Classical.choice, Quot.sound]`, recorded in `AxiomAudit.lean` under
  `#guard_msgs`.
- `lake build`: `Build completed successfully (3218 jobs)`, no warnings.
  `ElementDistinctness.lean`, which the build does not reach, was compiled
  separately with `lake env lean` and is clean.
- `python3 docs/verify_frozen_signatures.py`: exit 0, still 6/27 converted, all
  27 signatures preserved.

`spechtModule_kronecker` was **not** converted, on purpose. Its
`kroneckerCoefficient` is by definition the Hom dimension this lemma produces, so
the target is one application of the lemma to the Specht family — and the
application was elaborated to confirm exactly that — but its completeness
hypothesis can only come from `exists_iso_spechtModule`, which is still an axiom.
Landing it now would close a frozen target through a project axiom.

### Layer 3: `exists_iso_spechtModule`

Completeness of the Specht list, the counting half of Sagan's Theorem 2.4.6, in
the two new modules `SymmetricGroupRep/SimpleCount.lean` and
`SymmetricGroupRep/Partitions.lean`. With `spechtModule_irreducible` and
`spechtModule_iso_iff_eq` already converted, the Specht modules were known to be
pairwise non-isomorphic simples indexed by `YoungDiagramOfSize n`; the missing
ingredient was an upper bound on how many pairwise non-isomorphic simples there
can be. The conversion is that bound applied to the Specht family with one
hypothetical extra simple adjoined: if some simple `V` were isomorphic to no
Specht module, the family indexed by `Option (YoungDiagramOfSize n)` would have
one more member than `S_n` has conjugacy classes.

Three pieces, none of them in mathlib, make up the bound.

- **`FDRep.card_le_card_conjClasses`** in `SimpleCount.lean`: a family of
  pairwise non-isomorphic simple objects of `FDRep ℂ G`, `G` finite, has at most
  `Nat.card (ConjClasses G)` members. `FDRep.char_conj` makes a character
  constant on conjugacy classes, so `FDRep.classCharacter` reads it as a
  function on `ConjClasses G`; mathlib's `FDRep.char_orthonormal` then makes the
  family orthonormal for the pairing `⅟|G| * ∑ g, χ_i g * χ_j g⁻¹`, and pairing
  a vanishing linear combination against each `χ_j` returns its coefficient. The
  characters are therefore linearly independent in `ConjClasses G → ℂ`, whose
  dimension is `Nat.card (ConjClasses G)` by `Module.finrank_pi`.
- **`SymmetricGroup.conjClassesEquivPartition`** in `Partitions.lean`:
  `ConjClasses (S_n) ≃ n.Partition`. `Equiv.Perm.partition` lands in
  `(Fintype.card (Fin n)).Partition`, so `SymmetricGroup.partition` restates it
  at index `n`; `Equiv.Perm.partition_eq_of_isConj` gives both well-definedness
  on classes and injectivity. Surjectivity is `SymmetricGroup.exists_partition_eq`:
  the parts of `p` that are at least two are realised as a cycle type by
  `Equiv.Perm.exists_with_cycleType_iff`, and the remaining parts are all `1` by
  positivity, which is exactly the block of fixed points that
  `Equiv.Perm.partition` appends.
- **`YoungDiagramOfSize.equivPartition`** in `Partitions.lean`:
  `YoungDiagramOfSize n ≃ n.Partition`, by row lengths. Forwards is
  `YoungDiagram.rowLens` as a multiset, positive by
  `YoungDiagram.pos_of_mem_rowLens` and summing to `n` by the package's own
  `YoungDiagram.card_eq_rowLens_sum`. Backwards is `Multiset.sort (· ≥ ·)` fed to
  `YoungDiagram.ofRowLens`. The two compose to the identity because a list is
  determined by its multiset once it is sorted, which is
  `List.Perm.eq_of_pairwise'`.

Two shaping decisions are worth recording. The bound is stated for an arbitrary
indexed family rather than for a type of isomorphism classes, which avoids
quotienting the large type `FDRep ℂ (S_n)` — the step that the earlier
reconnaissance recorded as a separate missing piece. And `IsConj.setoid` is a
`local instance` in mathlib, so both new modules re-declare it locally in order
to use `Quotient.lift` on `ConjClasses`.

`TauCetiProject/TauCeti` (Apache-2.0) proves the corresponding bound as
`card_simpleSubmoduleClasses_le_card_conjClasses` in
`RepresentationTheory/CharacterTable/SimpleModuleCount.lean`, but over an
arbitrary field with semisimple group algebra, via the dimension of the centre of
`k[G]` and the class-sum basis. That route needs two developments this package
does not have; the character-theoretic route above works only over `ℂ` but rests
entirely on mathlib, so nothing here is adapted from it.

Verification:

- `#print axioms exists_iso_spechtModule`:
  `[propext, Classical.choice, Quot.sound]`, recorded in `AxiomAudit.lean` under
  `#guard_msgs`.
- `lake build`: `Build completed successfully (3232 jobs)`, only the nine
  pre-existing `TwoStepBranchingBasis.lean` lint hints.
- `python3 docs/verify_frozen_signatures.py`: exit 0, 7/27 converted, all 27
  signatures preserved.

`existsUnique_iso_spechtModule`, the uniqueness wrapper that was already stated
in `Classification.lean`, is now also free of project axioms. The note under the
previous entry, that `spechtModule_kronecker` could not be landed because its
completeness hypothesis was an axiom, no longer applies.

### Layer 1: `spechtModule_selfDual`

The dual character is `g ↦ χ(g⁻¹)` — `FDRep.char_rightDual`, proved earlier here —
and every symmetric-group character is inversion-invariant, because
`Equiv.Perm.cycleType_inv` makes `g` and `g⁻¹` conjugate. So `S^μ` and `(S^μ)ᘁ`
have the same character, and the conversion is one application of the converse of
`FDRep.char_iso`.

That converse is item 2 of the missing-infrastructure list and is the reusable
part of this step. It is proved in two stages in `Decomposition.lean`:

- `FDRep.nonempty_iso_of_finrank_hom_eq`: two representations that contain each
  member of a complete family of pairwise non-isomorphic simples equally often
  are isomorphic. Both sides are expanded by
  `FDRep.exists_iso_biproduct_multiplicity` and the resulting biproducts are
  matched summand by summand with `biproduct.reindex (finCongr _)`.
- `FDRep.nonempty_iso_of_character_eq_of_complete`: equal characters give equal
  multiplicities, because
  `FDRep.scalar_product_char_eq_finrank_equivariant` computes every multiplicity
  as a scalar product of characters. `Nat.cast` is injective in `ℂ`, so the
  equality of dimensions follows from the equality in `ℂ`.

`SymmetricGroupRepresentation.nonempty_iso_of_character_eq` in
`Classification.lean` specialises the second to the Specht family.

Two existing declarations moved rather than being duplicated:
`symmetricGroup_inverse_isConj` and `symmetricGroup_character_inv` came down from
`CharacterProjectorReal.lean` into `Semisimple.lean`, which already hosts the
other character facts about `FDRep ℂ (S_n)` that mathlib leaves to its callers.
`CharacterProjectorReal.lean` sits above `YoungPermutation.lean` in the import
order, so `SelfDuality.lean` could not have reached them where they were.

Verification: `#print axioms spechtModule_selfDual` is
`[propext, Classical.choice, Quot.sound]`, recorded under `#guard_msgs`;
`lake build` green at 3232 jobs.

### Layer 4: `spechtModule_kronecker`

The one-line target the previous stage predicted. `kroneckerCoefficient μ ν ξ` is
*defined* in `Kronecker.lean` as `finrank ℂ (S^ξ ⟶ S^μ ⊗ S^ν)`, which is exactly
the multiplicity `FDRep.exists_iso_biproduct_multiplicity` produces, so the
conversion is that lemma applied to the Specht family at `spechtInnerTensor μ ν`.
The three hypotheses are `spechtModule_irreducible`, `spechtModule_iso_iff_eq`
and `exists_iso_spechtModule`, all converted.

Verification: `#print axioms spechtModule_kronecker` is
`[propext, Classical.choice, Quot.sound]`, recorded under `#guard_msgs`.

### Layer 4: `symmetricGroupLeftRegular_decomposition`

The same application, at `symmetricGroupLeftRegular n`, plus the one computation
it needs: `finrank_hom_symmetricGroupLeftRegular` in `Regular.lean`, that every
representation occurs in `ℂ[S_n]` with multiplicity its own dimension.

`symmetricGroupLeftRegular_character` computes the regular character by reading
`LinearMap.trace` as a matrix trace in `Finsupp.basisSingleOne`: the matrix of
left multiplication by `g` has diagonal entry `1` at `x` exactly when `g * x = x`,
which by `mul_eq_right` happens for all `x` when `g = 1` and for no `x`
otherwise. The character pairing then collapses to its single term at `g = 1`,
where `FDRep.char_one` returns the dimension.

The multiplicities that `exists_iso_biproduct_multiplicity` produces are Hom
dimensions, while the frozen statement names `finrank ℂ (S^μ)`, so the two
biproducts are matched with `biproduct.reindex (finCongr _)` as above.

Verification: `#print axioms symmetricGroupLeftRegular_decomposition` is
`[propext, Classical.choice, Quot.sound]`, recorded under `#guard_msgs`.

### Layer 4: `existsUnique_iso_spechtOuterTensor`

The classification for `S_m × S_n`, proved by the same counting argument as
`exists_iso_spechtModule` and reusing `FDRep.card_le_card_conjClasses` unchanged,
since that bound was already stated for an arbitrary finite group.

Three pieces, all in `ProductClassification.lean`:

- `FDRep.finrank_hom_outerTensor` in `OuterTensor.lean`: equivariant maps between
  outer tensor products are counted factorwise,
  `finrank (V ⊠ W ⟶ V' ⊠ W') = finrank (V ⟶ V') * finrank (W ⟶ W')`. The
  character of an outer tensor product is a product, so the pairing over `G × H`
  factors as the product of the pairings over `G` and over `H`.
- `spechtOuterTensor_iso_iff_eq`, distinctness, is that formula read through
  Schur's lemma: an isomorphism makes the left side `1`, so both factors on the
  right are `1`, so both labels agree. This lemma previously existed in the file
  but was derived *from* the axiom; it is now proved directly and moved above the
  target, which consumes it.
- `ConjClasses.prodEquiv`, with `isConj_prod_iff` under it: conjugacy in a
  product group is componentwise, so the conjugacy classes of `S_m × S_n` are
  pairs of conjugacy classes. Composed with the two equivalences from
  `Partitions.lean`, that makes the number of pairs of Young diagrams equal to
  the number of conjugacy classes, and one more simple would exceed the bound.

Verification: `#print axioms existsUnique_iso_spechtOuterTensor` is
`[propext, Classical.choice, Quot.sound]`, recorded under `#guard_msgs`.

### Layer 5: `symmetricGroupBiregular_decomposition`

Both sides are representations of `S_n × S_n`, so this is the first target that
needs the decomposition engine over a group other than a symmetric group. The
three lemmas in `Decomposition.lean` were therefore generalised from
`SymmetricGroupRepresentation n` to `FDRep ℂ G` for `[Group G] [Finite G]
[NeZero (Nat.card G : ℂ)]` and moved into the `FDRep` namespace. No proof changed
— only the binders — and the `NeZero` and `Invertible` instances in
`Semisimple.lean` were generalised from symmetric groups to finite groups for the
same reason, which also removed their two special cases.

The decomposition itself is proved by matching multiplicities rather than
characters, which avoids needing the second orthogonality relation. Both sides
contain `S^μ ⊠ S^ν` exactly `if μ = ν then 1 else 0` times:

- `symmetricGroupBiregular_character`: the basis vector at `x` is fixed by
  `(g, h)` exactly when `x⁻¹ * g * x = h`, so the character is a count of
  conjugators. `finrank_hom_symmetricGroupBiregular` sums that count against the
  Specht characters: the indicator collapses the sum over `h`, replacing `h` by
  `x⁻¹ * g * x` for each `x`; `FDRep.char_conj` then makes every term independent
  of `x`, leaving `Nat.card (S_n)` copies of the ordinary pairing of `χ_μ` with
  `χ_ν`, which Schur's lemma evaluates. `symmetricGroup_character_inv` is what
  turns the two inverse arguments produced by this route into the orientation the
  pairing lemma wants.
- `finrank_hom_spechtDualBiproduct`: Hom out of a fixed object is additive over a
  biproduct (`FDRep.homFinrank_biproduct`), and the summand at `α` contributes
  `finrank (S^μ ⟶ S^α) * finrank (S^ν ⟶ (S^α)ᘁ)` by
  `FDRep.finrank_hom_outerTensor`. Self-duality makes `(S^α)ᘁ` simple
  (`simple_spechtModule_rightDual`, in `SelfDuality.lean`) and isomorphic to
  `S^α`, so the product is `1` only when `α` is both `μ` and `ν`.

`FDRep.nonempty_iso_of_finrank_hom_eq`, applied to the family
`(μ, ν) ↦ S^μ ⊠ S^ν` with `existsUnique_iso_spechtOuterTensor` supplying
completeness, then closes the target.

Verification: `#print axioms symmetricGroupBiregular_decomposition` is
`[propext, Classical.choice, Quot.sound]`, recorded under `#guard_msgs`;
`lake build` green at 3232 jobs with only the nine pre-existing
`TwoStepBranchingBasis.lean` lint hints; `python3 docs/verify_frozen_signatures.py`
exits 0 at 12/27 with all 27 signatures preserved.

