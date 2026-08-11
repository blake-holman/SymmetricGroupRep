# Axiom elimination status

Frozen baseline: `5f00453e209977aa0a6a8845e646e080b4a45676` on branch
`agent/complete-symmetric-group-roadmap`.

Independently confirmed target count: **27**. The inventory below was produced by
scanning `rg -n '^\s*axiom\s+' --glob '*.lean' .` against the frozen baseline and
extracting each declaration verbatim with `git show 5f00453:<file>`.

Baseline `lake build`: succeeds (3210 jobs). Current: succeeds (3214 jobs).

Progress: **4 of 27 verified**, 23 `axiom` declarations remain in the tree.

## Mechanised completion checks

Two of the completion checks are now enforced rather than inspected by hand, so
that drift fails loudly instead of silently:

- **Signature preservation.** `python3 docs/verify_frozen_signatures.py` extracts
  each of the 27 targets from the frozen baseline and from the working tree,
  strips the leading keyword, normalises whitespace, and requires the working
  tree text to be the frozen signature followed by nothing but a `:=` body
  marker. It also rejects any conversion to a declaration form other than
  `theorem` or `noncomputable def`. The script was negative-tested: it catches
  both an added hypothesis and an altered conclusion. Current status: 4/27
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
| 1 | `spechtModule_irreducible` | theorem | axiom |
| 1 | `spechtModule_singleRow` | theorem | **verified** |
| 1 | `spechtModule_selfDual` | theorem | axiom |
| 1 | `exists_spechtTableauBasis` | theorem | axiom |
| 1 | `twoRowKostkaIndexEquiv_shape` | theorem | **verified** |
| 2 | `spechtModule_iso_iff_eq` | theorem | axiom |
| 3 | `exists_iso_spechtModule` | theorem | axiom |
| 4 | `spechtModule_kronecker` | theorem | axiom |
| 4 | `symmetricGroupLeftRegular_decomposition` | theorem | axiom |
| 4 | `existsUnique_iso_spechtOuterTensor` | theorem | axiom |
| 4 | `spechtModule_tensor_sign` | theorem | axiom |
| 4 | `spechtModule_branching` | theorem | axiom |
| 4 | `youngsRule` | theorem | axiom |
| 5 | `symmetricGroupBiregular_decomposition` | theorem | axiom |
| 5 | `spechtModule_littlewoodRichardson` | theorem | axiom |
| 5 | `spechtModule_induction_branching` | theorem | axiom |
| 5 | `tensorPower_schurWeyl` | theorem | axiom |
| 5 | `spechtBranchingBasisData` | noncomputable def | axiom |
| 6 | `spechtModule_pieri_horizontal` | theorem | axiom |
| 6 | `spechtModule_pieri_vertical` | theorem | axiom |
| 6 | `twoRowKroneckerCoefficient_eq_roundTrip_sub` | theorem | axiom |
| 6 | `spechtOrthogonalBasis_adjacentTransposition` | theorem | axiom |

## Global blocker

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

1. **Isotypic decomposition in `FDRep`.** Mathlib has no `IsSemisimpleCategory`
   class and no theorem writing an object of an abelian category as a biproduct
   of simples. The module-level results
   (`IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top`,
   `Mathlib/RingTheory/SimpleModule/Isotypic.lean`) are the realistic route, then
   transported across `Representation.asModule`. Needed by
   `spechtModule_kronecker`, `youngsRule`, `spechtModule_littlewoodRichardson`,
   `spechtModule_branching`, `tensorPower_schurWeyl`, and both regular
   decompositions. This is the single largest piece of shared scaffolding.
2. **Equal characters imply isomorphic**, for `FDRep ℂ G` with `G` finite. Only
   the forward direction `FDRep.char_iso` exists. Needed by
   `spechtModule_selfDual` and `spechtModule_tensor_sign`. Follows from item 1
   plus `scalar_product_char_eq_finrank_equivariant` and
   `finrank_hom_simple_simple`.
3. **Number of simples equals number of conjugacy classes.** Absent; no
   `ConjClasses` appears anywhere in mathlib's representation theory. Needed by
   `exists_iso_spechtModule`.
4. **`ConjClasses (Equiv.Perm (Fin n)) ≃ Nat.Partition n`.** Both halves exist
   separately — `partition_eq_of_isConj` for injectivity and
   `exists_with_cycleType_iff` for surjectivity — but the bijection does not.
5. **`YoungDiagramOfSize n ≃ Nat.Partition n`.** `YoungDiagram` and
   `Nat.Partition` are never mentioned in the same mathlib file.
   `YoungDiagram.equivListRowLens` is the natural starting point.
6. **`(Vᘁ).character g = V.character g⁻¹` for the rigid dual.** Mathlib states
   `FDRep.char_dual` only for `FDRep.of (Representation.dual V.ρ)` and its own
   TODO notes the gap. `Action.rightDual_ρ` supplies the bridge. Needed by
   `spechtModule_selfDual` and `symmetricGroupBiregular_decomposition`.
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

## Next step: irreducibility

With `spechtModule` constructed, the next layer is `spechtModule_irreducible`
via Sagan's submodule theorem: the tabloid-orthonormal bilinear form on `M^μ`,
the Sign Lemma 2.4.1, Corollary 2.4.3 that the column antisymmetriser sends
`M^μ` into the line spanned by `e_t`, and Theorem 2.4.4. `spechtModule_singleRow`
and `spechtModule_selfDual` are also unblocked and are cheaper.

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
