<!-- Read-only reconnaissance, 2026-08-12, verified against the tree at 7c961f6.
Headline finding: specialise Stembridge to a STRAIGHT shape, which removes skew
SSYT, skew Bender-Knuth, skew Schur functions and the Hopf-algebra machinery
from the Littlewood-Richardson route entirely. -->

# IMPLEMENTATION BRIEF — `spechtModule_littlewoodRichardson`

*Merged from four scout reports, re-verified against the working tree at HEAD `7c961f6` (branch `agent/complete-symmetric-group-roadmap`) on 2026-08-12 ~15:15. Read-only; nothing was edited.*

**State-of-tree update that supersedes the scouts.** Since the scout reports were written, the concurrently-working agent has landed two new untracked files and **both now type-check**:

| file | status |
|---|---|
| `SymmetricGroupRep/BenderKnuth.lean` (506 lines) | compiles; `benderKnuth_benderKnuth` ✅, `weight_benderKnuth_self`/`_succ`/`_of_ne` ✅ |
| `SymmetricGroupRep/SchurPolynomial.lean` (114 lines) | `lake env lean` exits 0 with no diagnostics; olean built 15:07 |

`grep "^axiom"` confirms exactly two axioms remain: `LittlewoodRichardson.lean:72` and `Kronecker.lean:176`. Neither new file is imported from `SymmetricGroupRep.lean` yet (only `TwoBoxInduction` is, at line 49).

---

## 1. Recommended route (one paragraph)

**Run Stembridge's bialternant proof in the specialisation `κ := μ`, skew shape `:= ν` (i.e. inner shape empty), so that every tableau in the argument has a STRAIGHT shape.** Stembridge's theorem `a_{κ+ρ}·s_{λ/μ} = Σ_{good T} a_{κ+ω(T)+ρ}` with inner shape `∅` reads `a_{μ+ρ}·s_ν = Σ_{good T} a_{μ+ω(T)+ρ}`, `T` ranging over ordinary SSYT of shape `ν`, and its corollary is directly the product rule `s_μ·s_ν = Σ_{good T} s_{μ+ω(T)}`. This matters enormously: **no skew semistandard tableaux, no skew Bender–Knuth, no skew Schur functions, and no Hopf-algebra/comultiplication machinery are needed anywhere** — the scouts' cost estimates all assumed the `κ := ∅` specialisation, which needs all four. Everything runs on mathlib's straight-shape `SemistandardYoungTableau` and the repo's `BoundedSemistandardTableau`, which is precisely what the freshly-landed `BenderKnuth.lean` + `SchurPolynomial.lean` already provide (`schurPoly`, `coeff_schurPoly`, `schurPoly_isSymmetric` are done and compiling). The column-truncation `T_{<j}` that the sign-reversing involution acts on is again a straight shape (`rowLen i := min (ν.rowLen i) j`), so the existing `benderKnuth` applies verbatim. The price is that the resulting index set is Stembridge's ("shape `ν`, entries = target rows"), not the frozen Lean one ("shape `ξ/μ`, content `ν`, lattice word"), so a combinatorial bridge is owed — but I verified that bridge is a **matrix transposition** and that it decomposes into two independent, individually-provable equivalences (§3 Layer C, §6). The alternative routes were priced and rejected: Sagan's own proof needs jeu-de-taquin + dual equivalence (Sagan Thm 4.8.12 is stated without proof); the `κ := ∅` skew route needs skew Schur functions plus `⟨s_{ξ/μ}, s_ν⟩ = c^ξ_{μν}`, i.e. the Hall pairing; and a "stay inside representations" route is impossible because the only thing that could replace the symmetric functions is `K_{ξ/λ,β} = Σ_ρ c^ξ_{λρ}K_{ρβ}`, which *is* the LR rule.

---

## 2. What already exists and MUST be reused

### 2.1 The assembly skeleton — copy it, do not re-derive (all three are proved and axiom-clean)

| what | where | note |
|---|---|---|
| `FDRep.exists_iso_biproduct_multiplicity` | `Decomposition.lean:233` | multiplicities stated as `finrank ℂ (S i ⟶ V)` |
| `FDRep.nonempty_iso_of_finrank_hom_eq` | `Decomposition.lean:272` | the Pieri-style shell |
| `youngsRule` | `Kostka.lean:163-172` | **the exact 6-line pattern the LR assembly needs** (double biproduct `⨁ξ ⨁Fin c`) |
| `spechtModule_pieri_horizontal` | `Pieri.lean:46-61` | **the exact Frobenius rewrite chain** (lines 54-57) |
| `spechtModule_pieri_vertical` | `Pieri.lean:69-84` | same |
| `spechtModule_induction_branching` | `Branching.lean:547` | `b = 1` case of the target |

### 2.2 Hom / induction / biproduct calculus

- `FDRep.finrank_hom_symm` — `Decomposition.lean:342`
- `FDRep.indFunctor` — `Induction.lean:54`, carries `@[simps obj map]` so **`FDRep.indFunctor_obj` exists**
- `FDRep.indResHomEquiv` — `Induction.lean:71`: `(ind φ V ⟶ W) ≃ₗ[k] (V ⟶ (Action.res _ φ).obj W)`
- `FDRep.homFinrank_biproduct` — `Decomposition.lean:143`; `homBiproductLinearEquiv` — `:116`; `FDRep.finrank_eq_sum_finrank_hom_mul` — `:353`
- `FDRep.biproductLinearEquivPi` — `Decomposition.lean:311` — **`private`**, will need de-privatising for additivity work
- `SymmetricGroupRepresentation.youngSubgroupInduction a b` — `Pieri.lean:13-16` (frozen vocabulary)
- `SymmetricGroup.youngSubgroupInclusion` — `YoungSubgroup.lean:7`, with `_apply_castAdd` `:19`, `_apply_natAdd` `:27`, `_injective` `:13`, `mem_youngSubgroupInclusion_range_iff` `:34`
- `spechtOuterTensor` — `ProductClassification.lean:42` (`abbrev`, = `FDRep.outerTensor (spechtModule μ) (spechtModule ν)`); irreducibility `:48`, distinctness `:61`
- `FDRep.outerTensor` — `OuterTensor.lean:18`; `outerTensor_character` — `:34`; `finrank_hom_outerTensor` — `:85`
- Classification triple used by every shell: `spechtModule_irreducible`, `spechtModule_iso_iff_eq`, `exists_iso_spechtModule` — `Classification.lean:18/24/33`

### 2.3 Permutation modules, tabloids, induced-trivial

- `Tabloid` — `Tabloids.lean:14-18` (fields `rowOf : Fin n → Fin n`, `row_nonempty`, `content`); `ofCellEquiv` `:36`; `smul_rowOf` `:95`
- `youngPermutationModule` — `Tabloids.lean:122`
- `FDRep.ofMulActionEquiv` — `YoungPermutation.lean:80`
- **`FDRep.indTrivialIso` — `YoungPermutation.lean:97-116`** — the object to generalise (§4 D2)
- `youngPermutationModule_twoRow_induction` — `YoungPermutation.lean:369`, with its `private` inputs `twoRowBaseTabloid` `:322` and `smul_twoRowBaseTabloid_eq_self_iff` `:335` — **the template for the merged base tabloid**
- `YoungDiagramOfSize.equivPartition` — `Partitions.lean:53`; `Nat.Partition.toYoungDiagram` `:29`; `rowLens_toYoungDiagram`; `parts_partition`. **`α ∪ β` should be `Multiset` addition of `.parts`, not a `List.mergeSort`** — this kills the step scout 3 called "the only genuinely fiddly part of Layer C".

### 2.4 Kostka / Young's rule — proved, and the numeric form is what you want

- `WeightedSemistandardTableau` — `Kostka.lean:20-26` (mathlib SSYT + `entry_lt : < n` + `content`)
- `kostkaNumber shape weight` — `Kostka.lean:60` (**shape first**)
- **`YoungTableau.finrank_hom_eq_kostkaNumber` — `Kostka.lean:144`**: `finrank ℂ (spechtModule lam ⟶ youngPermutationModule mu) = kostkaNumber lam mu`. Consume this, not `youngsRule`.
- `YoungTableau.semistandardTabloidEquiv` — `Kostka.lean:116`
- `YoungTableau.finrank_hom_eq_card_semistandard` — `SemistandardHom.lean:1142` + `class LabelFilling` — `:42`. Any new `S_m`-set of labelled fillings gets its Specht multiplicities for free.

### 2.5 Straight-shape SSYT machinery (Schur–Weyl legacy)

- `BoundedSemistandardTableau q μ` — `SchurWeyl.lean:118`; `ext` `:127`; `entries` `:135`; `Fintype` `:147`
- **`BoundedSemistandardTableau.fiberEquiv` — `SchurWeyl.lean:264`**: `{T : Bdd (q+1) μ // T.tableau.below q = ν} ≃ Bdd q ν` — the horizontal-strip peeling, proved. Supporting: `restrict` `:152`, `extend` `:180`, `below_extend` `:222`, `restrict_extend` `:235`, `extend_restrict` `:245`.
- The **summed** form of that recursion is *not* a named lemma; it is inline at `SchurWeyl.lean:307-369` (hypotheses `hmem`/`hcount`/`hterm`/`hfiber`). Extract it, don't redo it.
- `SemistandardYoungTableau.below` `:70`, `row_le_entry` `:60`, `exists_youngDiagram_rowLen` `:39`

### 2.6 NEW, compiling, and load-bearing for this route

- `SemistandardYoungTableau.benderKnuth` — `BenderKnuth.lean:296`; `benderKnuth_benderKnuth` `:362`; `weight` `:394`; `weight_eq_sum` `:413`; `weight_benderKnuth_of_ne` `:456`; `weight_benderKnuth_self` `:464`; `weight_benderKnuth_succ` `:483`; plus the `rowSplit`/`freeStart`/`capAbove`/`freeEnd`/`bkMid` block `:21-192`
- `BoundedSemistandardTableau.weight` — `SchurPolynomial.lean:20` (`Fin q →₀ ℕ`); `bk` `:28`; `bk_bk` `:39`; `weight_bk` `:47`
- `schurPoly (q) (μ : YoungDiagram) : MvPolynomial (Fin q) ℤ` — `SchurPolynomial.lean:67`
- `coeff_schurPoly` — `:73` (coefficient = number of tableaux of that weight — this is your Kostka bridge)
- `schurPoly_isSymmetric` — `:97` (**this is Stembridge's only lemma-level input, already done**)

### 2.7 Dominance

`YoungDiagram.Dominates` — `YoungDiagrams.lean:54` (`∀ j, Σ_{i<j} ν.rowLen i ≤ Σ_{i<j} μ.rowLen i`; **μ is the dominator**); `Dominates.antisymm` — `:58`. No reflexivity/transitivity. `YoungTableau.dominates_of_injective` — `Distinctness.lean:80`; `YoungTableau.ColStrict.injective` — `SemistandardHom.lean:211`.

### 2.8 Definitively absent (grep-verified)

No transitivity of induction (`Ind∘Ind ≅ Ind`) in the repo **or** mathlib. No additivity of `Ind` or `outerTensor` over biproducts. No general Young subgroup for a composition. No `character_biproduct`. No Kostka-dominance lemmas. No alternants. No Schur polynomials, Kostka numbers, RSK or Bender–Knuth in mathlib. `Vandermonde.lean` is numeric (`ℚ`-valued `vanderDec`, `Matrix.vandermonde`) and **cannot** host a bialternant argument.

---

## 3. The proof, as numbered Lean-statable lemmas

Throughout fix `N := a + b`, `ρ : Fin N → ℕ := fun r => N - 1 - r`. All Schur polynomials live in `MvPolynomial (Fin N) ℤ`, one ring for all three sizes.

### Layer A — alternants (~250 lines, all moderate)

| # | statement | deps | size |
|---|---|---|---|
| A1 | `def alt (α : Fin N → ℕ) : MvPolynomial (Fin N) ℤ := ∑ w : Equiv.Perm (Fin N), (Equiv.Perm.sign w : ℤ) • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (α ∘ w)) 1` | — | trivial |
| A2 | `alt_comp : alt (α ∘ σ) = (Equiv.Perm.sign σ : ℤ) • alt α` | A1 | moderate |
| A3 | `alt_eq_zero_of_not_injective : ¬Function.Injective α → alt α = 0` (pair `w` with `w * swap`) | A2 | moderate |
| A4 | `coeff_alt_self : α StrictAnti → (alt α).coeff (of α) = 1`; `coeff_alt_of_ne : α, β both StrictAnti, α ≠ β → (alt α).coeff (of β) = 0` | A1 | moderate |
| A5 | `alt_linearIndependent`: `∑_ξ (n ξ : ℤ) • alt (ξ+ρ) = ∑_ξ (m ξ) • alt (ξ+ρ) → n = m`, over `ξ : YoungDiagramOfSize N` | A4 | moderate |

`ξ + ρ` is strictly decreasing for every partition `ξ` with `ℓ(ξ) ≤ N`, and a strictly decreasing vector is determined by its multiset — that is the whole content of A4/A5. **Do not** prove `a_ρ = ∏(x_i - x_j)` or that `a_ρ` is a non-zero-divisor; A5 replaces both.

### Layer B — Stembridge's theorem, straight shapes only (~900–1200 lines; the largest single block)

| # | statement | deps | size |
|---|---|---|---|
| B1 | `def YoungDiagram.colTrunc (μ : YoungDiagram) (j : ℕ) : YoungDiagram := ⟨μ.cells.filter (·.2 < j), _⟩`; `rowLen_colTrunc : (μ.colTrunc j).rowLen i = min (μ.rowLen i) j` | — | trivial |
| B2 | `def cutRestrict (T : BoundedSemistandardTableau q μ) (j) : BoundedSemistandardTableau q (μ.colTrunc j)` and the gluing `def glue (T) (j) (S : Bdd q (μ.colTrunc j)) (hseam) : Bdd q μ` | B1 | moderate |
| B3 | `def colWeight (T : Bdd q μ) (j r : ℕ) : ℕ := (μ.cells.filter fun c => j ≤ c.2 ∧ T.tableau c.1 c.2 = r).card`; `colWeight_zero : colWeight T 0 r = T.tableau.weight r`; `colWeight_succ : colWeight T j r = colWeight T (j+1) r + (if column j of T contains r then 1 else 0)` | B1 | moderate |
| B4 | `def Good (μ : YoungDiagramOfSize a) (T : Bdd N ν.val) : Prop := ∀ j r, μ.val.rowLen (r+1) + colWeight T j (r+1) ≤ μ.val.rowLen r + colWeight T j r` | B3 | trivial |
| B5 | **Selection.** `¬ Good μ T → ∃ j k, (violation at (k,j)) ∧ (no violation at any j' > j) ∧ (k minimal)`. Existence of the maximal `j`: `colWeight T j r = 0` for `j > ν.rowLen 0`. | B3, B4 | moderate |
| B6 | **Structure at (k,j).** From maximality: `Δ(j+1) ≥ 0`; column-strictness gives `Δ(j) − Δ(j+1) ∈ {−1,0,1}`; hence `Δ(j) = −1`, **column `j` of `T` contains `k+1` and no `k`**, and `μ_k + colWeight T j k + 1 = μ_{k+1} + colWeight T j (k+1)`. | B5 | moderate |
| B7 | **Seam semistandardness.** Given "column `j` has no `k`", `glue T j (bk (cutRestrict T j) k)` is row-weak across the `j−1 | j` boundary. Two cases: a cell `k → k+1` at column `j−1` still has `T(i,j) ≥ k`, `≠ k`, hence `≥ k+1`; a cell `k+1 → k` only decreases. **Both sources compress this to one sentence; it is real work.** | B2, B6 | moderate |
| B8 | `def flip (T) (hbad) : Bdd N ν.val` and `flip_flip : flip (flip T) = T`, via: `(flip T)` agrees with `T` on columns `≥ j`, so B5 reselects the same `(k,j)`; then `bk_bk` (`SchurPolynomial.lean:39`). | B2,B5,B6,B7 | large |
| B9 | **Sign reversal.** `s_k` fixes `μ + colWeight T j (·) + ρ` in coordinates `k,k+1` (by B6 plus `ρ_k − ρ_{k+1} = 1`), hence `alt (μ + weight (flip T) + ρ) = - alt (μ + weight T + ρ)`. | A2, B6, B8, `weight_bk` | moderate |
| B10 | **Fixed points.** `flip T = T → alt (μ + weight T + ρ) = 0` (two equal coordinates → A3). *Stembridge omits this case entirely; it is only in Grinberg–Reiner footnote 149.* | A3, B8 | moderate |
| B11 | **THE THEOREM.** `alt (μ.rowLen + ρ) * schurPoly N ν.val = ∑ T ∈ {T // Good μ T}, alt (μ.rowLen + T.weight + ρ)`. Opening step: `alt α * schurPoly = ∑_w sgn w • x^{wα} · w(schurPoly) = ∑_T alt (α + weight T)` — **use Grinberg–Reiner's algebraic chain via `schurPoly_isSymmetric`, not Stembridge's "identically distributed" phrasing.** Then cancel the bad guys with B8/B9/B10. | A1-A3, B8-B10, `schurPoly_isSymmetric` | large |
| B12 | **Bi-alternant.** `alt (ν.rowLen + ρ) = alt ρ * schurPoly N ν.val`, i.e. B11 at `μ = ∅` plus: the only `Good ∅` tableau of shape `ν` is the superstandard one (row `i` filled with `i`). Proof of uniqueness: least `i` with a row-`i` entry `≠ i` forces `colWeight` to vanish at `i` but not above it. *Only in G-R footnote 145.* | B11 | moderate |
| B13 | **Product rule.** `schurPoly N μ.val * schurPoly N ν.val = ∑ ξ : YoungDiagramOfSize N, (stembridgeCount μ ν ξ : ℤ) • schurPoly N ξ.val`, where `stembridgeCount μ ν ξ := Nat.card {T : Bdd N ν.val // Good μ T ∧ ∀ r, μ.rowLen r + T.tableau.weight r = ξ.rowLen r}`. Route: B11 + B12 on both sides, then A5. | A5, B11, B12 | moderate |

### Layer C — the combinatorial bridge (~600–900 lines; **numerically verified below, and it decomposes**)

Define, for `U : LittlewoodRichardsonTableau μ ν ξ` and for `T : Bdd N ν.val`, the **row-content matrix**

```
M r i  :=  #{skew cells of U in row r with entry i}          (r : Fin N, i : Fin b)
M r i  :=  #{cells of T in row i of ν with entry r}
```

They are transposes of each other. I verified (see §6) over **378 871 matrices covering every `(μ,ν,ξ)` with `|ξ| ≤ 8`, zero failures**, that under this correspondence:

* `row_weak U` and `row_weak T` are **automatic** from the reconstruction;
* **`lattice U ⟺ col_strict T`, unconditionally**; and
* **given `col_strict T`: `col_strict U ⟺ Good μ T`**;
* hence the conjunctions match.

| # | statement | deps | size |
|---|---|---|---|
| C1 | `def rowContent` for both objects; reconstruction lemmas: a weakly-increasing filling of an interval of columns is determined by its content vector, so `U ↦ M` and `T ↦ M` are injective with a common explicit inverse. | — | large (mechanical) |
| C2 | **`lattice U ⟺ (R)`**: `lattice ↔ ∀ r i, #{c // c.1.1 < r ∧ entry c = i} ≥ #{c // c.1.1 ≤ r ∧ entry c = i+1}`. Proof: inside a row the `i`s lie strictly left of the `i+1`s (from `row_weak`), so the binding prefix ends at the leftmost `i+1` of a row, where the prefix holds every `i+1` of rows `≤ r` and no `i` of row `r`. **Do this first; it removes `readingLE` from every downstream goal.** | — | moderate |
| C3 | `(R)(U) ⟺ col_strict T` — after C1 both sides are literally `∑_{r'<r} M r' i ≥ ∑_{r'≤r} M r' (i+1)`. | C1, C2 | moderate |
| C4 | `col_strict U ⟺ (R_μ)(T)` where `(R_μ) : ∀ r i, μ_{r+1} + ∑_{i'≤i} M (r+1) i' ≤ μ_r + ∑_{i'<i} M r i'` — again literally the same inequality after C1. | C1 | moderate |
| C5 | **`(R_μ)(T) ⟺ Good μ T`** (row-cut ⟺ column-cut, μ-shifted). Needs two structure lemmas, each ~3 lines from `row_weak` + `col_strict`: **(S1)** for `u < v`, every value-`r` cell in row `v` is strictly left of every value-`r` cell in row `u`; **(S2)** if `(x,c)` holds `r+1` and some row `x'' < x` has an `r` at column `< c`, then `(x'',c)` holds `r`. Then the two directions run as in Grinberg–Reiner Exercise 2.9.18(b) `D_i ⇒ C_i` and `C_i ⇒ E_i ⇒ F_i ⇒ D_i`, with `μ_r` added to both sides throughout — the arguments are shift-robust (checked). **This is the hard half.** | C1, `col_strict T` | large |
| C6 | `stembridgeCount μ ν ξ = littlewoodRichardsonCoefficient μ ν ξ` (assemble C1–C5 into an `Equiv`, then `Nat.card_congr`). | C1-C5 | moderate |

### Layer D — the representation bridge (~800–1200 lines) — see §4

---

## 4. THE BRIDGE, concretely

### Step 1 — assembly (≈15 lines; land this FIRST so everyone else has a fixed interface)

Copy `Kostka.lean:167-172` verbatim, substituting the induced module for `youngPermutationModule weight`:

```lean
theorem spechtModule_littlewoodRichardson {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b) : Nonempty (...) := by
  obtain ⟨e⟩ := FDRep.exists_iso_biproduct_multiplicity spechtModule spechtModule_irreducible
    (fun α β h => (spechtModule_iso_iff_eq α β).mp h)
    (fun T hT => @exists_iso_spechtModule (a + b) T hT)
    ((SymmetricGroupRepresentation.youngSubgroupInduction a b).obj (spechtOuterTensor μ ν))
  exact ⟨e ≪≫ biproduct.mapIso fun ξ =>
    biproduct.reindex (finCongr (key μ ν ξ)) fun _ => spechtModule ξ⟩
```

leaving exactly one obligation
```lean
key : ∀ ξ, Module.finrank ℂ (spechtModule ξ ⟶
        (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj (spechtOuterTensor μ ν))
      = littlewoodRichardsonCoefficient μ ν ξ
```

### Step 2 — Frobenius flip (exactly how Pieri crossed the gap; `Pieri.lean:54-57`)

```lean
rw [FDRep.finrank_hom_symm, FDRep.indFunctor_obj,
    (FDRep.indResHomEquiv (SymmetricGroup.youngSubgroupInclusion a b)
      (spechtOuterTensor μ ν) (spechtModule ξ)).finrank_eq]
```
turning `key` into
```lean
Module.finrank ℂ (spechtOuterTensor μ ν ⟶
  (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion a b)).obj (spechtModule ξ))
    = littlewoodRichardsonCoefficient μ ν ξ
```
**`finrank_hom_symm` must come first** — `indResHomEquiv` maps *out of* the induced module. This is the point where Pieri then invoked `finrank_hom_outerTensor_res` (`TwoBoxInduction.lean:952`) and an eigenvalue argument; that shortcut is hard-wired to `b = 2` and a one-dimensional second factor and **does not generalise** — for general `b` the object is the `S_b`-module `Hom_{S_a}(S^μ, Res S^ξ)`, and decomposing it *is* the LR rule. So from here the route diverges from Pieri.

### Step 3 — two numeric identities and one inversion (no `ch` map, no virtual modules)

Write `c^ξ_{λρ} := finrank ℂ (spechtModule ξ ⟶ Ind (spechtOuterTensor λ ρ))`.

| # | statement | how | size |
|---|---|---|---|
| D1 | `kostkaNumber_eq_zero_of_not_dominates : ¬ λ.val.Dominates μ.val → kostkaNumber λ μ = 0` | column-strictness + zero-based entries put every entry `≤ k` in rows `0..k`; count with the `card_filter_cells` idiom (`Kostka.lean:78`, **private**) | moderate |
| D2 | `kostkaNumber_self : kostkaNumber λ λ = 1` | superstandard uniqueness; model on `WeightedSemistandardTableau.subsingleton` (`Kostka.lean:373`) | moderate |
| D3 | `YoungDiagram.Dominates.trans` / `.refl` | one line each from `YoungDiagrams.lean:54` | trivial |
| D4 | `exists_kostka_inverse : ∀ μ, ∃ z : YoungDiagramOfSize m → ℤ, ∀ λ, ∑ α, z α * kostkaNumber λ α = if λ = μ then 1 else 0` | well-founded recursion on strict dominance (`Finite.wellFounded_of_trans_of_irrefl`); `δ_μ = mult(M^μ) − Σ_{λ ⊳ μ} K_{λμ} δ_λ` | moderate |
| D5 | `FDRep.indOfMulActionIso` — generalise `indTrivialIso` (`YoungPermutation.lean:97`) from `Ind φ 1` to `Ind φ ℂ[Y]`: given `f : Y → X` equivariant along `φ`, a base point `y₀`, transitivity on both sides, and `∀ g, g • f y₀ = f y₀ ↔ ∃ k, k • y₀ = y₀ ∧ φ k = g`. Same `Representation.Coinvariants.lift` / `IndV.hom_ext` skeleton as `YoungPermutation.lean:14-72`. **This replaces transitivity of induction, general Young subgroups, and `Ind ⊠ Ind` all at once — do not build any of those.** | ≈100 lines | large |
| D6 | `α ∪ β` as `YoungDiagramOfSize (a+b)`: `Multiset` addition of `.parts` through `YoungDiagramOfSize.equivPartition` (`Partitions.lean:53`) — **no `List.mergeSort`**. Plus the merged base tabloid, modelled on the private `twoRowBaseTabloid`/`smul_twoRowBaseTabloid_eq_self_iff` (`YoungPermutation.lean:322/335`), using `mem_youngSubgroupInclusion_range_iff` (`YoungSubgroup.lean:34`) for the stabiliser. Yields `Ind_{S_a×S_b}(M^α ⊠ M^β) ≅ M^{α∪β}`. | D5 | large |
| D7 | Additivity: `mult` of a biproduct is the sum (from `FDRep.homFinrank_biproduct`, `Decomposition.lean:143`), and `Ind (⊕ V_i ⊠ ⊕ W_j)` splits. Cheapest route is on the **character** side: prove `FDRep.character_biproduct` (needs de-privatising `FDRep.biproductLinearEquivPi`, `Decomposition.lean:311`) and combine with `outerTensor_character` (`OuterTensor.lean:34`) and `scalar_product_char_eq_finrank_equivariant`, following `finrank_hom_outerTensor` (`OuterTensor.lean:85-103`). Avoid promoting `TensorProduct`-over-biproducts to an `Action` iso. | D6 | large |
| D8 | **(\*) rep side:** `∀ α β ξ, ∑_{λ,ρ} K_{λα}·K_{ρβ}·c^ξ_{λρ} = K_{ξ, α∪β}` | D6 + D7 + `finrank_hom_eq_kostkaNumber` (`Kostka.lean:144`) | moderate |
| D9 | **Pieri for polynomials** = B11 with `ν` a single row, i.e. `schurPoly N (row k) * schurPoly N λ = ∑_{ξ/λ horiz k-strip} schurPoly N ξ` | B11 | moderate |
| D10 | `∏_{i} schurPoly N (row (α.rowLen i)) = ∑_λ (kostkaNumber λ α : ℤ) • schurPoly N λ` — induction on the parts of `α`, peeling the **largest letter / smallest part** with `BoundedSemistandardTableau.fiberEquiv` (`SchurWeyl.lean:264`) and the summed form inline at `SchurWeyl.lean:307-369` | D9, fiberEquiv | large |
| D11 | **(\*\*) combinatorial side:** `∀ α β ξ, ∑_{λ,ρ} K_{λα}·K_{ρβ}·(stembridgeCount λ ρ ξ) = K_{ξ, α∪β}` — from B13, D10 and `Multiset.prod_add` (this is `h_α · h_β = h_{α∪β}`), then coefficient extraction against `{schurPoly}` (linearly independent by D1+D2 via `coeff_schurPoly`, `SchurPolynomial.lean:73`) | B13, D1, D2, D10 | moderate |
| D12 | Subtract (\*) − (\*\*), apply `exists_kostka_inverse` (D4) in each variable ⟹ `c^ξ_{μν} = stembridgeCount μ ν ξ`. Chain with C6 ⟹ `key`. | D4, D8, D11, C6 | moderate |

**Why the `ch` map and "virtual rewriting" are unnecessary:** the DAG (`lr.REP7`, `lr.REP10`, `lr.REP11`) routes through a Frobenius characteristic and a splitting of virtual modules. D8/D11/D12 replace all of that with two `ℕ`-valued identities and one triangular inversion. You never construct a linear map on a Grothendieck group.

**One bridge you must also record:** `kostkaNumber` counts `WeightedSemistandardTableau` (`Kostka.lean:20`) while `coeff_schurPoly` counts `BoundedSemistandardTableau` weights. A small `Equiv` between them (same SSYT, same content, `Fin n` vs `Fin q` bound) is needed and is not present.

---

## 5. CONVENTION HAZARDS

This is where a late failure comes from. Every item below was checked against the tree or the PDFs.

1. **Entry indexing.** Lean entries are **0-based** everywhere: `entry : … → Fin b` with `content i ↔ ν.rowLen i`, and mathlib's `SemistandardYoungTableau` entries are `ℕ` with `i ≤ T i j`. Stembridge and Sagan are **1-based** in rows, columns *and* entries. Off-by-one here silently changes nothing on small symmetric examples and everything on asymmetric ones — use the oracle in §6.
2. **Cell coordinates.** `(i,j) ∈ μ ↔ j < μ.rowLen i` (mathlib `mem_iff_lt_rowLen`), so `c.1` = **row**, `c.2` = **column**, both 0-based, English (rows go down). `μ.val ≤ ξ.val` is `SetLike` inclusion of `cells`.
3. **Reading word direction.** `LittlewoodRichardson.readingLE c d := c.1 < d.1 ∨ (c.1 = d.1 ∧ d.2 ≤ c.2)` — a **total** order, lexicographic by (row ascending, **column descending**) = top-to-bottom, right-to-left. `{c | readingLE c d}` is the prefix **including `d`**. This is exactly Sagan's *reverse* reading word `π_T^r` from Def 4.9.3 / Thm 4.9.4 (Sagan's `π_T` itself is bottom-row-first, left-to-right). **There is no mismatch with the cited source — do not "fix" it.** Stembridge never forms a word at all, which is why Layer C exists.
4. **`lattice` uses `Fin (b-1)` with ℕ-truncated subtraction.** For `b = 0` this is `Fin 0` and the field is vacuous; for `b ≥ 1`, `i` ranges over `0..b-2` and both `i` and `i+1` are `< b`. Safe, but any refactor that changes `b-1` to something else must preserve this.
5. **Alphabet size is `b = |ν|`, not `ℓ(ν)`.** Entries `i` with `ν.rowLen i = 0` are permitted by the type and forbidden by `content`. When transporting to Stembridge tableaux with entries in `Fin N`, `N = a+b`, the same slack appears on the other index. Keep `N` fixed at `a+b` for the *entire* argument — `ℓ(ξ) ≤ a+b` always, so no truncation is ever lost, and `μ`, `ν`, `ξ` all live in one ring.
6. **Which factor is stripped.** `youngSubgroupInduction a b` uses `SymmetricGroup.youngSubgroupInclusion a b` (`YoungSubgroup.lean:7`), so **`μ` sits on the first `Fin a` block**, `ν` on the second, and the LR tableau has skew shape `ξ/μ` filled with content `ν`. Consistent with Sagan.
7. **`c^ξ_{μν} = c^ξ_{νμ}` is NOT available** and has no short tableau-level proof. Numerically true (verified `|ξ| ≤ 7`). **Do not design a route that computes the ν-side count and appeals to symmetry.** The route in §3/§4 computes the μ-side throughout.
8. **`kostkaNumber shape weight` takes the SHAPE FIRST.** `YoungDiagram.Dominates μ ν` means **μ dominates ν**. `dominates_of_injective` (`Distinctness.lean:80`) returns `μ.val.Dominates ν.val` from a tableau of shape `μ` and a tabloid of shape `ν` — check the argument order and the `Fin`/`ℕ` coercion before reusing.
9. **Two different `weight`s now exist.** `SemistandardYoungTableau.weight : ℕ → ℕ` (`BenderKnuth.lean:394`) and `BoundedSemistandardTableau.weight : Fin q →₀ ℕ` (`SchurPolynomial.lean:20`). They are related by `weight_apply` (`:24`).
10. **`below` truncates by VALUE, not by column.** `SemistandardYoungTableau.below T q` (`SchurWeyl.lean:70`) keeps cells with entry `< q`. Stembridge's `T_{<j}` truncates by **column**. You must build B1/B2; do not reach for `below`.
11. **`ρ` orientation.** Stembridge's `ρ = (n−1, …, 1, 0)`. With 0-based `Fin N`, `ρ r = N − 1 − r`, so `ρ_k − ρ_{k+1} = 1` — that `+1` is exactly what makes the sign-reversal step B9 work. Getting `ρ` the other way round breaks B9 silently (the involution still exists, the signs don't cancel).
12. **Frobenius variance.** `indResHomEquiv : (ind φ V ⟶ W) ≃ (V ⟶ Res W)`. The goal after the assembly is `Hom(S^ξ, Ind …)`, the wrong way round; `FDRep.finrank_hom_symm` first, then `indFunctor_obj`, then `indResHomEquiv`. Exactly the order in `Pieri.lean:54-57`.
13. **`schurPoly q μ` takes a bare `YoungDiagram`**, not `YoungDiagramOfSize n`. Use `.val`.
14. **Grinberg–Reiner theorem numbers are version-specific.** Cite the version dated "July 27, 2020 (with minor corrections July 10, 2026)": Thm 2.6.6, Cor 2.6.7/2.6.9/2.6.11/2.6.12, Ex 2.9.18(b), Rmk 2.9.19, Thm 4.4.1(a). Cite by number, never by page. Neither Stembridge nor Grinberg–Reiner is listed in `refs/SOURCES.md` today.
15. **PDF extraction.** `pypdf` mangles the CM fonts in the Stembridge PDF (drops all Greek and subscripts). Use `pdfminer.six` and decode `(cid:21)=λ/≥, (cid:22)=μ, (cid:23)=ν, (cid:20)=≤, (cid:26)=ρ, (cid:27)=σ, (cid:1)=·, (cid:3)=∗, "2"=∈, "!"=→, "?"=∅`. `pdftotext`/`pdftoppm` are not installed.
16. **Degenerate cases.** `b = 0`: `Fin 0` empty, `lattice` vacuous, size forces `ξ = μ`, coefficient `1`. `a = 0`: coefficient is `[ξ = ν]`. `μ ⊄ ξ`: the `shape` field is a `Prop`, so the type is empty and the coefficient is `0`. Check all three early.

---

## 6. Test oracle

All numbers below were produced by direct enumeration of the **Lean structure's own fields** and cross-checked against Sagan's worked examples (`refs/`, PDF p.192). Scripts live in `/tmp/claude-1000/-home-blake-projects-SymmetricGroupRep/f209e0f7-8989-4256-8720-dbdc21cdf3ec/scratchpad/{lr.py,bridge.py,bridge2.py}`.

### 6.1 Coefficients (entries shown 0-based; `.` = a cell of μ)

| μ | ν | ξ | `c` | witnesses |
|---|---|---|---|---|
| (1) | (1) | (2) | 1 | `. 0` |
| (1) | (1) | (1,1) | 1 | `.` / `0` |
| (2,1) | (1) | (3,1) | 1 | `. . 0` / `.` |
| (2,1) | (1) | (2,2) | 1 | `. .` / `. 0` |
| (2,1) | (1) | (2,1,1) | 1 | `. .` / `.` / `0` |
| (2,1) | (1) | (4), (1,1,1,1) | 0 | — |
| (2) | (1,1) | (3,1) | 1 | `. . 0` / `1` |
| (2) | (1,1) | (2,1,1) | 1 | `. .` / `0` / `1` |
| (2) | (1,1) | (4), (2,2), (1,1,1,1) | 0 | — |
| **(2,1)** | **(2,1)** | **(3,2,1)** | **2** | `. . 0`/`. 0`/`1` **and** `. . 0`/`. 1`/`0` |
| (2,1) | (2,1) | (4,2),(4,1,1),(3,3),(3,1,1,1),(2,2,2),(2,2,1,1) | 1 each | — |
| (3,2,1) | (3,2) | (5,3,2,1) | 3 | Sagan's worked example |
| μ | ∅ | μ | 1 | empty filling |
| μ | ∅ | ξ ≠ μ | 0 | — |

`μ = ν = (2,1)`, `ξ = (3,2,1)` is the **unique smallest** case with multiplicity > 1 (`n = 6`).

### 6.2 Global invariants (all `|ξ| ≤ 7`, zero failures)

* `∑_ξ c^ξ_{μν} · f^ξ = C(a+b, a) · f^μ · f^ν` (with `f` from the hook formula) — catches any off-by-one in content or reading conventions immediately;
* `c^ξ_{μν} = c^ξ_{νμ}`;
* `ν = (b)` ⟹ `c = 1` iff `ξ/μ` is a horizontal `b`-strip; `ν = (1^b)` ⟹ `c = 1` iff vertical `b`-strip — so the frozen definition specialises correctly onto the already-proved `spechtModule_pieri_horizontal`/`_vertical`.

### 6.3 The Layer-C bridge, verified (new; this is my own check, not a scout's)

Enumerating **all** row-content matrices `M` with row sums `ξ_r − μ_r` and column sums `ν_i`, for **every** `(μ, ν, ξ)` with `|ξ| ≤ 8` — **378 871 matrices** — and building `U_M` (skew, shape `ξ/μ`) and `T_M` (straight, shape `ν`) from `M` and `Mᵀ`:

| checked | failures |
|---|---|
| `row_weak (T_M)` automatic | **0** |
| `row_weak (U_M)` automatic | **0** |
| `lattice (U_M) ⟺ col_strict (T_M)` (unconditional) | **0** |
| given `col_strict (T_M)`: `col_strict (U_M) ⟺ Good μ (T_M)` | **0** |
| `col_strict U ∧ lattice U ⟺ col_strict T ∧ Good μ T` | **0** |

Separately, `Nat.card (LittlewoodRichardsonTableau μ ν ξ)` equals the Stembridge good-tableau count, **as multisets of row-content matrices, not merely as counts**, for all `(μ,ν,ξ)` with `|ξ| ≤ 5` (265 triples, 0 mismatches).

**Worked instance for the involution** (Grinberg–Reiner Example 2.6.10, re-verified): `n = 6`, outer `(5,4,4)`, inner `(2,2)`, `ν = (1)`; `T` has row1 = `1 2 2` (cols 3-5), row2 = `2 3` (cols 3-4), row3 = `2 2 3 4` (cols 1-4). `cont(T|≥5) = (0,1,0,…)` ⟹ partition; `cont(T|≥4) = (0,2,1,1,0,0)` ⟹ not. So `j = 4`, `k = 1`; column 4 = `(2,3,4)` contains a 2 and **no 1**, as B6 predicts. BK on `{1,2}` over columns 1-3 turns row3's two free 2s into 1s: `T*` row3 = `1 1 3 4`. Check: `ν+cont(T)+ρ = (7,9,5,3,1,0)` and `ν+cont(T*)+ρ = (9,7,5,3,1,0)` — swapped in coordinates 1,2. Use this as your first `#eval`/`decide` sanity test for B6–B9.

---

## 7. Still unlocated — stated plainly

1. **The μ-shifted `(R_μ) ⟺ Good` equivalence (C5) has no written source.** Grinberg–Reiner Exercise 2.9.18(b) proves the **unshifted** `C ⟺ D ⟺ E ⟺ F` cycle; the shifted version is my own adaptation. I checked that both directions of the argument are shift-robust and verified the shifted statement exhaustively to `|ξ| ≤ 8`, but **no source proves it**. G-R's Exercise 2.9.20 generalises to a shifted `C(κ)…G(κ)`, but its solution is **not in the PDF** ("we leave the details to the reader / look them up in the LaTeX source"). Budget C5 as if it were unsourced, because it is.
2. **`D_i ⇒ C_i` is genuinely the hard direction** — 2.5 dense pages in G-R even unshifted. If C5 stalls, split it out to a dedicated worker; it is a finite statement about a single tableau, completely independent of Layers A/B/D, and it de-risks the frozen definition regardless of which route wins.
3. **No rigorous skew Bender–Knuth exists in either source** (G-R Prop 2.2.4 is picture-based for straight shapes; Rmk 2.3.3 asserts the skew case "is proven similarly"). This route does not need it — but if anyone proposes the `κ = ∅` variant, that gap is real.
4. **Transitivity of induction is absent from the repo AND mathlib.** Mathlib has `Rep.indResAdjunction` (`RepresentationTheory/Induced.lean:159`), `Action.resComp` (`CategoryTheory/Action/Basic.lean:343`) and `Adjunction.conjugateIsoEquiv` (`Adjunction/Mates.lean:416`; note `natIsoOfRightAdjointNatIso` is **deprecated since 2026-01-31**), from which it could be assembled and lifted through `FDRep.forget₂HomLinearEquiv`. D5 makes this unnecessary. Don't build it.
5. **No `FDRep.character_biproduct`, no additivity of `Ind` or `outerTensor` over biproducts** anywhere. D7 is genuinely from scratch. I did not check whether `FDRep.biproductLinearEquivPi` (`Decomposition.lean:311`, **private**) can be avoided.
6. **Private declarations that will need de-privatising or restating:** `twoRowBaseTabloid` / `smul_twoRowBaseTabloid_eq_self_iff` (`YoungPermutation.lean:322/335`), `YoungTableau.card_filter_cells` (`Kostka.lean:78`), `FDRep.biproductLinearEquivPi` (`Decomposition.lean:311`), `Representation.indTrivialToFinsupp`/`indTrivialMk_mul`/`indTrivialFinsuppEquiv` (`YoungPermutation.lean:16/46/55`), `YoungTableau.card_filter_row_lt_and_column_eq` / `card_filter_column_eq` (`Distinctness.lean:39/62`).
7. **Line numbers in `BenderKnuth.lean`, `SchurPolynomial.lean` and `TwoBoxInduction.lean` are unstable** — untracked and being edited live. `Pieri.lean` has an uncommitted diff. Re-`git status` and re-`lake env lean` on those three before starting.
8. **Stale ledgers.** `docs/axiom-elimination-status.md` still lists `youngsRule` and both Pieri targets as open and claims "20 of 27 converted"; `docs/proof-dag.json` has `baseline_commit 5f00453` (8 commits behind), lists 7 remaining axioms (the tree has 2), and its `asm.spechtModule_littlewoodRichardson` cluster still records a stale edge to `spechtModule_pieri_horizontal` (Pieri is now proved independently via Young's orthogonal form, and `LittlewoodRichardson.lean` already imports `Pieri`, so there is no circularity either way). Do not plan from either file.
9. **I did not type-check any proposed statement.** Layers A–D are unelaborated. Everything cited from the tree was read directly; everything proposed is not.
10. **Total size estimate: 2 500–3 500 lines** (A ≈250, B ≈900–1200, C ≈600–900, D ≈800–1200), comparable to the largest existing files in the package. If that budget is unacceptable, the honest report upward is that Stembridge shortens the *combinatorics* to about a third of the DAG's 44-node plan, but Layer D — connecting any polynomial identity to `youngSubgroupInduction` — is irreducible on every route examined.
