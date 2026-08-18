import SymmetricGroupRep.HookLength
import SymmetricGroupRep.SemistandardHom
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Combinatorics.Young.SemistandardTableau

open CategoryTheory CategoryTheory.Limits Finset

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # The symmetric-group side of Schur-Weyl duality

The multiplicity of `S^shape` in tensor space counts semistandard tableaux of
that shape with bounded entries, and the hook-content formula evaluates that
count. The proof of the formula is the Weyl dimension formula in the
first-column coordinates of `HookLength.lean`: truncating a tableau at `q`
splits it into a shape interlacing `shape` and a tableau on that shape, and the
resulting recursion in `q` is the interlacing sum of `Vandermonde.lean`.
-/

/-- A row of a Young diagram reaches at least `a` exactly when it contains its
first `a` cells. -/
theorem YoungDiagram.le_rowLen_iff {μ : YoungDiagram} {i a : ℕ} :
    a ≤ μ.rowLen i ↔ ∀ j < a, (i, j) ∈ μ := by
  refine ⟨fun h j hj => YoungDiagram.mem_iff_lt_rowLen.mpr (hj.trans_le h), fun h => ?_⟩
  by_contra hcon
  have := YoungDiagram.mem_iff_lt_rowLen.mp (h (μ.rowLen i) (by omega))
  omega

/-- Below its first column length, a Young diagram has no rows. -/
theorem YoungDiagram.rowLen_eq_zero {ν : YoungDiagram} {q i : ℕ} (hν : ν.colLen 0 ≤ q)
    (hi : q ≤ i) : ν.rowLen i = 0 := by
  by_contra hcon
  have hcell : (i, 0) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have := YoungDiagram.mem_iff_lt_colLen.mp hcell
  omega

/-- A Young diagram has no more rows than cells. -/
theorem YoungDiagram.colLen_zero_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.card := by
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A Young diagram of size `n` has at most `n` rows. -/
theorem YoungDiagramOfSize.colLen_zero_le {n : ℕ} (mu : YoungDiagramOfSize n) :
    mu.val.colLen 0 ≤ n := by
  have hcard := mu.val.colLen_zero_le_card
  rw [mu.property] at hcard
  exact hcard

/-- Every antitone vector of length `q` is the vector of row lengths of a Young
diagram with at most `q` rows. -/
theorem exists_youngDiagram_rowLen {q : ℕ} (r : Fin q → ℕ)
    (hr : ∀ i j : Fin q, i ≤ j → r j ≤ r i) :
    ∃ ν : YoungDiagram, ν.colLen 0 ≤ q ∧ ∀ i : Fin q, ν.rowLen i = r i := by
  have hsorted : (List.ofFn r).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_ofFn]
    exact fun i j hij => hr i j hij.le
  refine ⟨YoungDiagram.ofRowLens (List.ofFn r) hsorted, ?_, fun i => ?_⟩
  · by_contra hcon
    have hcell : ((q, 0) : ℕ × ℕ) ∈ YoungDiagram.ofRowLens (List.ofFn r) hsorted :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [YoungDiagram.mem_ofRowLens] at hcell
    obtain ⟨h, -⟩ := hcell
    simp at h
  · rw [YoungDiagram.rowLen_ofRowLens ⟨(i : ℕ), by simp⟩]
    simp

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- Column strictness makes the entry at a cell at least its row index. -/
theorem row_le_entry (T : SemistandardYoungTableau μ) {i j : ℕ} (hcell : (i, j) ∈ μ) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hprev : (i, j) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hcell
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hprev) (T.col_strict (Nat.lt_succ_self i) hcell))

/-- The cells of `μ` whose entry is below `q`. They form a Young diagram because
entries grow weakly to the right and downwards. -/
def below (T : SemistandardYoungTableau μ) (q : ℕ) : YoungDiagram where
  cells := μ.cells.filter fun c => T c.1 c.2 < q
  isLowerSet := by
    rintro ⟨i1, j1⟩ ⟨i2, j2⟩ hle hmem
    obtain ⟨hi, hj⟩ := hle
    simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at hmem ⊢
    refine ⟨μ.up_left_mem hi hj hmem.1, ?_⟩
    exact lt_of_le_of_lt ((T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hmem.1)).trans
      (T.col_weak hi hmem.1)) hmem.2

@[simp]
theorem mem_below {T : SemistandardYoungTableau μ} {q : ℕ} {c : ℕ × ℕ} :
    c ∈ T.below q ↔ c ∈ μ ∧ T c.1 c.2 < q := by
  simp [below, ← YoungDiagram.mem_cells]

theorem below_le (T : SemistandardYoungTableau μ) (q : ℕ) : T.below q ≤ μ :=
  fun _ hc => (mem_below.mp hc).1

theorem rowLen_below_le (T : SemistandardYoungTableau μ) (q i : ℕ) :
    (T.below q).rowLen i ≤ μ.rowLen i :=
  YoungDiagram.le_rowLen_iff.mpr fun _ hj =>
    T.below_le q (YoungDiagram.mem_iff_lt_rowLen.mpr hj)

/-- One row down, every entry has grown by at least one, so the cells below `q`
in row `i` reach at least as far as the cells of `μ` in row `i + 1`. -/
theorem rowLen_le_rowLen_below {T : SemistandardYoungTableau μ} {q : ℕ}
    (hT : ∀ c ∈ μ.cells, T c.1 c.2 < q + 1) (i : ℕ) :
    μ.rowLen (i + 1) ≤ (T.below q).rowLen i := by
  refine YoungDiagram.le_rowLen_iff.mpr fun j hj => ?_
  have hcell : (i + 1, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
  have hup : (i, j) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hcell
  refine mem_below.mpr ⟨hup, show T i j < q from ?_⟩
  have hstep : T i j < T (i + 1) j := T.col_strict (Nat.lt_succ_self i) hcell
  have hbound : T (i + 1) j < q + 1 := hT (i + 1, j) hcell
  omega

theorem colLen_below_le {T : SemistandardYoungTableau μ} {q : ℕ} : (T.below q).colLen 0 ≤ q := by
  by_contra hlt
  have hcell : (q, 0) ∈ T.below q :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  rw [mem_below] at hcell
  have hle : q ≤ T q 0 := T.row_le_entry hcell.1
  have hlt' : T q 0 < q := hcell.2
  omega

end SemistandardYoungTableau

/-- A semistandard tableau whose zero-based entries lie in `Fin q`. -/
structure BoundedSemistandardTableau (q : ℕ) (μ : YoungDiagram) where
  tableau : SemistandardYoungTableau μ
  entry_lt : ∀ cell ∈ μ.cells, tableau cell.1 cell.2 < q

namespace BoundedSemistandardTableau

variable {q : ℕ} {μ ν : YoungDiagram}

@[ext]
theorem ext {T U : BoundedSemistandardTableau q μ}
    (h : ∀ i j, T.tableau i j = U.tableau i j) : T = U := by
  cases T
  cases U
  congr 1
  exact SemistandardYoungTableau.ext h

/-- The entries of a bounded semistandard tableau, restricted to its cells. -/
def entries (T : BoundedSemistandardTableau q μ) : (cell : ↥μ.cells) → Fin q :=
  fun cell => ⟨T.tableau cell.1.1 cell.1.2, T.entry_lt cell.1 cell.2⟩

private theorem entries_injective :
    Function.Injective
      (entries : BoundedSemistandardTableau q μ → ((cell : ↥μ.cells) → Fin q)) := by
  intro T U hequal
  ext row column
  by_cases hcell : (row, column) ∈ μ.cells
  · exact congrArg Fin.val (congrFun hequal ⟨(row, column), hcell⟩)
  · rw [T.tableau.zeros (by simpa using hcell), U.tableau.zeros (by simpa using hcell)]

noncomputable instance : Fintype (BoundedSemistandardTableau q μ) :=
  Fintype.ofInjective entries entries_injective

/-- The part of a tableau bounded by `q + 1` that stays below `q`, read on the
diagram of those cells. -/
def restrict (T : BoundedSemistandardTableau (q + 1) μ) (hν : T.tableau.below q = ν) :
    BoundedSemistandardTableau q ν where
  tableau :=
    { entry := fun i j => if T.tableau i j < q then T.tableau i j else 0
      row_weak' := fun {i j1 j2} hj hcell => by
        rw [← hν, SemistandardYoungTableau.mem_below] at hcell
        have hrow := T.tableau.row_weak hj hcell.1
        rw [if_pos (lt_of_le_of_lt hrow hcell.2), if_pos hcell.2]
        exact hrow
      col_strict' := fun {i1 i2 j} hi hcell => by
        rw [← hν, SemistandardYoungTableau.mem_below] at hcell
        have hcol := T.tableau.col_strict hi hcell.1
        rw [if_pos (lt_trans hcol hcell.2), if_pos hcell.2]
        exact hcol
      zeros' := fun {i j} hcell => by
        rw [← hν, SemistandardYoungTableau.mem_below] at hcell
        by_cases hlt : T.tableau i j < q
        · rw [if_pos hlt, T.tableau.zeros fun hmem => hcell ⟨hmem, hlt⟩]
        · rw [if_neg hlt] }
  entry_lt := fun cell hcell => by
    obtain ⟨i, j⟩ := cell
    rw [← hν, YoungDiagram.mem_cells, SemistandardYoungTableau.mem_below] at hcell
    show (if T.tableau i j < q then T.tableau i j else 0) < q
    rw [if_pos hcell.2]
    exact hcell.2

/-- Filling every cell of `μ` outside `ν` with the value `q`. The cells outside
`ν` meet each column at most once, which is what keeps columns strict. -/
def extend (hνμ : ν ≤ μ) (hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i)
    (S : BoundedSemistandardTableau q ν) : BoundedSemistandardTableau (q + 1) μ where
  tableau :=
    { entry := fun i j => if (i, j) ∈ ν then S.tableau i j else if (i, j) ∈ μ then q else 0
      row_weak' := fun {i j1 j2} hj hcell => by
        by_cases hν2 : (i, j2) ∈ ν
        · rw [if_pos hν2, if_pos (ν.up_left_mem le_rfl hj.le hν2)]
          exact S.tableau.row_weak hj hν2
        · rw [if_neg hν2, if_pos hcell]
          by_cases hν1 : (i, j1) ∈ ν
          · exact le_of_lt (if_pos hν1 ▸ S.entry_lt (i, j1) hν1)
          · rw [if_neg hν1, if_pos (μ.up_left_mem le_rfl hj.le hcell)]
      col_strict' := fun {i1 i2 j} hi hcell => by
        have hν1 : (i1, j) ∈ ν :=
          YoungDiagram.mem_iff_lt_rowLen.mpr (lt_of_lt_of_le
            (YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem hi le_rfl hcell)) (hstrip i1))
        rw [if_pos hν1]
        by_cases hν2 : (i2, j) ∈ ν
        · rw [if_pos hν2]
          exact S.tableau.col_strict hi hν2
        · rw [if_neg hν2, if_pos hcell]
          exact S.entry_lt (i1, j) hν1
      zeros' := fun {i j} hcell => by
        rw [if_neg fun hmem => hcell (hνμ hmem), if_neg hcell] }
  entry_lt := fun cell hcell => by
    obtain ⟨i, j⟩ := cell
    show (if (i, j) ∈ ν then S.tableau i j else if (i, j) ∈ μ then q else 0) < q + 1
    by_cases hνc : (i, j) ∈ ν
    · rw [if_pos hνc]
      exact Nat.lt_succ_of_lt (S.entry_lt (i, j) hνc)
    · rw [if_neg hνc, if_pos (show (i, j) ∈ μ from hcell)]
      exact Nat.lt_succ_self q

theorem restrict_apply (T : BoundedSemistandardTableau (q + 1) μ) (hν : T.tableau.below q = ν)
    (i j : ℕ) :
    (restrict T hν).tableau i j = if T.tableau i j < q then T.tableau i j else 0 := rfl

theorem extend_apply (hνμ : ν ≤ μ) (hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i)
    (S : BoundedSemistandardTableau q ν) (i j : ℕ) :
    (extend hνμ hstrip S).tableau i j =
      if (i, j) ∈ ν then S.tableau i j else if (i, j) ∈ μ then q else 0 := rfl

theorem below_extend (hνμ : ν ≤ μ) (hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i)
    (S : BoundedSemistandardTableau q ν) : (extend hνμ hstrip S).tableau.below q = ν := by
  refine YoungDiagram.ext (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, SemistandardYoungTableau.mem_below,
    extend_apply]
  by_cases hν : (i, j) ∈ ν
  · simpa [hν] using ⟨hνμ hν, S.entry_lt (i, j) hν⟩
  · simp only [hν, if_false, iff_false, not_and]
    intro hμ
    rw [if_pos hμ]
    exact Nat.lt_irrefl q

theorem restrict_extend (hνμ : ν ≤ μ) (hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i)
    (S : BoundedSemistandardTableau q ν) :
    restrict (extend hνμ hstrip S) (below_extend hνμ hstrip S) = S := by
  ext i j
  rw [restrict_apply, extend_apply]
  by_cases hν : (i, j) ∈ ν
  · rw [if_pos hν, if_pos (S.entry_lt (i, j) hν)]
  · rw [if_neg hν, S.tableau.zeros hν]
    by_cases hμ : (i, j) ∈ μ <;> simp [hμ]

theorem extend_restrict (hνμ : ν ≤ μ) (hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i)
    (T : BoundedSemistandardTableau (q + 1) μ) (hν : T.tableau.below q = ν) :
    extend hνμ hstrip (restrict T hν) = T := by
  ext i j
  rw [extend_apply, restrict_apply]
  by_cases hν' : (i, j) ∈ ν
  · rw [← hν, SemistandardYoungTableau.mem_below] at hν'
    rw [if_pos (by rw [← hν, SemistandardYoungTableau.mem_below]; exact hν'), if_pos hν'.2]
  · rw [if_neg hν']
    rw [← hν, SemistandardYoungTableau.mem_below, not_and] at hν'
    by_cases hμ : (i, j) ∈ μ
    · rw [if_pos hμ]
      have hup : T.tableau i j < q + 1 := T.entry_lt (i, j) hμ
      have hdown : ¬ T.tableau i j < q := hν' hμ
      omega
    · rw [if_neg hμ, T.tableau.zeros hμ]

/-- The tableaux bounded by `q + 1` that truncate to `ν` are the tableaux
bounded by `q` of shape `ν`. -/
def fiberEquiv (hνμ : ν ≤ μ) (hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i) :
    {T : BoundedSemistandardTableau (q + 1) μ // T.tableau.below q = ν} ≃
      BoundedSemistandardTableau q ν where
  toFun T := restrict T.1 T.2
  invFun S := ⟨extend hνμ hstrip S, below_extend hνμ hstrip S⟩
  left_inv T := Subtype.ext (extend_restrict hνμ hstrip T.1 T.2)
  right_inv S := restrict_extend hνμ hstrip S

end BoundedSemistandardTableau

/-- The hook-content formula in first-column coordinates: the number of
semistandard tableaux of shape `μ` with entries below `q`, times the product of
the first `q` factorials, is the Vandermonde product of the first-column hook
lengths of `μ` read with `q` rows.

This is the Weyl dimension formula for `GL q` at the identity, proved by
induction on `q`: truncating a tableau at `q` splits it into a smaller shape
interlacing `μ` together with a tableau on that shape, and summing the resulting
Vandermonde products over the interlacing shapes is `factorial_mul_sum_vanderDec`.
The statement is Krattenthaler, *Another involution principle-free bijective
proof of Stanley's hook-content formula*, Electronic Journal of Combinatorics 6
(1999), Theorem 1, whose hypothesis `b ≥ r` is the hypothesis `μ.colLen 0 ≤ q`
here. -/
theorem card_boundedSemistandardTableau_mul_prod_factorial (q : ℕ) (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ q) :
    (Nat.card (BoundedSemistandardTableau q μ) : ℚ) * ∏ k ∈ range q, (k.factorial : ℚ) =
      vanderDec q fun i => (μ.firstColumnHook q i : ℚ) := by
  induction q generalizing μ with
  | zero =>
    have hempty : ∀ c : ℕ × ℕ, c ∉ μ := by
      rintro ⟨i, j⟩ hc
      have := YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hc)
      omega
    have hcard : Nat.card (BoundedSemistandardTableau 0 μ) = 1 := by
      refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun T U => ?_⟩, ⟨?_⟩⟩
      · ext i j
        rw [T.tableau.zeros (hempty (i, j)), U.tableau.zeros (hempty (i, j))]
      · exact ⟨SemistandardYoungTableau.highestWeight μ,
          fun cell hcell => absurd (show cell ∈ μ from hcell) (hempty cell)⟩
    rw [hcard]
    simp [vanderDec]
  | succ q ih =>
    classical
    set Box : Finset (Fin q → ℕ) :=
      Fintype.piFinset fun i : Fin q => Finset.Icc (μ.rowLen (i + 1)) (μ.rowLen i) with hBox
    set shape : BoundedSemistandardTableau (q + 1) μ → (Fin q → ℕ) :=
      fun T i => (T.tableau.below q).rowLen i with hshape
    have hmem : ∀ T ∈ (Finset.univ : Finset (BoundedSemistandardTableau (q + 1) μ)),
        shape T ∈ Box := by
      intro T _
      rw [hBox, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      exact ⟨SemistandardYoungTableau.rowLen_le_rowLen_below T.entry_lt i,
        T.tableau.rowLen_below_le q i⟩
    have hcount : Nat.card (BoundedSemistandardTableau (q + 1) μ) =
        ∑ r ∈ Box, Nat.card {T : BoundedSemistandardTableau (q + 1) μ // shape T = r} := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmem]
      exact Finset.sum_congr rfl fun r _ => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hterm : ∀ r ∈ Box,
        (Nat.card {T : BoundedSemistandardTableau (q + 1) μ // shape T = r} : ℚ) *
            ∏ k ∈ range q, (k.factorial : ℚ) =
          ∏ i : Fin q, ∏ j ∈ Finset.Ioi i,
            (((r i + (q - 1 - (i : ℕ)) : ℕ) : ℚ) - ((r j + (q - 1 - (j : ℕ)) : ℕ) : ℚ)) := by
      intro r hr
      rw [hBox, Fintype.mem_piFinset] at hr
      simp only [Finset.mem_Icc] at hr
      have hanti : ∀ i j : Fin q, i ≤ j → r j ≤ r i := by
        intro i j hij
        rcases eq_or_lt_of_le hij with rfl | hlt
        · exact le_rfl
        · exact ((hr j).2.trans (μ.rowLen_anti ((i : ℕ) + 1) j hlt)).trans (hr i).1
      obtain ⟨ν, hνcol, hνrow⟩ := exists_youngDiagram_rowLen r hanti
      have hνzero : ∀ i, q ≤ i → ν.rowLen i = 0 := fun i hi =>
        YoungDiagram.rowLen_eq_zero hνcol hi
      have hνμ : ν ≤ μ := by
        rintro ⟨i, j⟩ hc
        refine YoungDiagram.mem_iff_lt_rowLen.mpr
          (lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hc) ?_)
        by_cases hi : i < q
        · rw [hνrow ⟨i, hi⟩]
          exact (hr ⟨i, hi⟩).2
        · rw [hνzero i (by omega)]
          exact Nat.zero_le _
      have hstrip : ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i := by
        intro i
        by_cases hi : i < q
        · rw [hνrow ⟨i, hi⟩]
          exact (hr ⟨i, hi⟩).1
        · rw [YoungDiagram.rowLen_eq_zero hμ (by omega)]
          exact Nat.zero_le _
      have hfiber : ∀ T : BoundedSemistandardTableau (q + 1) μ,
          shape T = r ↔ T.tableau.below q = ν := by
        intro T
        refine ⟨fun h => YoungDiagram.ext_of_rowLen fun i => ?_, fun h => funext fun i => ?_⟩
        · by_cases hi : i < q
          · rw [hνrow ⟨i, hi⟩, ← congrFun h ⟨i, hi⟩]
          · rw [YoungDiagram.rowLen_eq_zero SemistandardYoungTableau.colLen_below_le (by omega),
              hνzero i (by omega)]
        · show (T.tableau.below q).rowLen (i : ℕ) = r i
          rw [h, hνrow i]
      have hcardfiber : Nat.card {T : BoundedSemistandardTableau (q + 1) μ // shape T = r} =
          Nat.card (BoundedSemistandardTableau q ν) :=
        Nat.card_congr ((Equiv.subtypeEquivRight hfiber).trans
          (BoundedSemistandardTableau.fiberEquiv hνμ hstrip))
      rw [hcardfiber, ih ν hνcol, vanderDec_eq_prod_fin]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      simp only [YoungDiagram.firstColumnHook, hνrow i, hνrow j]
    have hb : ∀ i < q, μ.firstColumnHook (q + 1) (i + 1) ≤ μ.firstColumnHook (q + 1) i := by
      intro i _
      have := μ.rowLen_anti i (i + 1) (by omega)
      simp only [YoungDiagram.firstColumnHook]
      omega
    have hreindex : ∑ r ∈ Box, (∏ i : Fin q, ∏ j ∈ Finset.Ioi i,
          (((r i + (q - 1 - (i : ℕ)) : ℕ) : ℚ) - ((r j + (q - 1 - (j : ℕ)) : ℕ) : ℚ))) =
        ∑ γ ∈ Fintype.piFinset fun i : Fin q =>
            Finset.Ico (μ.firstColumnHook (q + 1) (i + 1)) (μ.firstColumnHook (q + 1) i),
          ∏ i : Fin q, ∏ j ∈ Finset.Ioi i, ((γ i : ℚ) - (γ j : ℚ)) := by
      have hBoxmem : ∀ r : Fin q → ℕ, r ∈ Box ↔
          ∀ i : Fin q, μ.rowLen ((i : ℕ) + 1) ≤ r i ∧ r i ≤ μ.rowLen (i : ℕ) := by
        intro r
        rw [hBox, Fintype.mem_piFinset]
        exact forall_congr' fun _ => Finset.mem_Icc
      have hIcomem : ∀ γ : Fin q → ℕ,
          γ ∈ (Fintype.piFinset fun i : Fin q =>
              Finset.Ico (μ.firstColumnHook (q + 1) ((i : ℕ) + 1))
                (μ.firstColumnHook (q + 1) (i : ℕ))) ↔
            ∀ i : Fin q, μ.rowLen ((i : ℕ) + 1) + (q - 1 - (i : ℕ)) ≤ γ i ∧
              γ i < μ.rowLen (i : ℕ) + (q - (i : ℕ)) := by
        intro γ
        rw [Fintype.mem_piFinset]
        refine forall_congr' fun i => ?_
        rw [Finset.mem_Ico]
        simp only [YoungDiagram.firstColumnHook]
        have hi := i.isLt
        omega
      refine Finset.sum_nbij' (fun r i => r i + (q - 1 - (i : ℕ)))
        (fun γ i => γ i - (q - 1 - (i : ℕ))) ?_ ?_ ?_ ?_ (fun r _ => rfl)
      · intro r hrmem
        rw [hBoxmem] at hrmem
        rw [hIcomem]
        intro i
        have := hrmem i
        have hi := i.isLt
        omega
      · intro γ hγ
        rw [hIcomem] at hγ
        rw [hBoxmem]
        intro i
        have := hγ i
        have hi := i.isLt
        omega
      · intro r _
        funext i
        dsimp only
        omega
      · intro γ hγ
        rw [hIcomem] at hγ
        funext i
        have := hγ i
        have hi := i.isLt
        dsimp only
        omega
    rw [hcount, Nat.cast_sum, Finset.prod_range_succ, ← mul_assoc, Finset.sum_mul,
      Finset.sum_congr rfl hterm, hreindex,
      ← factorial_mul_sum_vanderDec (μ.firstColumnHook (q + 1)) hb]
    ring

/-- The Schur-Weyl multiplicity of `S^shape` in `(ℂ^q)^{⊗ n}`. -/
noncomputable def schurWeylMultiplicity {n : ℕ}
    (q : ℕ) (shape : YoungDiagramOfSize n) : ℕ :=
  Nat.card (BoundedSemistandardTableau q shape.val)

/-- Coordinate permutations act on words by precomposition with the inverse
permutation. -/
instance symmetricGroupWordAction (q n : ℕ) :
    MulAction (SymmetricGroup n) (Fin n → Fin q) :=
  arrowAction

/-- A word is the filling that gives each position its letter. -/
instance symmetricGroupWordFilling (q n : ℕ) : LabelFilling n (Fin n → Fin q) where
  finite := inferInstance
  entry w i := w i
  entry_injective _ _ h := funext fun i => Fin.ext (congrFun h i)
  entry_smul _ _ _ := rfl

/-- The permutation representation of `S_n` on words of length `n` over a
`q`-letter alphabet. This is the coordinate basis of `(ℂ^q)^{⊗ n}`. -/
noncomputable def tensorPowerPermutationRepresentation (q n : ℕ) :
    SymmetricGroupRepresentation n :=
  FDRep.of (Representation.ofMulAction ℂ (SymmetricGroup n) (Fin n → Fin q))

namespace YoungTableau

variable {n : ℕ} {shape : YoungDiagramOfSize n}

/-- Reading a word through a tableau `t` of shape `shape` matches the semistandard words with the
semistandard tableaux of that shape whose entries stay below `q`. -/
def semistandardWordEquiv (q : ℕ) (t : YoungTableau shape) :
    {w : Fin n → Fin q // Semistandard t w} ≃ BoundedSemistandardTableau q shape.val where
  toFun w :=
    { tableau := readTableau t w.2
      entry_lt := fun cell hcell => by
        show readEntry t w.val cell.1 cell.2 < q
        rw [readEntry_of_mem t w.val hcell]
        exact (w.val _).isLt }
  invFun T :=
    ⟨fun i => ⟨T.tableau (t.row i) (t.column i), T.entry_lt _ (t.mem_cells i)⟩,
      semistandard_of_entry_eq t fun _ => rfl⟩
  left_inv w := Subtype.ext (funext fun i => Fin.ext (readEntry_row_column t w.val i))
  right_inv T := BoundedSemistandardTableau.ext (readEntry_eq t fun _ => rfl)

/-- The multiplicity of `S^shape` in tensor space counts the semistandard tableaux of that shape
with entries below `q`.

This is Sagan's Theorem 2.10.1 applied to the set of words rather than to a set of tabloids: a
word is semistandard for `t` exactly when reading it through `t` gives a semistandard tableau,
and no step of that theorem asks the entries to be row indices.  Grouping the words by their
content recovers James, *The Representation Theory of the Symmetric Groups*, Theorem 14.1 for
composition weights, which is how the count is usually presented. -/
theorem finrank_hom_tensorPower (q : ℕ) (shape : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtModule shape ⟶ tensorPowerPermutationRepresentation q n) =
      schurWeylMultiplicity q shape := by
  obtain ⟨t⟩ := YoungTableau.nonempty shape
  exact (t.finrank_hom_eq_card_semistandard (Y := Fin n → Fin q)).trans
    (Nat.card_congr (t.semistandardWordEquiv q))

end YoungTableau

/-- Schur-Weyl duality, restricted to the symmetric-group action on tensor
space.

Magee, *Random Unitary Representations of Surface Groups I: Asymptotic
Expansions*, Proposition 2.4 on page 133, gives the full commuting
`U(q) × S_n` decomposition. The Gelfand--Tsetlin construction on page 134
indexes a basis of its `U(q)` factor by semistandard tableaux with entries in
`1, ..., q`. Shifting these entries down to `Fin q` and forgetting the `U(q)`
action gives the displayed multiplicity. When `q = 0`, `hn` makes both the word
basis and every bounded-tableau index set empty. The source is bundled as
`refs/magee-2022-random-unitary-representations.pdf`.

The proof here stays inside the symmetric group: `finrank_hom_tensorPower`
computes each multiplicity as a Hom-space dimension, and the isotypic
decomposition `FDRep.exists_iso_biproduct_multiplicity` assembles them.  No
`U(q)` action is built, and the argument is uniform in `n`: the hypothesis `hn`
is not needed, and is consumed only by naming `n` as a successor. -/
theorem tensorPower_schurWeyl (q n : ℕ) (hn : 0 < n) :
  Nonempty (tensorPowerPermutationRepresentation q n ≅
    ⨁ fun shape : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (schurWeylMultiplicity q shape) => spechtModule shape) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨e⟩ := FDRep.exists_iso_biproduct_multiplicity spechtModule spechtModule_irreducible
    (fun shape shape' h => (spechtModule_iso_iff_eq shape shape').mp h)
    (fun T hT => @exists_iso_spechtModule _ T hT)
    (tensorPowerPermutationRepresentation q (m + 1))
  exact ⟨e ≪≫ biproduct.mapIso fun shape =>
    biproduct.reindex (finCongr (YoungTableau.finrank_hom_tensorPower q shape))
      fun _ => spechtModule shape⟩

/-- The numerator in the hook-content formula, using zero-based cell
coordinates. -/
def YoungDiagram.schurContentProduct (q : ℕ) (μ : YoungDiagram) : ℤ :=
  μ.cells.prod fun cell => (q : ℤ) + cell.2 - cell.1

/-- With fewer than `μ.colLen 0` values available there is no way to fill the
first column, so there are no bounded tableaux at all. -/
theorem card_boundedSemistandardTableau_eq_zero {q : ℕ} {μ : YoungDiagram}
    (hq : q < μ.colLen 0) : Nat.card (BoundedSemistandardTableau q μ) = 0 := by
  refine Nat.card_eq_zero.mpr (Or.inl ⟨fun T => ?_⟩)
  have hcell : ((q, 0) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hq
  have hlow : q ≤ T.tableau q 0 := T.tableau.row_le_entry hcell
  have hhigh : T.tableau q 0 < q := T.entry_lt (q, 0) hcell
  omega

/-- The same hypothesis makes the content of the cell `(q, 0)` vanish. -/
theorem schurContentProduct_eq_zero {q : ℕ} {μ : YoungDiagram} (hq : q < μ.colLen 0) :
    μ.schurContentProduct q = 0 :=
  Finset.prod_eq_zero (i := (q, 0)) (YoungDiagram.mem_iff_lt_colLen.mpr hq) (by simp)

/-- Row `i` of the content product is a segment of consecutive integers ending
at the first-column hook length of that row. -/
theorem schurContentProduct_mul_prod_factorial {q : ℕ} {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ q) :
    μ.schurContentProduct q * ∏ i ∈ range q, ((q - 1 - i).factorial : ℤ) =
      ∏ i ∈ range q, ((μ.firstColumnHook q i).factorial : ℤ) := by
  have hsplit : μ.schurContentProduct q =
      ∏ i ∈ range q, ∏ j ∈ range (μ.rowLen i), ((q : ℤ) + j - i) := by
    rw [YoungDiagram.schurContentProduct, YoungDiagram.cells_eq_biUnion hμ,
      Finset.prod_biUnion (YoungDiagram.pairwiseDisjoint_rows μ)]
    exact Finset.prod_congr rfl fun i _ =>
      Finset.prod_image fun a _ b _ hab => (Prod.mk.injEq .. ▸ hab).2
  rw [hsplit, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  have hcast : ∀ j ∈ range (μ.rowLen i), (q : ℤ) + j - i = (((q - 1 - i) + 1 + j : ℕ) : ℤ) :=
    fun j _ => by omega
  rw [Finset.prod_congr rfl hcast, ← Nat.cast_prod, ← Nat.ascFactorial_eq_prod_range,
    ← Nat.cast_mul, Nat.mul_comm, Nat.factorial_mul_ascFactorial]
  congr 2
  simp only [YoungDiagram.firstColumnHook]
  omega

/-- The hook-content dimension formula in multiplicative form.

Krattenthaler, *Another involution principle-free bijective proof of Stanley's
hook-content formula*, Electronic Journal of Combinatorics 6 (1999), Article
R42, Theorem 1, states the formula for `q` at least the number of rows; that
case is `card_boundedSemistandardTableau_mul_prod_factorial` combined with the
first-column hook lemma `YoungDiagram.hookProduct_mul_vanderDec` and the content
lemma `schurContentProduct_mul_prod_factorial`. Krattenthaler's one-based
content `j - i` equals the zero-based `cell.2 - cell.1` used here. When `q` is
below the number of rows both sides vanish: there are no bounded tableaux, and
the cell `(q, 0)` contributes a zero content factor. The source is bundled as
`refs/krattenthaler-another-hook-content-arxiv-math9807068.pdf`. -/
theorem schurWeylMultiplicity_mul_hookProduct {n : ℕ}
    (q : ℕ) (shape : YoungDiagramOfSize n) :
  (schurWeylMultiplicity q shape : ℤ) * shape.val.hookProduct =
    shape.val.schurContentProduct q := by
  by_cases hq : q < shape.val.colLen 0
  · rw [schurWeylMultiplicity, card_boundedSemistandardTableau_eq_zero hq,
      schurContentProduct_eq_zero hq, Nat.cast_zero, zero_mul]
  · replace hq : shape.val.colLen 0 ≤ q := not_lt.mp hq
    have hP : (∏ k ∈ range q, (k.factorial : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast Nat.factorial_ne_zero k
    have hC := schurContentProduct_mul_prod_factorial hq
    rw [Finset.prod_range_reflect (fun k => (k.factorial : ℤ)) q] at hC
    have hCQ : (shape.val.schurContentProduct q : ℚ) * ∏ k ∈ range q, (k.factorial : ℚ) =
        ∏ i ∈ range q, ((shape.val.firstColumnHook q i).factorial : ℚ) := by
      exact_mod_cast hC
    have key : (Nat.card (BoundedSemistandardTableau q shape.val) : ℚ) *
        (shape.val.hookProduct : ℚ) = (shape.val.schurContentProduct q : ℚ) := by
      refine mul_right_cancel₀ hP ?_
      calc (Nat.card (BoundedSemistandardTableau q shape.val) : ℚ) *
              (shape.val.hookProduct : ℚ) * ∏ k ∈ range q, (k.factorial : ℚ)
          = (shape.val.hookProduct : ℚ) *
              ((Nat.card (BoundedSemistandardTableau q shape.val) : ℚ) *
                ∏ k ∈ range q, (k.factorial : ℚ)) := by ring
        _ = (shape.val.hookProduct : ℚ) *
              vanderDec q fun i => (shape.val.firstColumnHook q i : ℚ) := by
              rw [card_boundedSemistandardTableau_mul_prod_factorial q shape.val hq]
        _ = ∏ i ∈ range q, ((shape.val.firstColumnHook q i).factorial : ℚ) :=
              YoungDiagram.hookProduct_mul_vanderDec hq
        _ = (shape.val.schurContentProduct q : ℚ) * ∏ k ∈ range q, (k.factorial : ℚ) := hCQ.symm
    rw [schurWeylMultiplicity]
    exact_mod_cast key
