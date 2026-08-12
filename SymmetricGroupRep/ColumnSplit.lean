import SymmetricGroupRep.Alternant

/-! # Splitting a tableau along a column

Cutting a Young diagram after column `j` splits a semistandard tableau into the
tableau on the first `j` columns and the entries in the columns from `j` on.  The
two pieces glue back together as soon as the entries of column `j - 1` do not
exceed those of column `j`.
-/

/-- The first `j` columns of a Young diagram. -/
def YoungDiagram.truncCols (μ : YoungDiagram) (j : ℕ) : YoungDiagram where
  cells := μ.cells.filter fun c => c.2 < j
  isLowerSet := by
    rintro ⟨i1, j1⟩ ⟨i2, j2⟩ hle hmem
    simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at *
    exact ⟨μ.up_left_mem hle.1 hle.2 hmem.1, lt_of_le_of_lt hle.2 hmem.2⟩

@[simp]
theorem YoungDiagram.mem_truncCols {μ : YoungDiagram} {j : ℕ} {c : ℕ × ℕ} :
    c ∈ μ.truncCols j ↔ c ∈ μ ∧ c.2 < j := by
  simp [YoungDiagram.truncCols, ← YoungDiagram.mem_cells]

theorem YoungDiagram.truncCols_le (μ : YoungDiagram) (j : ℕ) : μ.truncCols j ≤ μ :=
  fun _ hc => (YoungDiagram.mem_truncCols.mp hc).1

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The restriction of a tableau to its first `j` columns. -/
def restrictCols (T : SemistandardYoungTableau μ) (j : ℕ) :
    SemistandardYoungTableau (μ.truncCols j) where
  entry := fun r c => if c < j then T r c else 0
  row_weak' := fun {r c1 c2} hc hcell => by
    rw [YoungDiagram.mem_truncCols] at hcell
    rw [if_pos (by omega), if_pos hcell.2]
    exact T.row_weak hc hcell.1
  col_strict' := fun {r1 r2 c} hr hcell => by
    rw [YoungDiagram.mem_truncCols] at hcell
    rw [if_pos hcell.2, if_pos hcell.2]
    exact T.col_strict hr hcell.1
  zeros' := fun {r c} hcell => by
    rw [YoungDiagram.mem_truncCols, not_and_or] at hcell
    rcases hcell with hcell | hcell
    · rw [T.zeros hcell]
      exact ite_self 0
    · exact if_neg (by simpa using hcell)

@[simp]
theorem restrictCols_apply (T : SemistandardYoungTableau μ) (j r c : ℕ) :
    T.restrictCols j r c = if c < j then T r c else 0 := rfl

/-- Gluing a tableau on the first `j` columns to a tableau on the whole shape. -/
def glueCols {j : ℕ} (S : SemistandardYoungTableau (μ.truncCols j))
    (T : SemistandardYoungTableau μ)
    (hb : ∀ r c, c < j → (r, j) ∈ μ → S r c ≤ T r j) : SemistandardYoungTableau μ where
  entry := fun r c => if c < j then S r c else T r c
  row_weak' := fun {r c1 c2} hc hcell => by
    rcases lt_or_ge c2 j with hc2 | hc2
    · rw [if_pos (show c1 < j by omega), if_pos hc2]
      exact S.row_weak hc (YoungDiagram.mem_truncCols.mpr ⟨hcell, hc2⟩)
    · rw [if_neg (show ¬ c2 < j by omega)]
      rcases lt_or_ge c1 j with hc1 | hc1
      · rw [if_pos hc1]
        exact le_trans (hb r c1 hc1 (μ.up_left_mem le_rfl hc2 hcell))
          (T.row_weak_of_le hc2 hcell)
      · rw [if_neg (show ¬ c1 < j by omega)]
        exact T.row_weak hc hcell
  col_strict' := fun {r1 r2 c} hr hcell => by
    rcases lt_or_ge c j with hc | hc
    · rw [if_pos hc, if_pos hc]
      exact S.col_strict hr (YoungDiagram.mem_truncCols.mpr ⟨hcell, hc⟩)
    · rw [if_neg (show ¬ c < j by omega), if_neg (show ¬ c < j by omega)]
      exact T.col_strict hr hcell
  zeros' := fun {r c} hcell => by
    rcases lt_or_ge c j with hc | hc
    · rw [if_pos hc]
      exact S.zeros fun hmem => hcell (YoungDiagram.mem_truncCols.mp hmem).1
    · rw [if_neg (show ¬ c < j by omega)]
      exact T.zeros hcell

@[simp]
theorem glueCols_apply {j : ℕ} (S : SemistandardYoungTableau (μ.truncCols j))
    (T : SemistandardYoungTableau μ)
    (hb : ∀ r c, c < j → (r, j) ∈ μ → S r c ≤ T r j) (r c : ℕ) :
    glueCols S T hb r c = if c < j then S r c else T r c := rfl

/-- How often the entry `v` occurs in the columns from `j` on. -/
def colWeight (T : SemistandardYoungTableau μ) (j v : ℕ) : ℕ :=
  (μ.cells.filter fun c => j ≤ c.2 ∧ T c.1 c.2 = v).card

/-- How often the entry `v` occurs in column `j`. -/
def colCell (T : SemistandardYoungTableau μ) (j v : ℕ) : ℕ :=
  (μ.cells.filter fun c => c.2 = j ∧ T c.1 c.2 = v).card

theorem colWeight_zero (T : SemistandardYoungTableau μ) (v : ℕ) :
    T.colWeight 0 v = T.weight v := by
  simp [colWeight, weight]

theorem colWeight_succ (T : SemistandardYoungTableau μ) (j v : ℕ) :
    T.colWeight j v = T.colWeight (j + 1) v + T.colCell j v := by
  rw [colWeight, colWeight, colCell, ← Finset.card_union_of_disjoint]
  · congr 1
    ext c
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hc, hj, hv⟩
      rcases eq_or_lt_of_le hj with h | h
      · exact Or.inr ⟨hc, h.symm, hv⟩
      · exact Or.inl ⟨hc, by omega, hv⟩
    · rintro (⟨hc, hj, hv⟩ | ⟨hc, hj, hv⟩)
      · exact ⟨hc, by omega, hv⟩
      · exact ⟨hc, by omega, hv⟩
  · rw [Finset.disjoint_left]
    rintro c hc hc'
    simp only [Finset.mem_filter] at hc hc'
    omega

theorem colWeight_eq_zero (T : SemistandardYoungTableau μ) {j : ℕ} (hj : μ.rowLen 0 ≤ j)
    (v : ℕ) : T.colWeight j v = 0 := by
  rw [colWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨r, c⟩ hc
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc
  have := μ.rowLen_anti 0 r (Nat.zero_le r)
  simp only [not_and]
  omega

/-- Columns increase strictly, so a value occurs at most once in a column. -/
theorem colCell_le_one (T : SemistandardYoungTableau μ) (j v : ℕ) : T.colCell j v ≤ 1 := by
  rw [colCell, Finset.card_le_one]
  rintro ⟨r1, c1⟩ h1 ⟨r2, c2⟩ h2
  simp only [Finset.mem_filter, YoungDiagram.mem_cells] at h1 h2
  obtain ⟨hc1, rfl, hv1⟩ := h1
  obtain ⟨hc2, rfl, hv2⟩ := h2
  rcases lt_trichotomy r1 r2 with h | h | h
  · exact absurd (T.col_strict h hc2) (by omega)
  · rw [h]
  · exact absurd (T.col_strict h hc1) (by omega)

theorem colCell_eq_zero_iff (T : SemistandardYoungTableau μ) (j v : ℕ) :
    T.colCell j v = 0 ↔ ∀ r, (r, j) ∈ μ → T r j ≠ v := by
  rw [colCell, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h r hr hv
    exact (h (by simpa using hr)) ⟨rfl, hv⟩
  · rintro h ⟨r, c⟩ hc
    simp only [not_and]
    rintro rfl
    exact h r (by simpa using hc)

theorem colCell_eq_one_iff (T : SemistandardYoungTableau μ) (j v : ℕ) :
    T.colCell j v = 1 ↔ ∃ r, (r, j) ∈ μ ∧ T r j = v := by
  have hle := T.colCell_le_one j v
  constructor
  · intro h
    by_contra hcon
    rw [(T.colCell_eq_zero_iff j v).mpr fun r hr hv => hcon ⟨r, hr, hv⟩] at h
    omega
  · rintro ⟨r, hr, hv⟩
    have hne : T.colCell j v ≠ 0 := fun h => by
      rw [colCell_eq_zero_iff] at h
      exact h r hr hv
    omega

theorem weight_eq_restrictCols_add_colWeight (T : SemistandardYoungTableau μ) (j v : ℕ) :
    T.weight v = (T.restrictCols j).weight v + T.colWeight j v := by
  rw [weight, weight, colWeight, ← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨r, c⟩
    simp only [Finset.mem_union, Finset.mem_filter, YoungDiagram.mem_cells,
      YoungDiagram.mem_truncCols, restrictCols_apply]
    constructor
    · rintro ⟨hc, hv⟩
      rcases lt_or_ge c j with h | h
      · exact Or.inl ⟨⟨hc, h⟩, by rwa [if_pos h]⟩
      · exact Or.inr ⟨hc, h, hv⟩
    · rintro (⟨⟨hc, h⟩, hv⟩ | ⟨hc, h, hv⟩)
      · rw [if_pos h] at hv
        exact ⟨hc, hv⟩
      · exact ⟨hc, hv⟩
  · rw [Finset.disjoint_left]
    rintro ⟨r, c⟩ hc hc'
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_truncCols] at hc hc'
    omega

theorem weight_glueCols {j : ℕ} (S : SemistandardYoungTableau (μ.truncCols j))
    (T : SemistandardYoungTableau μ)
    (hb : ∀ r c, c < j → (r, j) ∈ μ → S r c ≤ T r j) (v : ℕ) :
    (glueCols S T hb).weight v = S.weight v + T.colWeight j v := by
  rw [weight, weight, colWeight, ← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨r, c⟩
    simp only [Finset.mem_union, Finset.mem_filter, YoungDiagram.mem_cells,
      YoungDiagram.mem_truncCols, glueCols_apply]
    constructor
    · rintro ⟨hc, hv⟩
      rcases lt_or_ge c j with h | h
      · rw [if_pos h] at hv
        exact Or.inl ⟨⟨hc, h⟩, hv⟩
      · rw [if_neg (by omega)] at hv
        exact Or.inr ⟨hc, h, hv⟩
    · rintro (⟨⟨hc, h⟩, hv⟩ | ⟨hc, h, hv⟩)
      · exact ⟨hc, by rwa [if_pos h]⟩
      · exact ⟨hc, by rwa [if_neg (by omega)]⟩
  · rw [Finset.disjoint_left]
    rintro ⟨r, c⟩ hc hc'
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_truncCols] at hc hc'
    omega

theorem colWeight_glueCols {j : ℕ} (S : SemistandardYoungTableau (μ.truncCols j))
    (T : SemistandardYoungTableau μ)
    (hb : ∀ r c, c < j → (r, j) ∈ μ → S r c ≤ T r j) {j' : ℕ} (hj : j ≤ j') (v : ℕ) :
    (glueCols S T hb).colWeight j' v = T.colWeight j' v := by
  rw [colWeight, colWeight]
  congr 1
  ext ⟨r, c⟩
  simp only [Finset.mem_filter, glueCols_apply]
  constructor
  · rintro ⟨hc, hj', hv⟩
    rw [if_neg (by omega)] at hv
    exact ⟨hc, hj', hv⟩
  · rintro ⟨hc, hj', hv⟩
    exact ⟨hc, hj', by rwa [if_neg (by omega)]⟩

theorem restrictCols_glueCols {j : ℕ} (S : SemistandardYoungTableau (μ.truncCols j))
    (T : SemistandardYoungTableau μ)
    (hb : ∀ r c, c < j → (r, j) ∈ μ → S r c ≤ T r j) :
    (glueCols S T hb).restrictCols j = S := by
  ext r c
  rw [restrictCols_apply, glueCols_apply]
  rcases lt_or_ge c j with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (show ¬ c < j by omega)]
    exact (S.zeros fun hmem => by rw [YoungDiagram.mem_truncCols] at hmem; omega).symm

theorem glueCols_apply_col {j : ℕ} (S : SemistandardYoungTableau (μ.truncCols j))
    (T : SemistandardYoungTableau μ)
    (hb : ∀ r c, c < j → (r, j) ∈ μ → S r c ≤ T r j) (r : ℕ) :
    glueCols S T hb r j = T r j := by
  rw [glueCols_apply, if_neg (by omega)]

end SemistandardYoungTableau
