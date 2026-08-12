import SymmetricGroupRep.JucysMurphy
import SymmetricGroupRep.PaddedDiagrams
import SymmetricGroupRep.StandardTableaux

/-! # Contents, axial distances and adjacent swaps of standard tableaux

The content of a label is `column - row` of the cell carrying it, and the axial
distance from `i` to `i + 1` is the difference of their contents. Together with
the reading tableau, which fills the cells in reading order, these are the
combinatorial inputs of Young's orthogonal form.

Three facts are proved here. The axial distance is `1` when `i` and `i + 1`
share a row, `-1` when they share a column, and otherwise of absolute value at
least `2`; the adjacent swap is standard exactly in that last case; and a
standard tableau is determined by its sequence of contents.

See Armon and Halverson, *Transition Matrices between Young's Natural and
Seminormal Representations*, Section 3.1, equations (3.1)--(3.2).
-/

namespace YoungDiagram

/-- The position of a cell in reading order: rows from top to bottom, each row
from left to right. -/
def readingIndex (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (∑ r ∈ Finset.range c.1, μ.rowLen r) + c.2

/-- The cells in the first `m` rows are counted by the first `m` row lengths. -/
theorem sum_rowLen_range (μ : YoungDiagram) (m : ℕ) :
    ∑ r ∈ Finset.range m, μ.rowLen r = (μ.cells.filter fun c => c.1 < m).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range m)
    fun c hc => Finset.mem_range.mpr (Finset.mem_filter.mp hc).2]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [rowLen_eq_card, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun c _ => ?_
  simp only [Finset.mem_range] at hr
  exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

theorem readingIndex_lt_card {μ : YoungDiagram} {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    μ.readingIndex c < μ.card := by
  classical
  have hcol : c.2 < μ.rowLen c.1 := mem_iff_lt_rowLen.mp hc
  calc μ.readingIndex c < (∑ r ∈ Finset.range c.1, μ.rowLen r) + μ.rowLen c.1 := by
        exact Nat.add_lt_add_left hcol _
    _ = ∑ r ∈ Finset.range (c.1 + 1), μ.rowLen r := (Finset.sum_range_succ _ _).symm
    _ = (μ.cells.filter fun d => d.1 < c.1 + 1).card := μ.sum_rowLen_range _
    _ ≤ μ.card := Finset.card_le_card (Finset.filter_subset _ _)

/-- Reading order strictly increases the reading index. -/
theorem readingIndex_lt_readingIndex {μ : YoungDiagram} {c d : ℕ × ℕ} (hc : c ∈ μ.cells)
    (h : c.1 < d.1 ∨ (c.1 = d.1 ∧ c.2 < d.2)) : μ.readingIndex c < μ.readingIndex d := by
  rcases h with hrow | ⟨hrow, hcol⟩
  · have hcol : c.2 < μ.rowLen c.1 := mem_iff_lt_rowLen.mp hc
    calc μ.readingIndex c < ∑ r ∈ Finset.range (c.1 + 1), μ.rowLen r := by
          rw [Finset.sum_range_succ]
          exact Nat.add_lt_add_left hcol _
      _ ≤ ∑ r ∈ Finset.range d.1, μ.rowLen r :=
          Finset.sum_le_sum_of_subset fun x hx =>
            Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le hrow)
      _ ≤ μ.readingIndex d := Nat.le_add_right _ _
  · rw [readingIndex, readingIndex, hrow]
    exact Nat.add_lt_add_left hcol _

theorem readingIndex_injOn (μ : YoungDiagram) :
    Set.InjOn μ.readingIndex ↑μ.cells := by
  intro c hc d hd hcd
  by_contra hne
  rcases lt_trichotomy c.1 d.1 with hrow | hrow | hrow
  · exact absurd hcd (readingIndex_lt_readingIndex hc (Or.inl hrow)).ne
  · rcases lt_trichotomy c.2 d.2 with hcol | hcol | hcol
    · exact absurd hcd (readingIndex_lt_readingIndex hc (Or.inr ⟨hrow, hcol⟩)).ne
    · exact hne (Prod.ext hrow hcol)
    · exact absurd hcd (readingIndex_lt_readingIndex hd (Or.inr ⟨hrow.symm, hcol⟩)).ne'
  · exact absurd hcd (readingIndex_lt_readingIndex hd (Or.inl hrow)).ne'

end YoungDiagram

/-- Filling the cells of `μ` in reading order. -/
noncomputable def readingEntry {n : ℕ} (μ : YoungDiagramOfSize n) : ↥μ.val.cells ≃ Fin n :=
  Equiv.ofBijective
    (fun c => ⟨μ.val.readingIndex c.1,
      (YoungDiagram.readingIndex_lt_card c.2).trans_le μ.property.le⟩)
    (by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun c d hcd => ?_, ?_⟩
      · exact Subtype.ext (μ.val.readingIndex_injOn c.2 d.2 (congrArg Fin.val hcd))
      · simp [μ.property])

@[simp]
theorem readingEntry_val {n : ℕ} (μ : YoungDiagramOfSize n) (c : ↥μ.val.cells) :
    (readingEntry μ c : ℕ) = μ.val.readingIndex c.1 :=
  rfl

/-- The standard tableau that fills the cells of `μ` in reading order. -/
noncomputable def readingTableau {n : ℕ} (μ : YoungDiagramOfSize n) :
    StandardYoungTableau μ where
  entry := readingEntry μ
  row_strict := fun {c _} hrow hcol =>
    YoungDiagram.readingIndex_lt_readingIndex c.2 (Or.inr ⟨hrow, hcol⟩)
  col_strict := fun {c _} _ hrow =>
    YoungDiagram.readingIndex_lt_readingIndex c.2 (Or.inl hrow)

namespace StandardYoungTableau

/-- The cell occupied by an entry of a standard tableau. -/
def position {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) (i : Fin n) : ℕ × ℕ :=
  (T.entry.symm i).1

/-- The content of an entry: column minus row. -/
def content {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) (i : Fin n) : ℤ :=
  (T.position i).2 - (T.position i).1

theorem position_mem {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ)
    (i : Fin n) : T.position i ∈ μ.val.cells :=
  (T.entry.symm i).2

@[simp]
theorem position_entry {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ)
    (c : ↥μ.val.cells) : T.position (T.entry c) = c.1 := by
  rw [position, Equiv.symm_apply_apply]

theorem position_injective {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ) :
    Function.Injective T.position :=
  YoungTableau.row_column_injective T.entry

/-- The axial distance from `i` to `i + 1`. -/
def axialDistance {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) (i : Fin n) : ℤ :=
  T.content i.succ - T.content (Fin.castSucc i)

/-- Swap the adjacent labels `i` and `i + 1` in a tableau labeling. -/
def swappedEntry {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) (i : Fin n) : ↥μ.val.cells ≃ Fin (n + 1) :=
  T.entry.trans (Equiv.swap (Fin.castSucc i) i.succ)

/-- The adjacent label swap preserves standardness. -/
def IsAdjacentSwapStandard {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) (i : Fin n) : Prop :=
  (∀ {c d}, c.1.1 = d.1.1 → c.1.2 < d.1.2 →
      T.swappedEntry i c < T.swappedEntry i d) ∧
    ∀ {c d}, c.1.2 = d.1.2 → c.1.1 < d.1.1 →
      T.swappedEntry i c < T.swappedEntry i d

/-- Swap adjacent entries when the resulting tableau is standard. -/
def swapAdjacent {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) (i : Fin n)
    (h : T.IsAdjacentSwapStandard i) : StandardYoungTableau μ where
  entry := T.swappedEntry i
  row_strict := h.1
  col_strict := h.2

@[simp]
theorem swapAdjacent_entry {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) (i : Fin n)
    (h : T.IsAdjacentSwapStandard i) (c : ↥μ.val.cells) :
    (T.swapAdjacent i h).entry c = T.swappedEntry i c :=
  rfl

end StandardYoungTableau

namespace StandardYoungTableau

section AdjacentSwap

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau μ) (i : Fin n)

@[simp]
theorem entry_position {m : ℕ} {ν : YoungDiagramOfSize m} (U : StandardYoungTableau ν)
    (k : Fin m) : U.entry ⟨U.position k, U.position_mem k⟩ = k :=
  U.entry.apply_symm_apply k

/-- No label lies strictly between `i` and `i + 1`. -/
private theorem not_lt_and_lt_adjacent {z : Fin (n + 1)}
    (h₁ : Fin.castSucc i < z) (h₂ : z < i.succ) : False := by
  have hcast : (Fin.castSucc i : Fin (n + 1)).val = i.val := rfl
  have hsucc : (i.succ : Fin (n + 1)).val = i.val + 1 := rfl
  have h₁' : i.val < z.val := h₁
  have h₂' : z.val < i.val + 1 := h₂
  omega

/-- In a shared row the label `i` sits one column left of `i + 1`. -/
theorem position_succ_of_row_eq
    (hrow : (T.position (Fin.castSucc i)).1 = (T.position i.succ).1) :
    (T.position i.succ).2 = (T.position (Fin.castSucc i)).2 + 1 := by
  have hpmem : T.position (Fin.castSucc i) ∈ μ.val.cells := T.position_mem _
  have hqmem : T.position i.succ ∈ μ.val.cells := T.position_mem _
  have hpe : T.entry ⟨T.position (Fin.castSucc i), hpmem⟩ = Fin.castSucc i := T.entry_position _
  have hqe : T.entry ⟨T.position i.succ, hqmem⟩ = i.succ := T.entry_position _
  have hlt : (T.position (Fin.castSucc i)).2 < (T.position i.succ).2 := by
    rcases lt_trichotomy (T.position (Fin.castSucc i)).2 (T.position i.succ).2 with h | h | h
    · exact h
    · exact absurd (T.position_injective (Prod.ext hrow h)) (Fin.castSucc_lt_succ (i := i)).ne
    · have hstrict := T.row_strict (c := ⟨T.position i.succ, hqmem⟩)
        (d := ⟨T.position (Fin.castSucc i), hpmem⟩) hrow.symm h
      rw [hpe, hqe] at hstrict
      exact absurd hstrict (Fin.castSucc_lt_succ (i := i)).asymm
  by_contra hcontra
  have hgap : (T.position (Fin.castSucc i)).2 + 1 < (T.position i.succ).2 := by omega
  have hmid : ((T.position (Fin.castSucc i)).1, (T.position (Fin.castSucc i)).2 + 1) ∈ μ.val.cells :=
    μ.val.up_left_mem (le_of_eq hrow) hgap.le hqmem
  refine not_lt_and_lt_adjacent i (z := T.entry ⟨_, hmid⟩) ?_ ?_
  · have hstrict := T.row_strict (c := ⟨T.position (Fin.castSucc i), hpmem⟩) (d := ⟨_, hmid⟩)
      rfl (Nat.lt_succ_self _)
    rwa [hpe] at hstrict
  · have hstrict := T.row_strict (c := ⟨_, hmid⟩) (d := ⟨T.position i.succ, hqmem⟩) hrow hgap
    rwa [hqe] at hstrict

/-- In a shared column the label `i` sits one row above `i + 1`. -/
theorem position_succ_of_column_eq
    (hcol : (T.position (Fin.castSucc i)).2 = (T.position i.succ).2) :
    (T.position i.succ).1 = (T.position (Fin.castSucc i)).1 + 1 := by
  have hpmem : T.position (Fin.castSucc i) ∈ μ.val.cells := T.position_mem _
  have hqmem : T.position i.succ ∈ μ.val.cells := T.position_mem _
  have hpe : T.entry ⟨T.position (Fin.castSucc i), hpmem⟩ = Fin.castSucc i := T.entry_position _
  have hqe : T.entry ⟨T.position i.succ, hqmem⟩ = i.succ := T.entry_position _
  have hlt : (T.position (Fin.castSucc i)).1 < (T.position i.succ).1 := by
    rcases lt_trichotomy (T.position (Fin.castSucc i)).1 (T.position i.succ).1 with h | h | h
    · exact h
    · exact absurd (T.position_injective (Prod.ext h hcol)) (Fin.castSucc_lt_succ (i := i)).ne
    · have hstrict := T.col_strict (c := ⟨T.position i.succ, hqmem⟩)
        (d := ⟨T.position (Fin.castSucc i), hpmem⟩) hcol.symm h
      rw [hpe, hqe] at hstrict
      exact absurd hstrict (Fin.castSucc_lt_succ (i := i)).asymm
  by_contra hcontra
  have hgap : (T.position (Fin.castSucc i)).1 + 1 < (T.position i.succ).1 := by omega
  have hmid : ((T.position (Fin.castSucc i)).1 + 1, (T.position (Fin.castSucc i)).2) ∈ μ.val.cells :=
    μ.val.up_left_mem hgap.le (le_of_eq hcol) hqmem
  refine not_lt_and_lt_adjacent i (z := T.entry ⟨_, hmid⟩) ?_ ?_
  · have hstrict := T.col_strict (c := ⟨T.position (Fin.castSucc i), hpmem⟩) (d := ⟨_, hmid⟩)
      rfl (Nat.lt_succ_self _)
    rwa [hpe] at hstrict
  · have hstrict := T.col_strict (c := ⟨_, hmid⟩) (d := ⟨T.position i.succ, hqmem⟩) hcol hgap
    rwa [hqe] at hstrict

/-- Out of line and out of column, the label `i + 1` lies strictly left of `i`
when it lies strictly below. -/
theorem position_column_lt_of_row_lt
    (hrow : (T.position (Fin.castSucc i)).1 < (T.position i.succ).1)
    (hne : (T.position (Fin.castSucc i)).2 ≠ (T.position i.succ).2) :
    (T.position i.succ).2 < (T.position (Fin.castSucc i)).2 := by
  have hpmem : T.position (Fin.castSucc i) ∈ μ.val.cells := T.position_mem _
  have hqmem : T.position i.succ ∈ μ.val.cells := T.position_mem _
  have hpe : T.entry ⟨T.position (Fin.castSucc i), hpmem⟩ = Fin.castSucc i := T.entry_position _
  have hqe : T.entry ⟨T.position i.succ, hqmem⟩ = i.succ := T.entry_position _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have hmid : ((T.position i.succ).1, (T.position (Fin.castSucc i)).2) ∈ μ.val.cells :=
      μ.val.up_left_mem le_rfl hlt.le hqmem
    refine not_lt_and_lt_adjacent i (z := T.entry ⟨_, hmid⟩) ?_ ?_
    · have hstrict := T.col_strict (c := ⟨T.position (Fin.castSucc i), hpmem⟩) (d := ⟨_, hmid⟩)
        rfl hrow
      rwa [hpe] at hstrict
    · have hstrict := T.row_strict (c := ⟨_, hmid⟩) (d := ⟨T.position i.succ, hqmem⟩) rfl hlt
      rwa [hqe] at hstrict
  · exact hgt

/-- Out of line and out of column, the label `i + 1` lies strictly right of `i`
when it lies strictly above. -/
theorem position_column_gt_of_row_gt
    (hrow : (T.position i.succ).1 < (T.position (Fin.castSucc i)).1)
    (hne : (T.position (Fin.castSucc i)).2 ≠ (T.position i.succ).2) :
    (T.position (Fin.castSucc i)).2 < (T.position i.succ).2 := by
  have hpmem : T.position (Fin.castSucc i) ∈ μ.val.cells := T.position_mem _
  have hqmem : T.position i.succ ∈ μ.val.cells := T.position_mem _
  have hpe : T.entry ⟨T.position (Fin.castSucc i), hpmem⟩ = Fin.castSucc i := T.entry_position _
  have hqe : T.entry ⟨T.position i.succ, hqmem⟩ = i.succ := T.entry_position _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · exfalso
    have hmid : ((T.position (Fin.castSucc i)).1, (T.position i.succ).2) ∈ μ.val.cells :=
      μ.val.up_left_mem le_rfl hgt.le hpmem
    have hone : i.succ < T.entry ⟨_, hmid⟩ := by
      have hstrict := T.col_strict (c := ⟨T.position i.succ, hqmem⟩) (d := ⟨_, hmid⟩) rfl hrow
      rwa [hqe] at hstrict
    have htwo : T.entry ⟨_, hmid⟩ < Fin.castSucc i := by
      have hstrict := T.row_strict (c := ⟨_, hmid⟩)
        (d := ⟨T.position (Fin.castSucc i), hpmem⟩) rfl hgt
      rwa [hpe] at hstrict
    exact absurd (hone.trans htwo) (Fin.castSucc_lt_succ (i := i)).asymm

/-- The three cases of the axial distance. -/
theorem axialDistance_eq_one_of_row_eq
    (hrow : (T.position (Fin.castSucc i)).1 = (T.position i.succ).1) :
    T.axialDistance i = 1 := by
  have hcol := T.position_succ_of_row_eq i hrow
  simp only [axialDistance, content, hrow, hcol]
  push_cast
  ring

theorem axialDistance_eq_neg_one_of_column_eq
    (hcol : (T.position (Fin.castSucc i)).2 = (T.position i.succ).2) :
    T.axialDistance i = -1 := by
  have hrow := T.position_succ_of_column_eq i hcol
  simp only [axialDistance, content, hcol, hrow]
  push_cast
  ring

theorem two_le_natAbs_axialDistance
    (hrow : (T.position (Fin.castSucc i)).1 ≠ (T.position i.succ).1)
    (hcol : (T.position (Fin.castSucc i)).2 ≠ (T.position i.succ).2) :
    2 ≤ (T.axialDistance i).natAbs := by
  have hexpand : T.axialDistance i =
      (((T.position i.succ).2 : ℤ) - ((T.position i.succ).1 : ℤ)) -
        ((((T.position (Fin.castSucc i)).2 : ℤ)) - (((T.position (Fin.castSucc i)).1 : ℤ))) := rfl
  rcases lt_or_gt_of_ne hrow with h | h
  · have := T.position_column_lt_of_row_lt i h hcol
    omega
  · have := T.position_column_gt_of_row_gt i h hcol
    omega

/-- The adjacent swap is standard exactly when `i` and `i + 1` share neither a
row nor a column. -/
theorem isAdjacentSwapStandard_iff :
    T.IsAdjacentSwapStandard i ↔
      (T.position (Fin.castSucc i)).1 ≠ (T.position i.succ).1 ∧
        (T.position (Fin.castSucc i)).2 ≠ (T.position i.succ).2 := by
  have hpmem : T.position (Fin.castSucc i) ∈ μ.val.cells := T.position_mem _
  have hqmem : T.position i.succ ∈ μ.val.cells := T.position_mem _
  have hpe : T.entry ⟨T.position (Fin.castSucc i), hpmem⟩ = Fin.castSucc i := T.entry_position _
  have hqe : T.entry ⟨T.position i.succ, hqmem⟩ = i.succ := T.entry_position _
  have hswapped : ∀ c : ↥μ.val.cells,
      T.swappedEntry i c = Equiv.swap (Fin.castSucc i) i.succ (T.entry c) := fun _ => rfl
  constructor
  · intro hstd
    constructor
    · intro hrow
      have hcolgap := T.position_succ_of_row_eq i hrow
      have hlt := hstd.1 (c := ⟨T.position (Fin.castSucc i), hpmem⟩)
        (d := ⟨T.position i.succ, hqmem⟩) hrow
        (show (T.position (Fin.castSucc i)).2 < (T.position i.succ).2 by omega)
      rw [hswapped, hswapped, hpe, hqe, Equiv.swap_apply_left, Equiv.swap_apply_right] at hlt
      exact absurd hlt (Fin.castSucc_lt_succ (i := i)).asymm
    · intro hcol
      have hrowgap := T.position_succ_of_column_eq i hcol
      have hlt := hstd.2 (c := ⟨T.position (Fin.castSucc i), hpmem⟩)
        (d := ⟨T.position i.succ, hqmem⟩) hcol
        (show (T.position (Fin.castSucc i)).1 < (T.position i.succ).1 by omega)
      rw [hswapped, hswapped, hpe, hqe, Equiv.swap_apply_left, Equiv.swap_apply_right] at hlt
      exact absurd hlt (Fin.castSucc_lt_succ (i := i)).asymm
  · rintro ⟨hrow, hcol⟩
    have hpos : ∀ (c : ↥μ.val.cells) (k : Fin (n + 1)), T.entry c = k → c.1 = T.position k := by
      intro c k hck
      rw [position, ← hck, Equiv.symm_apply_apply]
    constructor
    · intro c d hcd hlt
      rw [hswapped, hswapped]
      refine SymmetricGroup.adjacentTransposition_lt i (T.row_strict hcd hlt) ?_
      rintro ⟨hc, hd⟩
      exact hrow ((congrArg Prod.fst (hpos c _ hc)).symm.trans
        (hcd.trans (congrArg Prod.fst (hpos d _ hd))))
    · intro c d hcd hlt
      rw [hswapped, hswapped]
      refine SymmetricGroup.adjacentTransposition_lt i (T.col_strict hcd hlt) ?_
      rintro ⟨hc, hd⟩
      exact hcol ((congrArg Prod.snd (hpos c _ hc)).symm.trans
        (hcd.trans (congrArg Prod.snd (hpos d _ hd))))

theorem axialDistance_ne_zero : T.axialDistance i ≠ 0 := by
  by_cases hrow : (T.position (Fin.castSucc i)).1 = (T.position i.succ).1
  · rw [T.axialDistance_eq_one_of_row_eq i hrow]
    norm_num
  · by_cases hcol : (T.position (Fin.castSucc i)).2 = (T.position i.succ).2
    · rw [T.axialDistance_eq_neg_one_of_column_eq i hcol]
      norm_num
    · intro hzero
      have htwo := T.two_le_natAbs_axialDistance i hrow hcol
      rw [hzero] at htwo
      norm_num at htwo

/-- The adjacent swap is standard exactly when the axial distance is at least
two in absolute value. -/
theorem isAdjacentSwapStandard_iff_two_le_natAbs :
    T.IsAdjacentSwapStandard i ↔ 2 ≤ (T.axialDistance i).natAbs := by
  rw [T.isAdjacentSwapStandard_iff i]
  constructor
  · rintro ⟨hrow, hcol⟩
    exact T.two_le_natAbs_axialDistance i hrow hcol
  · intro htwo
    refine ⟨fun hrow => ?_, fun hcol => ?_⟩
    · rw [T.axialDistance_eq_one_of_row_eq i hrow] at htwo
      norm_num at htwo
    · rw [T.axialDistance_eq_neg_one_of_column_eq i hcol] at htwo
      norm_num at htwo

/-- Swapping adjacent labels swaps their positions. -/
theorem position_swapAdjacent (h : T.IsAdjacentSwapStandard i) (k : Fin (n + 1)) :
    (T.swapAdjacent i h).position k = T.position (Equiv.swap (Fin.castSucc i) i.succ k) := by
  have hentry : (T.swapAdjacent i h).entry =
      T.entry.trans (Equiv.swap (Fin.castSucc i) i.succ) := rfl
  rw [position, position, hentry, Equiv.symm_trans_apply, Equiv.symm_swap]

theorem content_swapAdjacent (h : T.IsAdjacentSwapStandard i) (k : Fin (n + 1)) :
    (T.swapAdjacent i h).content k = T.content (Equiv.swap (Fin.castSucc i) i.succ k) := by
  rw [content, content, T.position_swapAdjacent i h k]

/-- Swapping the same adjacent pair a second time restores the original
entry labeling. -/
theorem swappedEntry_swapAdjacent {n : ℕ} {mu : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau mu) (i : Fin n)
    (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).swappedEntry i = T.entry := by
  apply Equiv.ext
  intro cell
  simp [swappedEntry, swapAdjacent]

/-- An admissible adjacent swap is admissible in the reverse direction. -/
theorem isAdjacentSwapStandard_swapAdjacent {n : ℕ}
    {mu : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau mu) (i : Fin n)
    (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).IsAdjacentSwapStandard i := by
  rw [IsAdjacentSwapStandard, swappedEntry_swapAdjacent]
  exact ⟨T.row_strict, T.col_strict⟩

/-- Swapping an admissible adjacent pair twice restores the tableau. -/
theorem swapAdjacent_swapAdjacent {n : ℕ}
    {mu : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau mu) (i : Fin n)
    (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).swapAdjacent i
        (T.isAdjacentSwapStandard_swapAdjacent i h) = T := by
  apply StandardYoungTableau.ext
  exact T.swappedEntry_swapAdjacent i h

theorem axialDistance_swapAdjacent (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).axialDistance i = -T.axialDistance i := by
  rw [axialDistance, axialDistance, T.content_swapAdjacent i h, T.content_swapAdjacent i h,
    Equiv.swap_apply_right, Equiv.swap_apply_left]
  ring

end AdjacentSwap

end StandardYoungTableau

namespace OneBoxRemoval

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}

/-- The content of the cell that a one-box removal deletes. -/
noncomputable def cellContent (ν : OneBoxRemoval μ) : ℤ :=
  YoungDiagram.cellContent (cell ν)

theorem position_extend_castSucc (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val)
    (k : Fin n) : (extend ν S).position (Fin.castSucc k) = S.position k := by
  have hmem : (S.entry.symm k).1 ∈ ν.val.val.cells := (S.entry.symm k).2
  have hentry : (extend ν S).entry ⟨(S.entry.symm k).1, cells_subset ν hmem⟩ =
      Fin.castSucc k := by
    rw [entry_extend_of_mem ν S _ hmem]
    congr 1
    exact S.entry.apply_symm_apply k
  rw [StandardYoungTableau.position, ← hentry, Equiv.symm_apply_apply,
    StandardYoungTableau.position]

theorem position_extend_last (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val) :
    (extend ν S).position (Fin.last n) = cell ν := by
  have hentry : (extend ν S).entry ⟨cell ν, cell_mem ν⟩ = Fin.last n :=
    entry_extend_cell ν S _ (cell_notMem ν)
  rw [StandardYoungTableau.position, ← hentry, Equiv.symm_apply_apply]

theorem content_extend_castSucc (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val)
    (k : Fin n) : (extend ν S).content (Fin.castSucc k) = S.content k := by
  rw [StandardYoungTableau.content, StandardYoungTableau.content, position_extend_castSucc]

theorem content_extend_last (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val) :
    (extend ν S).content (Fin.last n) = ν.cellContent := by
  rw [StandardYoungTableau.content, position_extend_last, cellContent, YoungDiagram.cellContent]

end OneBoxRemoval

namespace StandardYoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau μ)

theorem position_last : T.position (Fin.last n) = T.largestCell.1 := rfl

theorem position_restrictLargest (k : Fin n) :
    T.restrictLargest.position k = T.position (Fin.castSucc k) := by
  conv_rhs => rw [← OneBoxRemoval.extend_restrictLargest T]
  rw [OneBoxRemoval.position_extend_castSucc]
  rfl

theorem content_restrictLargest (k : Fin n) :
    T.restrictLargest.content k = T.content (Fin.castSucc k) := by
  rw [content, content, position_restrictLargest]

theorem content_last : T.content (Fin.last n) = T.largestRemoval.cellContent := by
  conv_lhs => rw [← OneBoxRemoval.extend_restrictLargest T]
  rw [OneBoxRemoval.content_extend_last]

/-- The cell of the largest label ends its row. -/
theorem rowLen_position_last :
    μ.val.rowLen (T.position (Fin.last n)).1 = (T.position (Fin.last n)).2 + 1 := by
  have hmem : T.position (Fin.last n) ∈ μ.val.cells := T.position_mem _
  have hlt : (T.position (Fin.last n)).2 < μ.val.rowLen (T.position (Fin.last n)).1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp hmem
  by_contra hne
  have hgap : (T.position (Fin.last n)).2 + 1 < μ.val.rowLen (T.position (Fin.last n)).1 := by
    omega
  have hnext : ((T.position (Fin.last n)).1, (T.position (Fin.last n)).2 + 1) ∈ μ.val.cells :=
    YoungDiagram.mem_iff_lt_rowLen.mpr hgap
  have hstrict := T.row_strict (c := ⟨T.position (Fin.last n), hmem⟩) (d := ⟨_, hnext⟩)
    rfl (Nat.lt_succ_self _)
  rw [T.entry_position] at hstrict
  exact absurd (Fin.le_last _) (not_le.mpr hstrict)

/-- The row below the cell of the largest label is shorter. -/
theorem rowLen_succ_position_last :
    μ.val.rowLen ((T.position (Fin.last n)).1 + 1) ≤ (T.position (Fin.last n)).2 := by
  have hmem : T.position (Fin.last n) ∈ μ.val.cells := T.position_mem _
  by_contra hne
  have hbelow : ((T.position (Fin.last n)).1 + 1, (T.position (Fin.last n)).2) ∈ μ.val.cells :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (not_le.mp hne)
  have hstrict := T.col_strict (c := ⟨T.position (Fin.last n), hmem⟩) (d := ⟨_, hbelow⟩)
    rfl (Nat.lt_succ_self _)
  rw [T.entry_position] at hstrict
  exact absurd (Fin.le_last _) (not_le.mpr hstrict)

end StandardYoungTableau

/-- The sum of the contents `column - row` over the cells of a diagram. -/
def contentSum {n : ℕ} (μ : YoungDiagramOfSize n) : ℤ :=
  ∑ c ∈ μ.val.cells, YoungDiagram.cellContent c

/-- Removing a box lowers the content sum by the content of that box. -/
theorem contentSum_sub_contentSum {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (ν : OneBoxRemoval μ) : contentSum μ - contentSum ν.val = ν.cellContent := by
  classical
  have hcells : μ.val.cells = insert (OneBoxRemoval.cell ν) ν.val.val.cells := by
    rw [OneBoxRemoval.cells_eq_erase ν, Finset.insert_erase (OneBoxRemoval.cell_mem ν)]
  rw [contentSum, contentSum, hcells, Finset.sum_insert (OneBoxRemoval.cell_notMem ν),
    OneBoxRemoval.cellContent]
  ring

/-- **A standard tableau is determined by its contents.** Induction on the size:
the content of the largest label picks out its corner, because distinct
removable corners of one diagram lie in different rows with strictly decreasing
column indices. -/
theorem StandardYoungTableau.position_eq_of_content_eq :
    ∀ (n : ℕ) (μ ν : YoungDiagramOfSize n) (T : StandardYoungTableau μ)
      (U : StandardYoungTableau ν), μ = ν → (∀ k, T.content k = U.content k) →
      ∀ k, T.position k = U.position k := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ _ k => k.elim0
  | succ n ih =>
    intro μ ν T U hshape hcontent k
    subst hshape
    have hlast : T.position (Fin.last n) = U.position (Fin.last n) := by
      have hcast := hcontent (Fin.last n)
      rw [content, content] at hcast
      have hTrow := T.rowLen_position_last
      have hTcol := T.rowLen_succ_position_last
      have hUrow := U.rowLen_position_last
      have hUcol := U.rowLen_succ_position_last
      rcases lt_trichotomy (T.position (Fin.last n)).1 (U.position (Fin.last n)).1 with h | h | h
      · have hanti := μ.val.rowLen_anti ((T.position (Fin.last n)).1 + 1)
          (U.position (Fin.last n)).1 h
        omega
      · exact Prod.ext h (by omega)
      · have hanti := μ.val.rowLen_anti ((U.position (Fin.last n)).1 + 1)
          (T.position (Fin.last n)).1 h
        omega
    refine Fin.lastCases hlast (fun j => ?_) k
    have hshapes : T.eraseLargestShape = U.eraseLargestShape :=
      Subtype.ext (YoungDiagram.ext (by
        show μ.val.cells.erase T.largestCell.1 = μ.val.cells.erase U.largestCell.1
        rw [show T.largestCell.1 = U.largestCell.1 from hlast]))
    have hrec := ih T.eraseLargestShape U.eraseLargestShape T.restrictLargest U.restrictLargest
      hshapes (fun j => by
        rw [T.content_restrictLargest, U.content_restrictLargest, hcontent]) j
    rwa [T.position_restrictLargest, U.position_restrictLargest] at hrec

theorem StandardYoungTableau.eq_of_content_eq {n : ℕ} {μ : YoungDiagramOfSize n}
    {T U : StandardYoungTableau μ} (h : ∀ k, T.content k = U.content k) : T = U := by
  have hpos := StandardYoungTableau.position_eq_of_content_eq n μ μ T U rfl h
  exact StandardYoungTableau.ext
    (Equiv.symm_bijective.injective (Equiv.ext fun k => Subtype.ext (hpos k)))

theorem StandardYoungTableau.content_injective {n : ℕ} (μ : YoungDiagramOfSize n) :
    Function.Injective (fun T : StandardYoungTableau μ => T.content) :=
  fun _ _ h => StandardYoungTableau.eq_of_content_eq (congrFun h)

section Extend

variable {m : ℕ} {μ : YoungDiagramOfSize (m + 2)}

/-- Including the labels commutes with an adjacent transposition. -/
private theorem castSucc_swap (a b x : Fin (m + 1)) :
    Fin.castSucc (Equiv.swap a b x) =
      Equiv.swap (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc x) := by
  rcases eq_or_ne x a with rfl | hxa
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · rcases eq_or_ne x b with rfl | hxb
    · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.swap_apply_of_ne_of_ne (fun h => hxa (Fin.castSucc_injective _ h))
          (fun h => hxb (Fin.castSucc_injective _ h))]

theorem OneBoxRemoval.axialDistance_extend (ν : OneBoxRemoval μ)
    (S : StandardYoungTableau ν.val) (j : Fin m) :
    (OneBoxRemoval.extend ν S).axialDistance (Fin.castSucc j) = S.axialDistance j := by
  rw [StandardYoungTableau.axialDistance, StandardYoungTableau.axialDistance,
    Fin.succ_castSucc, OneBoxRemoval.content_extend_castSucc,
    OneBoxRemoval.content_extend_castSucc]

theorem OneBoxRemoval.isAdjacentSwapStandard_extend (ν : OneBoxRemoval μ)
    (S : StandardYoungTableau ν.val) (j : Fin m) :
    (OneBoxRemoval.extend ν S).IsAdjacentSwapStandard (Fin.castSucc j) ↔
      S.IsAdjacentSwapStandard j := by
  rw [StandardYoungTableau.isAdjacentSwapStandard_iff,
    StandardYoungTableau.isAdjacentSwapStandard_iff, Fin.succ_castSucc,
    OneBoxRemoval.position_extend_castSucc, OneBoxRemoval.position_extend_castSucc]

theorem OneBoxRemoval.extend_swapAdjacent (ν : OneBoxRemoval μ)
    (S : StandardYoungTableau ν.val) (j : Fin m) (h : S.IsAdjacentSwapStandard j) :
    OneBoxRemoval.extend ν (S.swapAdjacent j h) =
      (OneBoxRemoval.extend ν S).swapAdjacent (Fin.castSucc j)
        ((OneBoxRemoval.isAdjacentSwapStandard_extend ν S j).mpr h) := by
  set hstd := (OneBoxRemoval.isAdjacentSwapStandard_extend ν S j).mpr h with hstddef
  refine StandardYoungTableau.ext (Equiv.ext fun d => ?_)
  have hright : ((OneBoxRemoval.extend ν S).swapAdjacent (Fin.castSucc j) hstd).entry d =
      Equiv.swap (Fin.castSucc (Fin.castSucc j)) (Fin.castSucc j.succ)
        ((OneBoxRemoval.extend ν S).entry d) := by
    rw [StandardYoungTableau.swapAdjacent_entry, StandardYoungTableau.swappedEntry,
      Fin.succ_castSucc]
    rfl
  rw [hright]
  by_cases hd : d.1 ∈ ν.val.val.cells
  · rw [OneBoxRemoval.entry_extend_of_mem _ _ d hd, OneBoxRemoval.entry_extend_of_mem _ _ d hd,
      StandardYoungTableau.swapAdjacent_entry, StandardYoungTableau.swappedEntry]
    exact castSucc_swap _ _ _
  · rw [OneBoxRemoval.entry_extend_cell _ _ d hd, OneBoxRemoval.entry_extend_cell _ _ d hd]
    exact (Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne'
      (Fin.castSucc_lt_last _).ne').symm

end Extend
