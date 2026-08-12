import SymmetricGroupRep.Bialternant
import SymmetricGroupRep.Kostka

/-! # Kostka numbers as Schur coefficients

A Schur polynomial in `n` variables collects the semistandard tableaux of its
shape by weight, so its coefficients are Kostka numbers.  Counting the same
tableaux by rows instead makes the Kostka matrix unitriangular for the dominance
order: a shape occurs once in its own weight, and not at all in a weight it fails
to dominate.
-/

open Finset

/-- The cells of a Young diagram in its first `j` rows number its first `j` row
lengths. -/
private theorem YoungDiagram.card_filter_row_lt (mu : YoungDiagram) (j : ℕ) :
    (mu.cells.filter fun cell => cell.1 < j).card = ∑ row ∈ Finset.range j, mu.rowLen row := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun cell : ℕ × ℕ => cell.1) (t := Finset.range j)
    fun cell hcell => Finset.mem_range.mpr (Finset.mem_filter.mp hcell).2]
  refine Finset.sum_congr rfl fun row hrow => ?_
  have himage : ((mu.cells.filter fun cell => cell.1 < j).filter fun cell => cell.1 = row) =
      (Finset.range (mu.rowLen row)).image (Prod.mk row) := by
    ext ⟨i, c⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, YoungDiagram.mem_cells,
      YoungDiagram.mem_iff_lt_rowLen, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hcell, -⟩, rfl⟩
      exact ⟨c, hcell, rfl, rfl⟩
    · rintro ⟨d, hd, rfl, rfl⟩
      exact ⟨⟨hd, Finset.mem_range.mp hrow⟩, rfl⟩
  rw [himage, Finset.card_image_of_injective _ fun a b hab => by simpa using hab,
    Finset.card_range]

namespace WeightedSemistandardTableau

variable {n : ℕ} {shape weight : YoungDiagramOfSize n}

/-- Bounding the entries by `n` and reading the entry counts as a weight
identifies the two descriptions of the Kostka index set. -/
def boundedEquiv (shape weight : YoungDiagramOfSize n) :
    WeightedSemistandardTableau shape weight ≃
      {T : BoundedSemistandardTableau n shape.val // T.weight = expo n weight.val.rowLen} where
  toFun T := ⟨⟨T.tableau, T.entry_lt⟩, Finsupp.ext T.content⟩
  invFun T :=
    { tableau := T.val.tableau
      entry_lt := T.val.entry_lt
      content := fun i => congrArg (fun d : Fin n →₀ ℕ => d i) T.property }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cells carrying an entry below `j` number the first `j` rows of the
weight. -/
private theorem card_filter_entry_lt (T : WeightedSemistandardTableau shape weight) (j : ℕ) :
    (shape.val.cells.filter fun cell => T.tableau cell.1 cell.2 < j).card =
      ∑ row ∈ Finset.range j, weight.val.rowLen row := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun cell : ℕ × ℕ => T.tableau cell.1 cell.2)
    (t := Finset.range j) fun cell hcell => Finset.mem_range.mpr (Finset.mem_filter.mp hcell).2]
  refine Finset.sum_congr rfl fun row hrow => ?_
  rcases lt_or_ge row n with hrn | hrn
  · have hiff : ∀ cell ∈ shape.val.cells,
        (T.tableau cell.1 cell.2 < j ∧ T.tableau cell.1 cell.2 = row) ↔
          T.tableau cell.1 cell.2 = row := by
      refine fun cell _ => ⟨fun hcell => hcell.2, fun hcell => ⟨?_, hcell⟩⟩
      rw [hcell]
      exact Finset.mem_range.mp hrow
    rw [Finset.filter_filter, ← T.content ⟨row, hrn⟩]
    exact congrArg Finset.card (Finset.filter_congr hiff)
  · rw [YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le weight) hrn,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun cell hcell hval => absurd (hval ▸ T.entry_lt cell
      (Finset.mem_filter.mp hcell).1) (by omega)

/-- Columns increase strictly from the row index up, so a cell with an entry
below `j` lies in one of the first `j` rows. -/
private theorem filter_entry_lt_subset (T : WeightedSemistandardTableau shape weight) (j : ℕ) :
    (shape.val.cells.filter fun cell => T.tableau cell.1 cell.2 < j) ⊆
      shape.val.cells.filter fun cell => cell.1 < j := by
  classical
  intro cell hcell
  rw [Finset.mem_filter] at hcell ⊢
  exact ⟨hcell.1, lt_of_le_of_lt (T.tableau.row_le_entry hcell.1) hcell.2⟩

/-- **The shape of a semistandard tableau dominates its weight.** -/
theorem dominates (T : WeightedSemistandardTableau shape weight) :
    shape.val.Dominates weight.val := fun j => by
  classical
  rw [← card_filter_entry_lt T j, ← YoungDiagram.card_filter_row_lt shape.val j]
  exact Finset.card_le_card (filter_entry_lt_subset T j)

/-- A tableau whose weight is its own shape carries the row index in every
cell. -/
theorem entry_eq_row (T : WeightedSemistandardTableau shape shape) {row column : ℕ}
    (hcell : (row, column) ∈ shape.val) : T.tableau row column = row := by
  classical
  have hset : ∀ j, (shape.val.cells.filter fun cell => T.tableau cell.1 cell.2 < j) =
      shape.val.cells.filter fun cell => cell.1 < j := fun j =>
    Finset.eq_of_subset_of_card_le (filter_entry_lt_subset T j)
      (le_of_eq (by rw [YoungDiagram.card_filter_row_lt, card_filter_entry_lt]))
  have hcells : (row, column) ∈ shape.val.cells := hcell
  have hlt : T.tableau row column < row + 1 := by
    have hmem : (row, column) ∈ shape.val.cells.filter fun cell => cell.1 < row + 1 :=
      Finset.mem_filter.mpr ⟨hcells, Nat.lt_succ_self row⟩
    rw [← hset (row + 1)] at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hge : ¬ T.tableau row column < row := fun hcon => by
    have hmem : (row, column) ∈ shape.val.cells.filter fun cell => T.tableau cell.1 cell.2 < row :=
      Finset.mem_filter.mpr ⟨hcells, hcon⟩
    rw [hset row] at hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (by omega)
  omega

/-- Two tableaux of a common shape whose weight is that shape agree. -/
theorem subsingleton_self (shape : YoungDiagramOfSize n) :
    Subsingleton (WeightedSemistandardTableau shape shape) := by
  refine ⟨fun T U => ?_⟩
  obtain ⟨Tt, Tlt, Tc⟩ := T
  obtain ⟨Ut, Ult, Uc⟩ := U
  congr 1
  refine SemistandardYoungTableau.ext fun row column => ?_
  by_cases hcell : (row, column) ∈ shape.val
  · rw [entry_eq_row ⟨Tt, Tlt, Tc⟩ hcell, entry_eq_row ⟨Ut, Ult, Uc⟩ hcell]
  · rw [Tt.zeros hcell, Ut.zeros hcell]

/-- The tableau carrying its row index in every cell has its shape for weight. -/
def highestWeight (shape : YoungDiagramOfSize n) : WeightedSemistandardTableau shape shape where
  tableau := SemistandardYoungTableau.highestWeight shape.val
  entry_lt := (Stembridge.superstandard n shape.val
    (YoungDiagramOfSize.colLen_zero_le shape)).entry_lt
  content := fun entry =>
    Stembridge.weight_superstandard (YoungDiagramOfSize.colLen_zero_le shape) entry

end WeightedSemistandardTableau

open scoped Classical in
/-- **The coefficients of a Schur polynomial are Kostka numbers.** -/
theorem coeff_schurPoly_eq_kostkaNumber {n : ℕ} (shape weight : YoungDiagramOfSize n) :
    (schurPoly n shape.val).coeff (expo n weight.val.rowLen) = kostkaNumber shape weight := by
  rw [coeff_schurPoly, kostkaNumber,
    Nat.card_congr (WeightedSemistandardTableau.boundedEquiv shape weight),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Kostka unitriangularity, the diagonal.**  A shape occurs once in its own
weight. -/
theorem kostkaNumber_self {n : ℕ} (shape : YoungDiagramOfSize n) :
    kostkaNumber shape shape = 1 := by
  rw [kostkaNumber, Nat.card_eq_one_iff_unique]
  exact ⟨WeightedSemistandardTableau.subsingleton_self shape,
    ⟨WeightedSemistandardTableau.highestWeight shape⟩⟩

/-- **Kostka unitriangularity, the vanishing.**  A shape does not occur in a
weight it fails to dominate. -/
theorem kostkaNumber_eq_zero_of_not_dominates {n : ℕ} {shape weight : YoungDiagramOfSize n}
    (h : ¬ shape.val.Dominates weight.val) : kostkaNumber shape weight = 0 := by
  haveI : IsEmpty (WeightedSemistandardTableau shape weight) := ⟨fun T => h T.dominates⟩
  exact Nat.card_of_isEmpty
