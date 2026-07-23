import SymmetricGroupRep.YoungDiagrams

/-! # Padded Young diagrams

For a diagram `eta` of size at most `N`, the padded diagram has first row
`N - eta.card` followed by the rows of `eta`.
-/

namespace YoungDiagram

/-- The rows of `eta` fit below a first row of length `N - eta.card`. -/
def CanPad (N : ℕ) (eta : YoungDiagram) : Prop :=
  eta.card ≤ N ∧ eta.rowLen 0 ≤ N - eta.card

theorem rowLens_le_rowLen_zero (eta : YoungDiagram) {a : ℕ} (ha : a ∈ eta.rowLens) :
    a ≤ eta.rowLen 0 := by
  rw [rowLens, List.mem_map] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact eta.rowLen_anti 0 i (Nat.zero_le _)

/-- Add a sufficiently long first row to `eta`, yielding a diagram of size `N`. -/
def padded (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) : YoungDiagram :=
  YoungDiagram.ofRowLens ((N - eta.card) :: eta.rowLens) <|
    List.Pairwise.sortedGE <| (List.pairwise_cons.mpr ⟨fun a ha =>
      (eta.rowLens_le_rowLen_zero (a := a) ha).trans h.2, eta.rowLens_sorted.pairwise⟩)

theorem cellsOfRowLens_card (w : List ℕ) :
    (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
    · simp [ih]
    · rw [Finset.disjoint_left]
      rintro ⟨i, j⟩ hij hshift
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hij
      obtain ⟨rfl, hj⟩ := hij
      rw [Finset.mem_map] at hshift
      obtain ⟨⟨i, j⟩, -, hEq⟩ := hshift
      have hfst := congrArg Prod.fst hEq
      change Nat.succ i = 0 at hfst
      omega

theorem card_ofRowLens (w : List ℕ) (hw : w.SortedGE) :
    (YoungDiagram.ofRowLens w hw).card = w.sum :=
  cellsOfRowLens_card w

theorem card_eq_rowLens_sum (eta : YoungDiagram) : eta.card = eta.rowLens.sum := by
  calc
    eta.card = (YoungDiagram.ofRowLens eta.rowLens eta.rowLens_sorted).card :=
      congrArg YoungDiagram.card eta.ofRowLens_to_rowLens_eq_self.symm
    _ = eta.rowLens.sum := card_ofRowLens _ _

theorem padded_card (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (padded N eta h).card = N := by
  rw [padded, card_ofRowLens]
  change N - eta.card + eta.rowLens.sum = N
  rw [← eta.card_eq_rowLens_sum]
  exact Nat.sub_add_cancel h.1

theorem mem_padded_zero_iff (N j : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (0, j) ∈ padded N eta h ↔ j < N - eta.card := by
  rw [padded, YoungDiagram.mem_ofRowLens]
  simp

theorem mem_padded_succ_iff (N i j : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (i + 1, j) ∈ padded N eta h ↔ (i, j) ∈ eta := by
  rw [padded, YoungDiagram.mem_ofRowLens, YoungDiagram.mem_iff_lt_rowLen]
  simp only [List.length_cons, List.getElem_cons_succ]
  constructor
  · rintro ⟨hi, hj⟩
    simpa only [YoungDiagram.get_rowLens] using hj
  · intro hj
    have hmem : (i, j) ∈ eta := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    have hi : i < eta.rowLens.length := by
      rw [YoungDiagram.length_rowLens]
      exact (YoungDiagram.mem_iff_lt_colLen.mp hmem).trans_le
        (eta.colLen_anti 0 j (Nat.zero_le _))
    refine ⟨?_, ?_⟩
    · exact Nat.succ_lt_succ hi
    · simpa only [YoungDiagram.get_rowLens] using hj

/-- The zero-based content of a cell. -/
def cellContent (c : ℕ × ℕ) : ℤ := c.2 - c.1

theorem cellContent_zero (j : ℕ) : cellContent (0, j) = j := by
  simp [cellContent]

theorem cellContent_succ (i j : ℕ) :
    cellContent (i + 1, j) = cellContent (i, j) - 1 := by
  simp only [cellContent, Int.natCast_add, Int.natCast_one]
  omega

theorem cellContent_succ_sub_succ (i j k l : ℕ) :
    cellContent (i + 1, j) - cellContent (k + 1, l) =
      cellContent (i, j) - cellContent (k, l) := by
  rw [cellContent_succ, cellContent_succ]
  omega

theorem canPad_add (N k : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    CanPad (N + k) eta :=
  ⟨h.1.trans (Nat.le_add_right N k),
    h.2.trans (Nat.sub_le_sub_right (Nat.le_add_right N k) eta.card)⟩

theorem padded_le_add (N k : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    padded N eta h ≤ padded (N + k) eta (canPad_add N k eta h) := by
  rw [← YoungDiagram.cells_subset_iff]
  rintro ⟨i, j⟩ hcell
  cases i with
  | zero =>
    change (0, j) ∈ padded N eta h at hcell
    change (0, j) ∈ padded (N + k) eta (canPad_add N k eta h)
    rw [mem_padded_zero_iff] at hcell ⊢
    exact hcell.trans_le (Nat.sub_le_sub_right (Nat.le_add_right N k) eta.card)
  | succ i =>
    change (i + 1, j) ∈ padded N eta h at hcell
    change (i + 1, j) ∈ padded (N + k) eta (canPad_add N k eta h)
    simpa only [Nat.succ_eq_add_one, mem_padded_succ_iff] using hcell

/-- The padded diagram, packaged with its size. -/
def paddedOfSize (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) : YoungDiagramOfSize N :=
  ⟨padded N eta h, padded_card N eta h⟩

theorem padded_card_sdiff (N k : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    ((paddedOfSize (N + k) eta (canPad_add N k eta h)).val.cells \
      (paddedOfSize N eta h).val.cells).card = k := by
  simpa only [Nat.add_sub_cancel_left] using YoungDiagramOfSize.card_sdiff
    (paddedOfSize N eta h) (paddedOfSize (N + k) eta (canPad_add N k eta h))
    (padded_le_add N k eta h)

/-- Removing the final cell of the padded first row is a one-box removal. -/
theorem padded_isOneBoxRemoval (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    IsOneBoxRemoval (paddedOfSize N eta h)
      (paddedOfSize (N + 1) eta (canPad_add N 1 eta h)) :=
  padded_le_add N 1 eta h

theorem padded_one_removal_card_sdiff (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    ((paddedOfSize (N + 1) eta (canPad_add N 1 eta h)).val.cells \
      (paddedOfSize N eta h).val.cells).card = 1 := by
  simpa using padded_card_sdiff N 1 eta h

theorem padded_two_removal_card_sdiff (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    ((paddedOfSize (N + 2) eta (canPad_add N 2 eta h)).val.cells \
      (paddedOfSize N eta h).val.cells).card = 2 := by
  simpa using padded_card_sdiff N 2 eta h

theorem padded_three_removal_card_sdiff (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    ((paddedOfSize (N + 3) eta (canPad_add N 3 eta h)).val.cells \
      (paddedOfSize N eta h).val.cells).card = 3 := by
  simpa using padded_card_sdiff N 3 eta h

end YoungDiagram
