import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Powerset

/-! # Size-indexed Young diagrams and small skew shapes

This file supplies the finite indexing types used by the branching and two-box
Pieri rules.
-/

/-- A Young diagram with exactly `n` boxes. -/
abbrev YoungDiagramOfSize (n : ℕ) := { μ : YoungDiagram // μ.card = n }

private theorem YoungDiagram.cell_fst_lt_card
    (μ : YoungDiagram) {c : ℕ × ℕ} (hc : c ∈ μ.cells) : c.1 < μ.card := by
  exact (YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le <| by
    rw [YoungDiagram.colLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem YoungDiagram.cell_snd_lt_card
    (μ : YoungDiagram) {c : ℕ × ℕ} (hc : c ∈ μ.cells) : c.2 < μ.card := by
  exact (YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le <| by
    rw [YoungDiagram.rowLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)

/-- There are finitely many Young diagrams of any fixed size. -/
noncomputable instance (n : ℕ) : Finite (YoungDiagramOfSize n) := by
  let square : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n
  let cells : YoungDiagramOfSize n → ↥square.powerset := fun μ =>
    ⟨μ.val.cells, Finset.mem_powerset.mpr fun c hc => by
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by simpa [μ.property] using μ.val.cell_fst_lt_card hc,
        by simpa [μ.property] using μ.val.cell_snd_lt_card hc⟩⟩
  exact Finite.of_injective cells fun μ ν h => by
    apply Subtype.ext
    exact YoungDiagram.ext (congrArg Subtype.val h)

/-- A Young diagram is determined by its row lengths. -/
theorem YoungDiagram.ext_of_rowLen {μ ν : YoungDiagram}
    (h : ∀ row, μ.rowLen row = ν.rowLen row) : μ = ν := by
  apply YoungDiagram.ext
  ext ⟨row, column⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, h]

/-- `ν` is obtained from `μ` by removing one box.

Because their sizes are already `n` and `n + 1`, containment is enough to express this. -/
def IsOneBoxRemoval {n : ℕ}
    (ν : YoungDiagramOfSize n) (μ : YoungDiagramOfSize (n + 1)) : Prop :=
  ν.val ≤ μ.val

/-- A Young diagram obtained from `μ` by removing one box. -/
abbrev OneBoxRemoval {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :=
  { ν : YoungDiagramOfSize n // IsOneBoxRemoval ν μ }

/-- `ν` is obtained from `μ` by adding one box. -/
def IsOneBoxAddition {n : ℕ}
    (μ : YoungDiagramOfSize n) (ν : YoungDiagramOfSize (n + 1)) : Prop :=
  IsOneBoxRemoval μ ν

/-- A Young diagram obtained from `μ` by adding one box. -/
abbrev OneBoxAddition {n : ℕ} (μ : YoungDiagramOfSize n) :=
  { ν : YoungDiagramOfSize (n + 1) // IsOneBoxAddition μ ν }

/-- `ν / μ` is a horizontal two-strip: it consists of two boxes in distinct columns. -/
def IsHorizontalTwoStrip {n : ℕ}
  (μ : YoungDiagramOfSize n) (ν : YoungDiagramOfSize (n + 2)) : Prop :=
  μ.val ≤ ν.val ∧
    Set.InjOn Prod.snd (↑(ν.val.cells \ μ.val.cells) : Set (ℕ × ℕ))

/-- Young diagrams obtained from `μ` by adding a horizontal two-strip. -/
abbrev HorizontalTwoStrip {n : ℕ} (μ : YoungDiagramOfSize n) :=
  { ν : YoungDiagramOfSize (n + 2) // IsHorizontalTwoStrip μ ν }

/-- `ν / μ` is a vertical two-strip: it consists of two boxes in distinct rows. -/
def IsVerticalTwoStrip {n : ℕ}
  (μ : YoungDiagramOfSize n) (ν : YoungDiagramOfSize (n + 2)) : Prop :=
  μ.val ≤ ν.val ∧
    Set.InjOn Prod.fst (↑(ν.val.cells \ μ.val.cells) : Set (ℕ × ℕ))

/-- Young diagrams obtained from `μ` by adding a vertical two-strip. -/
abbrev VerticalTwoStrip {n : ℕ} (μ : YoungDiagramOfSize n) :=
  { ν : YoungDiagramOfSize (n + 2) // IsVerticalTwoStrip μ ν }

/-- The number of cells added between two nested size-indexed Young diagrams. -/
theorem YoungDiagramOfSize.card_sdiff {m n : ℕ}
    (μ : YoungDiagramOfSize m) (ν : YoungDiagramOfSize n) (h : μ.val ≤ ν.val) :
    (ν.val.cells \ μ.val.cells).card = n - m := by
  have hν : ν.val.cells.card = n := ν.property
  have hμ : μ.val.cells.card = m := μ.property
  rw [Finset.card_sdiff_of_subset (YoungDiagram.cells_subset_iff.mpr h), hν, hμ]

theorem IsOneBoxRemoval.card_sdiff {n : ℕ}
    {ν : YoungDiagramOfSize n} {μ : YoungDiagramOfSize (n + 1)}
    (h : IsOneBoxRemoval ν μ) :
    (μ.val.cells \ ν.val.cells).card = 1 := by
  simpa using YoungDiagramOfSize.card_sdiff ν μ h

theorem IsOneBoxAddition.card_sdiff {n : ℕ}
    {μ : YoungDiagramOfSize n} {ν : YoungDiagramOfSize (n + 1)}
    (h : IsOneBoxAddition μ ν) :
    (ν.val.cells \ μ.val.cells).card = 1 := by
  exact IsOneBoxRemoval.card_sdiff h

theorem IsHorizontalTwoStrip.card_sdiff {n : ℕ}
    {μ : YoungDiagramOfSize n} {ν : YoungDiagramOfSize (n + 2)}
    (h : IsHorizontalTwoStrip μ ν) :
    (ν.val.cells \ μ.val.cells).card = 2 := by
  simpa using YoungDiagramOfSize.card_sdiff μ ν h.1

theorem IsVerticalTwoStrip.card_sdiff {n : ℕ}
    {μ : YoungDiagramOfSize n} {ν : YoungDiagramOfSize (n + 2)}
    (h : IsVerticalTwoStrip μ ν) :
    (ν.val.cells \ μ.val.cells).card = 2 := by
  simpa using YoungDiagramOfSize.card_sdiff μ ν h.1
