import SymmetricGroupRep.BranchingBasis
import Mathlib.Analysis.RCLike.Sqrt

/-! # Young's orthogonal form -/

open scoped Classical

/-- The adjacent transposition exchanging `i` and `i + 1`. -/
def SymmetricGroup.adjacentTransposition {n : ℕ} (i : Fin n) :
    SymmetricGroup (n + 1) :=
  Equiv.swap (Fin.castSucc i) i.succ

@[simp]
theorem SymmetricGroup.adjacentTransposition_apply_left {n : ℕ} (i : Fin n) :
    SymmetricGroup.adjacentTransposition i (Fin.castSucc i) = i.succ :=
  Equiv.swap_apply_left _ _

@[simp]
theorem SymmetricGroup.adjacentTransposition_apply_right {n : ℕ} (i : Fin n) :
    SymmetricGroup.adjacentTransposition i i.succ = Fin.castSucc i :=
  Equiv.swap_apply_right _ _

@[simp]
theorem SymmetricGroup.adjacentTransposition_apply_of_ne {n : ℕ}
    (i : Fin n) (j : Fin (n + 1))
    (hleft : j ≠ Fin.castSucc i) (hright : j ≠ i.succ) :
    SymmetricGroup.adjacentTransposition i j = j :=
  Equiv.swap_apply_of_ne_of_ne hleft hright

namespace StandardYoungTableau

/-- The cell occupied by an entry of a standard tableau. -/
def position {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) (i : Fin n) : ℕ × ℕ :=
  (T.entry.symm i).1

/-- The content of an entry: column minus row. -/
def content {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) (i : Fin n) : ℤ :=
  (T.position i).2 - (T.position i).1

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

/-- The swapped orthogonal-basis vector, interpreted as zero when the adjacent
swap is not standard. -/
noncomputable def swappedOrthogonalBasisVector {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    spechtModule μ :=
  if h : T.IsAdjacentSwapStandard i then
    spechtOrthogonalBasis μ (T.swapAdjacent i h)
  else
    0

/-- Young's orthogonal action formula for an adjacent transposition.

Armon and Halverson, *Transition Matrices between Young's Natural and
Seminormal Representations*, EJC 28(3) (2021), Section 3.1, equations
(3.1)--(3.2), defines content and axial distance, and Section 3.3, equation
(3.4) (DOI `10.37236/10081`), gives this orthogonal action. The convention was
cross-checked against Geetha and Prasad, *Comparison of Gelfand--Tsetlin Bases
for Alternating and Symmetric Groups*, Section 2, equation (2)
(arXiv:1606.04424). Lean index `i` swaps zero-based labels `i,i+1`, which
correspond to classical labels `i+1,i+2` and the generator `s_(i+1)`. -/
axiom spechtOrthogonalBasis_adjacentTransposition {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
        (spechtOrthogonalBasis μ T) =
      ((T.axialDistance i : ℂ)⁻¹) • spechtOrthogonalBasis μ T +
        Complex.sqrt (1 - ((T.axialDistance i : ℂ)⁻¹) ^ 2) •
          swappedOrthogonalBasisVector μ T i
