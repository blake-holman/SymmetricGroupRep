import SymmetricGroupRep.Tableaux
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Hook lengths and the hook-length formula -/

namespace YoungDiagram

/-- The hook length of a cell: one plus the number of cells strictly to its
right in the same row and strictly below it in the same column. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (μ.rowLen c.1 - (c.2 + 1)) + (μ.colLen c.2 - (c.1 + 1)) + 1

/-- The product of the hook lengths of all cells of a Young diagram. -/
def hookProduct (μ : YoungDiagram) : ℕ :=
  μ.cells.prod μ.hookLength

/-- Every hook length is positive. -/
theorem hookLength_pos (μ : YoungDiagram) (c : ℕ × ℕ) :
    0 < μ.hookLength c := by
  simp [hookLength]

/-- The hook product is positive, including for the empty diagram. -/
theorem hookProduct_pos (μ : YoungDiagram) : 0 < μ.hookProduct := by
  exact Finset.prod_pos fun c _ => μ.hookLength_pos c

end YoungDiagram

/-- Multiplicative hook-length formula: `f^μ` times the hook product is `n!`.

The hook convention is Sagan, *The Symmetric Group*, 2nd ed., Definition 3.10.1
(DOI `10.1007/978-1-4757-6804-6_3`), cross-checked against Frame, Robinson, and
Thrall, *The Hook Graphs of the Symmetric Group*, Canadian Journal of
Mathematics 6 (1954), Section 1, equation (1.1) (DOI
`10.4153/CJM-1954-030-1`). The formula is Sagan, Theorem 3.10.2, and
Frame--Robinson--Thrall, Theorem 1. The multiplicative form avoids truncated
natural-number division. -/
axiom standardYoungTableau_card_mul_hookProduct {n : ℕ}
    (μ : YoungDiagramOfSize n) :
  Nat.card (StandardYoungTableau μ) * μ.val.hookProduct = n.factorial
