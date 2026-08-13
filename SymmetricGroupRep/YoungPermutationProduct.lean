import SymmetricGroupRep.Partitions
import SymmetricGroupRep.Tabloids

/-! # Combined weights

Inducing the outer tensor product of two Young permutation modules along the
standard Young-subgroup inclusion yields the Young permutation module whose
rows are the rows of both inputs.  This file provides that combined weight.
-/

namespace YoungDiagramOfSize

/-- The Young diagram of size `a + b` whose row lengths are the row lengths of
`α` together with the row lengths of `β`. -/
def combine {a b : ℕ} (α : YoungDiagramOfSize a) (β : YoungDiagramOfSize b) :
    YoungDiagramOfSize (a + b) :=
  Nat.Partition.toYoungDiagram
    { parts := α.partition.parts + β.partition.parts
      parts_pos := fun h => (Multiset.mem_add.mp h).elim
        α.partition.parts_pos β.partition.parts_pos
      parts_sum := by
        rw [Multiset.sum_add, α.partition.parts_sum, β.partition.parts_sum] }

/-- The rows of the combined diagram are the rows of the two inputs. -/
theorem rowLens_combine {a b : ℕ} (α : YoungDiagramOfSize a)
    (β : YoungDiagramOfSize b) :
    ((α.combine β).val.rowLens : Multiset ℕ) =
      ↑α.val.rowLens + ↑β.val.rowLens :=
  congrArg Nat.Partition.parts (Nat.Partition.partition_toYoungDiagram _)

/-- The combined diagram has one row for each row of the two inputs. -/
theorem length_rowLens_combine {a b : ℕ} (α : YoungDiagramOfSize a)
    (β : YoungDiagramOfSize b) :
    (α.combine β).val.rowLens.length =
      α.val.rowLens.length + β.val.rowLens.length := by
  simpa using congrArg Multiset.card (rowLens_combine α β)

end YoungDiagramOfSize
