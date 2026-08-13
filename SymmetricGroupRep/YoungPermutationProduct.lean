import SymmetricGroupRep.OuterTensor
import SymmetricGroupRep.Partitions
import SymmetricGroupRep.Tabloids
import Mathlib.LinearAlgebra.DirectSum.Finsupp

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

/-- The concatenated rows of the inputs are a permutation of the combined rows. -/
theorem rowLens_append_perm_combine {a b : ℕ} (α : YoungDiagramOfSize a)
    (β : YoungDiagramOfSize b) :
    (α.val.rowLens ++ β.val.rowLens).Perm (α.combine β).val.rowLens :=
  Multiset.coe_eq_coe.mp (by rw [← Multiset.coe_add]; exact (rowLens_combine α β).symm)

/-- Rows of the two inputs matched with rows of the combined diagram. -/
noncomputable def combineRowEquiv {a b : ℕ} (α : YoungDiagramOfSize a)
    (β : YoungDiagramOfSize b) :
    Fin α.val.rowLens.length ⊕ Fin β.val.rowLens.length ≃
      Fin (α.combine β).val.rowLens.length :=
  (finSumFinEquiv.trans (finCongr List.length_append.symm)).trans
    { toFun := (rowLens_append_perm_combine α β).idxBij
      invFun := (rowLens_append_perm_combine α β).symm.idxBij
      left_inv := fun _ => List.Perm.idxBij_symm_idxBij _
      right_inv := fun _ => List.Perm.idxBij_idxBij_symm _ }

/-- A row inherited from the first input keeps its length. -/
theorem rowLen_combineRowEquiv_inl {a b : ℕ} (α : YoungDiagramOfSize a)
    (β : YoungDiagramOfSize b) (r : Fin α.val.rowLens.length) :
    (α.combine β).val.rowLen (combineRowEquiv α β (Sum.inl r)) =
      α.val.rowLen r := by
  have h := (rowLens_append_perm_combine α β).getElem_idxBij_eq_getElem
    (finCongr List.length_append.symm (finSumFinEquiv (Sum.inl r)))
  rw [YoungDiagram.get_rowLens] at h
  simp only [combineRowEquiv, Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [h]
  exact (List.getElem_append_left r.isLt).trans YoungDiagram.get_rowLens

/-- A row inherited from the second input keeps its length. -/
theorem rowLen_combineRowEquiv_inr {a b : ℕ} (α : YoungDiagramOfSize a)
    (β : YoungDiagramOfSize b) (r : Fin β.val.rowLens.length) :
    (α.combine β).val.rowLen (combineRowEquiv α β (Sum.inr r)) =
      β.val.rowLen r := by
  have h := (rowLens_append_perm_combine α β).getElem_idxBij_eq_getElem
    (finCongr List.length_append.symm (finSumFinEquiv (Sum.inr r)))
  rw [YoungDiagram.get_rowLens] at h
  simp only [combineRowEquiv, Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [h]
  exact (List.getElem_append_right (Nat.le_add_right _ _)).trans
    (by simp [YoungDiagram.get_rowLens])

end YoungDiagramOfSize

/-- The componentwise action of `S_a × S_b` on pairs of tabloids. -/
instance {a b : ℕ} {α : YoungDiagramOfSize a} {β : YoungDiagramOfSize b} :
    MulAction (SymmetricGroup a × SymmetricGroup b) (Tabloid α × Tabloid β) where
  smul p T := (p.1 • T.1, p.2 • T.2)
  one_smul T := Prod.ext (one_smul _ T.1) (one_smul _ T.2)
  mul_smul p q T := Prod.ext (mul_smul p.1 q.1 T.1) (mul_smul p.2 q.2 T.2)

@[simp]
theorem Tabloid.prod_smul_def {a b : ℕ} {α : YoungDiagramOfSize a}
    {β : YoungDiagramOfSize b} (p : SymmetricGroup a × SymmetricGroup b)
    (T : Tabloid α × Tabloid β) : p • T = (p.1 • T.1, p.2 • T.2) :=
  rfl

/-- The outer tensor product of two Young permutation modules is the
permutation module of the product tabloid action. -/
noncomputable def outerTensorYoungPermutationIso {a b : ℕ}
    (α : YoungDiagramOfSize a) (β : YoungDiagramOfSize b) :
    FDRep.outerTensor (youngPermutationModule α) (youngPermutationModule β) ≅
      FDRep.of (Representation.ofMulAction ℂ
        (SymmetricGroup a × SymmetricGroup b) (Tabloid α × Tabloid β)) := by
  let E : Representation.Equiv
      (Representation.tprod
        ((Representation.ofMulAction ℂ (SymmetricGroup a) (Tabloid α)).comp
          (MonoidHom.fst _ _))
        ((Representation.ofMulAction ℂ (SymmetricGroup b) (Tabloid β)).comp
          (MonoidHom.snd _ _)))
      (Representation.ofMulAction ℂ (SymmetricGroup a × SymmetricGroup b)
        (Tabloid α × Tabloid β)) :=
    Representation.Equiv.mk (finsuppTensorFinsupp' ℂ (Tabloid α) (Tabloid β))
      fun p => by
        obtain ⟨g, h⟩ := p
        apply TensorProduct.ext'
        intro x y
        ext ⟨A, B⟩
        simp [finsuppTensorFinsupp'_apply_apply, Representation.tprod_apply,
          Representation.ofMulAction_apply]
  exact Action.mkIso E.toLinearEquiv.toFGModuleCatIso fun p => by
    apply FGModuleCat.hom_ext
    exact E.toIntertwiningMap.2 p
