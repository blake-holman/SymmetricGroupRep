import SymmetricGroupRep.Induction
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

namespace Representation

variable {G H Y X : Type} [Group G] [Group H] [MulAction G Y] [MulAction H X]

/-- The map out of the induced permutation representation sending the generator
indexed by `h` at the basis point `y` to the point `h⁻¹ • j y`. -/
private noncomputable def indPermToFinsupp (φ : G →* H) (j : Y → X)
    (equivariant : ∀ (g : G) (y : Y), j (g • y) = φ g • j y) :
    IndV φ (ofMulAction ℂ G Y) →ₗ[ℂ] (X →₀ ℂ) :=
  Coinvariants.lift _
    (Finsupp.lmapDomain ℂ ℂ (fun p : H × Y => p.1⁻¹ • j p.2) ∘ₗ
      (finsuppTensorFinsupp' ℂ H Y).toLinearMap)
    fun g => by
      ext h y
      simp [mul_smul, equivariant]

private theorem indPermToFinsupp_mk (φ : G →* H) (j : Y → X)
    (equivariant : ∀ (g : G) (y : Y), j (g • y) = φ g • j y)
    (h : H) (y : Y) (z : ℂ) :
    indPermToFinsupp φ j equivariant (IndV.mk φ _ h (Finsupp.single y z)) =
      Finsupp.single (h⁻¹ • j y) z := by
  simp [indPermToFinsupp]

/-- The map into the induced permutation representation choosing a generator
carrying a basis point to the given point. -/
private noncomputable def indPermOfFinsupp (φ : G →* H) (j : Y → X)
    (surj : ∀ x : X, ∃ h : H, ∃ y : Y, h⁻¹ • j y = x) :
    (X →₀ ℂ) →ₗ[ℂ] IndV φ (ofMulAction ℂ G Y) :=
  Finsupp.linearCombination ℂ fun x =>
    IndV.mk φ _ (surj x).choose (Finsupp.single (surj x).choose_spec.choose 1)

private theorem indPermOfFinsupp_single (φ : G →* H) (j : Y → X)
    (surj : ∀ x : X, ∃ h : H, ∃ y : Y, h⁻¹ • j y = x) (x : X) (z : ℂ) :
    indPermOfFinsupp φ j surj (Finsupp.single x z) =
      IndV.mk φ _ (surj x).choose
        (Finsupp.single (surj x).choose_spec.choose z) := by
  rw [indPermOfFinsupp, Finsupp.linearCombination_single, ← map_smul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Generators of the induced permutation representation indexed by the same
coset of the same basis point agree. -/
private theorem indPermMk_mul (φ : G →* H) (g : G) (h : H) (y : Y) (z : ℂ) :
    IndV.mk φ (ofMulAction ℂ G Y) (φ g * h) (Finsupp.single (g • y) z) =
      IndV.mk φ _ h (Finsupp.single y z) := by
  have := Coinvariants.mk_self_apply
    (Representation.tprod ((leftRegular ℂ H).comp φ) (ofMulAction ℂ G Y)) g
    (Finsupp.single h (1 : ℂ) ⊗ₜ[ℂ] Finsupp.single y z)
  simpa using this

/-- When `H` acts on `X` so that `j` matches `Y` with the fibre of a point and
`φ` with its stabiliser, the induced permutation representation is the
permutation module on `X`. -/
private noncomputable def indPermFinsuppEquiv (φ : G →* H) (j : Y → X)
    (equivariant : ∀ (g : G) (y : Y), j (g • y) = φ g • j y)
    (surj : ∀ x : X, ∃ h : H, ∃ y : Y, h⁻¹ • j y = x)
    (rel : ∀ (h : H) (y y' : Y), h • j y' = j y → ∃ g : G, φ g = h ∧ g • y' = y) :
    IndV φ (ofMulAction ℂ G Y) ≃ₗ[ℂ] (X →₀ ℂ) :=
  LinearEquiv.ofLinear (indPermToFinsupp φ j equivariant)
    (indPermOfFinsupp φ j surj)
    (Finsupp.lhom_ext' fun x => LinearMap.ext_ring (by
      show indPermToFinsupp φ j equivariant
          (indPermOfFinsupp φ j surj (Finsupp.single x 1)) = Finsupp.single x 1
      rw [indPermOfFinsupp_single, indPermToFinsupp_mk,
        (surj x).choose_spec.choose_spec]))
    (IndV.hom_ext _ _ fun h => Finsupp.lhom_ext fun y z => by
      obtain ⟨g, hg, hgy⟩ := rel (h * (surj (h⁻¹ • j y)).choose⁻¹) y
        (surj (h⁻¹ • j y)).choose_spec.choose (by
          rw [mul_smul, (surj (h⁻¹ • j y)).choose_spec.choose_spec, smul_inv_smul])
      show indPermOfFinsupp φ j surj (indPermToFinsupp φ j equivariant
          (IndV.mk φ _ h (Finsupp.single y z))) = IndV.mk φ _ h (Finsupp.single y z)
      rw [indPermToFinsupp_mk, indPermOfFinsupp_single,
        ← indPermMk_mul φ g (surj (h⁻¹ • j y)).choose
          (surj (h⁻¹ • j y)).choose_spec.choose z,
        hg, hgy, inv_mul_cancel_right])

end Representation

/-- Inducing a permutation representation along an equivariant matching of basis
points yields the permutation module on the target. -/
noncomputable def FDRep.indOfMulActionIso {G H Y X : Type} [Group G] [Group H]
    [Finite H] [MulAction G Y] [MulAction H X] [Finite X] [Finite Y]
    (φ : G →* H) (j : Y → X)
    (equivariant : ∀ (g : G) (y : Y), j (g • y) = φ g • j y)
    (surj : ∀ x : X, ∃ h : H, ∃ y : Y, h⁻¹ • j y = x)
    (rel : ∀ (h : H) (y y' : Y), h • j y' = j y → ∃ g : G, φ g = h ∧ g • y' = y) :
    FDRep.ind φ (FDRep.of (Representation.ofMulAction ℂ G Y)) ≅
      FDRep.of (Representation.ofMulAction ℂ H X) := by
  haveI : Module.Finite ℂ (Representation.IndV φ (Representation.ofMulAction ℂ G Y)) :=
    Module.Finite.equiv
      (Representation.indPermFinsuppEquiv φ j equivariant surj rel).symm
  refine Action.mkIso
    (Representation.indPermFinsuppEquiv φ j equivariant surj rel).toFGModuleCatIso ?_
  intro h
  apply FGModuleCat.hom_ext
  refine Representation.IndV.hom_ext φ _ fun h₂ => Finsupp.lhom_ext fun y z => ?_
  show Representation.indPermToFinsupp φ j equivariant
      (Representation.ind φ _ h (Representation.IndV.mk φ _ h₂ (Finsupp.single y z))) =
    Representation.ofMulAction ℂ H X h
      (Representation.indPermToFinsupp φ j equivariant
        (Representation.IndV.mk φ _ h₂ (Finsupp.single y z)))
  rw [Representation.ind_mk, Representation.indPermToFinsupp_mk,
    Representation.indPermToFinsupp_mk, Representation.ofMulAction_single,
    mul_inv_rev, inv_inv, mul_smul]

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
