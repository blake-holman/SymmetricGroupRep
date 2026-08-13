import SymmetricGroupRep.Induction
import SymmetricGroupRep.OuterTensor
import SymmetricGroupRep.Partitions
import SymmetricGroupRep.Pieri
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

/-- A row has cells exactly when it is listed in `rowLens`. -/
private theorem rowLen_pos_iff {μ : YoungDiagram} {r : ℕ} :
    0 < μ.rowLen r ↔ r < μ.rowLens.length := by
  rw [YoungDiagram.length_rowLens, ← YoungDiagram.mem_iff_lt_colLen,
    ← YoungDiagram.mem_iff_lt_rowLen]

/-- A diagram of size `n` has at most `n` rows. -/
private theorem length_rowLens_le {n : ℕ} (μ : YoungDiagramOfSize n) :
    μ.val.rowLens.length ≤ n := by
  rw [YoungDiagram.length_rowLens]
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (Tabloid.cell_fst_lt (mu := μ)
      ⟨(n, 0), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_colLen.mpr hlt)⟩)
    (lt_irrefl n)

namespace Tabloid

variable {a b : ℕ} {α : YoungDiagramOfSize a} {β : YoungDiagramOfSize b}

/-- The merged row assignment: first-block labels keep the rows of the first
tabloid and second-block labels the rows of the second. -/
private noncomputable def combineRowOf (T : Tabloid α) (U : Tabloid β) :
    Fin (a + b) → Fin (a + b) :=
  Fin.addCases
    (fun i => ⟨(YoungDiagramOfSize.combineRowEquiv α β
        (Sum.inl ⟨(T.rowOf i : ℕ), rowLen_pos_iff.mp (T.row_nonempty i)⟩) : ℕ),
      lt_of_lt_of_le (Fin.isLt _) (length_rowLens_le _)⟩)
    (fun i => ⟨(YoungDiagramOfSize.combineRowEquiv α β
        (Sum.inr ⟨(U.rowOf i : ℕ), rowLen_pos_iff.mp (U.row_nonempty i)⟩) : ℕ),
      lt_of_lt_of_le (Fin.isLt _) (length_rowLens_le _)⟩)

private theorem combineRowOf_castAdd (T : Tabloid α) (U : Tabloid β) (i : Fin a) :
    (combineRowOf T U (Fin.castAdd b i) : ℕ) =
      (YoungDiagramOfSize.combineRowEquiv α β
        (Sum.inl ⟨(T.rowOf i : ℕ), rowLen_pos_iff.mp (T.row_nonempty i)⟩) : ℕ) := by
  rw [combineRowOf, Fin.addCases_left]

private theorem combineRowOf_natAdd (T : Tabloid α) (U : Tabloid β) (i : Fin b) :
    (combineRowOf T U (Fin.natAdd a i) : ℕ) =
      (YoungDiagramOfSize.combineRowEquiv α β
        (Sum.inr ⟨(U.rowOf i : ℕ), rowLen_pos_iff.mp (U.row_nonempty i)⟩) : ℕ) := by
  rw [combineRowOf, Fin.addCases_right]

/-- The merged tabloid of a pair of tabloids. -/
noncomputable def combine (T : Tabloid α) (U : Tabloid β) : Tabloid (α.combine β) where
  rowOf := combineRowOf T U
  row_nonempty i := by
    induction i using Fin.addCases with
    | left j =>
        rw [show ((combineRowOf T U (Fin.castAdd b j) : Fin (a + b)) : ℕ) = _ from
          combineRowOf_castAdd T U j]
        exact rowLen_pos_iff.mpr (Fin.isLt _)
    | right j =>
        rw [show ((combineRowOf T U (Fin.natAdd a j) : Fin (a + b)) : ℕ) = _ from
          combineRowOf_natAdd T U j]
        exact rowLen_pos_iff.mpr (Fin.isLt _)
  content row := by
    by_cases hrow : row < (α.combine β).val.rowLens.length
    · rcases hs : (YoungDiagramOfSize.combineRowEquiv α β).symm ⟨row, hrow⟩ with p | p
      · have heq : YoungDiagramOfSize.combineRowEquiv α β (Sum.inl p) = ⟨row, hrow⟩ := by
          rw [← hs, Equiv.apply_symm_apply]
        have hrowLen : (α.combine β).val.rowLen row = α.val.rowLen p := by
          have := YoungDiagramOfSize.rowLen_combineRowEquiv_inl α β p
          rwa [heq] at this
        rw [hrowLen, ← T.content (p : ℕ)]
        refine (Finset.card_nbij (fun i => Fin.castAdd b i) ?_ ?_ ?_).symm
        · intro i hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
          rw [show ((combineRowOf T U (Fin.castAdd b i) : Fin (a + b)) : ℕ) = _ from
              combineRowOf_castAdd T U i,
            show (⟨(T.rowOf i : ℕ), rowLen_pos_iff.mp (T.row_nonempty i)⟩ :
              Fin α.val.rowLens.length) = p from Fin.ext hi, heq]
        · intro i _ j _ hij
          simpa using hij
        · intro i hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi
          induction i using Fin.addCases with
          | left j =>
              refine ⟨j, ?_, rfl⟩
              simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
              rw [show ((combineRowOf T U (Fin.castAdd b j) : Fin (a + b)) : ℕ) = _ from
                combineRowOf_castAdd T U j] at hi
              have hj : YoungDiagramOfSize.combineRowEquiv α β
                  (Sum.inl ⟨(T.rowOf j : ℕ), rowLen_pos_iff.mp (T.row_nonempty j)⟩) =
                    ⟨row, hrow⟩ := Fin.ext hi
              exact congrArg Fin.val (Sum.inl.inj
                ((YoungDiagramOfSize.combineRowEquiv α β).injective (hj.trans heq.symm)))
          | right j =>
              rw [show ((combineRowOf T U (Fin.natAdd a j) : Fin (a + b)) : ℕ) = _ from
                combineRowOf_natAdd T U j] at hi
              have hj : YoungDiagramOfSize.combineRowEquiv α β
                  (Sum.inr ⟨(U.rowOf j : ℕ), rowLen_pos_iff.mp (U.row_nonempty j)⟩) =
                    ⟨row, hrow⟩ := Fin.ext hi
              exact absurd ((YoungDiagramOfSize.combineRowEquiv α β).injective
                (heq.trans hj.symm)) (by simp)
      · have heq : YoungDiagramOfSize.combineRowEquiv α β (Sum.inr p) = ⟨row, hrow⟩ := by
          rw [← hs, Equiv.apply_symm_apply]
        have hrowLen : (α.combine β).val.rowLen row = β.val.rowLen p := by
          have := YoungDiagramOfSize.rowLen_combineRowEquiv_inr α β p
          rwa [heq] at this
        rw [hrowLen, ← U.content (p : ℕ)]
        refine (Finset.card_nbij (fun i => Fin.natAdd a i) ?_ ?_ ?_).symm
        · intro i hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
          rw [show ((combineRowOf T U (Fin.natAdd a i) : Fin (a + b)) : ℕ) = _ from
              combineRowOf_natAdd T U i,
            show (⟨(U.rowOf i : ℕ), rowLen_pos_iff.mp (U.row_nonempty i)⟩ :
              Fin β.val.rowLens.length) = p from Fin.ext hi, heq]
        · intro i _ j _ hij
          simpa using hij
        · intro i hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi
          induction i using Fin.addCases with
          | left j =>
              rw [show ((combineRowOf T U (Fin.castAdd b j) : Fin (a + b)) : ℕ) = _ from
                combineRowOf_castAdd T U j] at hi
              have hj : YoungDiagramOfSize.combineRowEquiv α β
                  (Sum.inl ⟨(T.rowOf j : ℕ), rowLen_pos_iff.mp (T.row_nonempty j)⟩) =
                    ⟨row, hrow⟩ := Fin.ext hi
              exact absurd ((YoungDiagramOfSize.combineRowEquiv α β).injective
                (heq.trans hj.symm)) (by simp)
          | right j =>
              refine ⟨j, ?_, rfl⟩
              simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
              rw [show ((combineRowOf T U (Fin.natAdd a j) : Fin (a + b)) : ℕ) = _ from
                combineRowOf_natAdd T U j] at hi
              have hj : YoungDiagramOfSize.combineRowEquiv α β
                  (Sum.inr ⟨(U.rowOf j : ℕ), rowLen_pos_iff.mp (U.row_nonempty j)⟩) =
                    ⟨row, hrow⟩ := Fin.ext hi
              exact congrArg Fin.val (Sum.inr.inj
                ((YoungDiagramOfSize.combineRowEquiv α β).injective (hj.trans heq.symm)))
    · have hzero : (α.combine β).val.rowLen row = 0 := by
        by_contra hne
        exact hrow (rowLen_pos_iff.mp (Nat.pos_of_ne_zero hne))
      rw [not_lt] at hrow
      rw [hzero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i -
      induction i using Fin.addCases with
      | left j =>
          rw [show ((combineRowOf T U (Fin.castAdd b j) : Fin (a + b)) : ℕ) = _ from
            combineRowOf_castAdd T U j]
          have hlt := Fin.isLt (YoungDiagramOfSize.combineRowEquiv α β
            (Sum.inl ⟨(T.rowOf j : ℕ), rowLen_pos_iff.mp (T.row_nonempty j)⟩))
          omega
      | right j =>
          rw [show ((combineRowOf T U (Fin.natAdd a j) : Fin (a + b)) : ℕ) = _ from
            combineRowOf_natAdd T U j]
          have hlt := Fin.isLt (YoungDiagramOfSize.combineRowEquiv α β
            (Sum.inr ⟨(U.rowOf j : ℕ), rowLen_pos_iff.mp (U.row_nonempty j)⟩))
          omega

/-- Merged rows remember their block. -/
private theorem combineRowOf_castAdd_ne_natAdd (T T' : Tabloid α) (U U' : Tabloid β)
    (i : Fin a) (j : Fin b) :
    combineRowOf T U (Fin.castAdd b i) ≠ combineRowOf T' U' (Fin.natAdd a j) := by
  intro hcontra
  have hval := congrArg Fin.val hcontra
  rw [combineRowOf_castAdd, combineRowOf_natAdd] at hval
  exact absurd ((YoungDiagramOfSize.combineRowEquiv α β).injective (Fin.ext hval))
    (by simp)

/-- Merged rows remember the row of the first input. -/
private theorem combineRowOf_castAdd_inj (T T' : Tabloid α) (U U' : Tabloid β)
    (i i' : Fin a)
    (heq : combineRowOf T U (Fin.castAdd b i) = combineRowOf T' U' (Fin.castAdd b i')) :
    T.rowOf i = T'.rowOf i' := by
  have hval := congrArg Fin.val heq
  rw [combineRowOf_castAdd, combineRowOf_castAdd] at hval
  have hsum := (YoungDiagramOfSize.combineRowEquiv α β).injective (Fin.ext hval)
  have hmk := Sum.inl.inj hsum
  have hval2 := congrArg Fin.val hmk
  exact Fin.ext hval2

/-- Merged rows remember the row of the second input. -/
private theorem combineRowOf_natAdd_inj (T T' : Tabloid α) (U U' : Tabloid β)
    (j j' : Fin b)
    (heq : combineRowOf T U (Fin.natAdd a j) = combineRowOf T' U' (Fin.natAdd a j')) :
    U.rowOf j = U'.rowOf j' := by
  have hval := congrArg Fin.val heq
  rw [combineRowOf_natAdd, combineRowOf_natAdd] at hval
  have hsum := (YoungDiagramOfSize.combineRowEquiv α β).injective (Fin.ext hval)
  have hmk := Sum.inr.inj hsum
  have hval2 := congrArg Fin.val hmk
  exact Fin.ext hval2

/-- Merging is equivariant for the Young-subgroup inclusion. -/
private theorem combine_smul (g : SymmetricGroup a) (h : SymmetricGroup b)
    (T : Tabloid α) (U : Tabloid β) :
    (g • T).combine (h • U) =
      SymmetricGroup.youngSubgroupInclusion a b (g, h) • (T.combine U) := by
  apply Tabloid.ext
  funext i
  rw [smul_rowOf]
  induction i using Fin.addCases with
  | left j =>
      have harg : (SymmetricGroup.youngSubgroupInclusion a b (g, h))⁻¹
          (Fin.castAdd b j) = Fin.castAdd b (g⁻¹ j) := by
        rw [← map_inv]
        exact SymmetricGroup.youngSubgroupInclusion_apply_castAdd g⁻¹ h⁻¹ j
      rw [harg]
      apply Fin.ext
      rw [show (((g • T).combine (h • U)).rowOf (Fin.castAdd b j) : ℕ) = _ from
          combineRowOf_castAdd (g • T) (h • U) j,
        show ((T.combine U).rowOf (Fin.castAdd b (g⁻¹ j)) : ℕ) = _ from
          combineRowOf_castAdd T U (g⁻¹ j)]
      simp only [Tabloid.smul_rowOf]
  | right j =>
      have harg : (SymmetricGroup.youngSubgroupInclusion a b (g, h))⁻¹
          (Fin.natAdd a j) = Fin.natAdd a (h⁻¹ j) := by
        rw [← map_inv]
        exact SymmetricGroup.youngSubgroupInclusion_apply_natAdd g⁻¹ h⁻¹ j
      rw [harg]
      apply Fin.ext
      rw [show (((g • T).combine (h • U)).rowOf (Fin.natAdd a j) : ℕ) = _ from
          combineRowOf_natAdd (g • T) (h • U) j,
        show ((T.combine U).rowOf (Fin.natAdd a (h⁻¹ j)) : ℕ) = _ from
          combineRowOf_natAdd T U (h⁻¹ j)]
      simp only [Tabloid.smul_rowOf]

end Tabloid

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

/-- Inducing the outer tensor product of two Young permutation modules along
the standard Young subgroup gives the combined Young permutation module. -/
noncomputable def youngPermutationCombineIso {a b : ℕ}
    (α : YoungDiagramOfSize a) (β : YoungDiagramOfSize b) :
    (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (FDRep.outerTensor (youngPermutationModule α) (youngPermutationModule β)) ≅
      youngPermutationModule (α.combine β) :=
  (SymmetricGroupRepresentation.youngSubgroupInduction a b).mapIso
      (outerTensorYoungPermutationIso α β) ≪≫
    FDRep.indOfMulActionIso (SymmetricGroup.youngSubgroupInclusion a b)
      (fun p : Tabloid α × Tabloid β => p.1.combine p.2)
      (fun g p => Tabloid.combine_smul g.1 g.2 p.1 p.2)
      (fun W => by
        obtain ⟨T₀⟩ := Tabloid.nonempty α
        obtain ⟨U₀⟩ := Tabloid.nonempty β
        obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (SymmetricGroup (a + b))
          (T₀.combine U₀) W
        exact ⟨σ⁻¹, (T₀, U₀), by simpa using hσ⟩)
      (fun h p p' hmatch => by
        obtain ⟨T, U⟩ := p
        obtain ⟨T', U'⟩ := p'
        have hrows : ∀ i, (T'.combine U').rowOf (h⁻¹ i) = (T.combine U).rowOf i := by
          intro i
          have := congrArg (fun W : Tabloid (α.combine β) => W.rowOf i) hmatch
          simpa using this
        have hblock : ∀ i : Fin (a + b), (i : ℕ) < a →
            ((h⁻¹ i : Fin (a + b)) : ℕ) < a := by
          intro i hi
          by_contra hge
          rw [not_lt] at hge
          set k := h⁻¹ i with hk
          have hri : (T'.combine U').rowOf k = (T.combine U).rowOf i := hrows i
          have hival : i = Fin.castAdd b ⟨(i : ℕ), hi⟩ := Fin.ext rfl
          have hkval : k = Fin.natAdd a ⟨(k : ℕ) - a, by have := k.isLt; omega⟩ :=
            Fin.ext (by simp only [Fin.val_natAdd]; omega)
          rw [hival] at hri
          rw [hkval] at hri
          exact absurd hri.symm
            (Tabloid.combineRowOf_castAdd_ne_natAdd T T' U U' _ _)
        have hmem : h⁻¹ ∈ (SymmetricGroup.youngSubgroupInclusion a b).range :=
          (SymmetricGroup.mem_youngSubgroupInclusion_range_iff a b h⁻¹).mpr hblock
        have hmem' : h ∈ (SymmetricGroup.youngSubgroupInclusion a b).range := by
          simpa using inv_mem hmem
        obtain ⟨⟨g₁, g₂⟩, hg⟩ := hmem'
        have hT : g₁ • T' = T := by
          apply Tabloid.ext
          funext i
          have hri := hrows (Fin.castAdd b i)
          have harg : h⁻¹ (Fin.castAdd b i) = Fin.castAdd b (g₁⁻¹ i) := by
            rw [← hg, ← map_inv]
            exact SymmetricGroup.youngSubgroupInclusion_apply_castAdd g₁⁻¹ g₂⁻¹ i
          rw [harg] at hri
          have := Tabloid.combineRowOf_castAdd_inj T' T U' U (g₁⁻¹ i) i hri
          simpa using this
        have hU : g₂ • U' = U := by
          apply Tabloid.ext
          funext i
          have hri := hrows (Fin.natAdd a i)
          have harg : h⁻¹ (Fin.natAdd a i) = Fin.natAdd a (g₂⁻¹ i) := by
            rw [← hg, ← map_inv]
            exact SymmetricGroup.youngSubgroupInclusion_apply_natAdd g₁⁻¹ g₂⁻¹ i
          rw [harg] at hri
          have := Tabloid.combineRowOf_natAdd_inj T' T U' U (g₂⁻¹ i) i hri
          simpa using this
        exact ⟨(g₁, g₂), hg, Prod.ext hT hU⟩)
