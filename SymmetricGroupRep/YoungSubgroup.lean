import SymmetricGroupRep.Classification
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Fin.Basic

/-- The standard Young-subgroup inclusion `S_a × S_b → S_(a+b)`, where each
permutation acts on its corresponding block. -/
noncomputable def SymmetricGroup.youngSubgroupInclusion (a b : ℕ) :
    SymmetricGroup a × SymmetricGroup b →* SymmetricGroup (a + b) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin a) (Fin b))

/-- The Young-subgroup inclusion is injective. -/
theorem SymmetricGroup.youngSubgroupInclusion_injective (a b : ℕ) :
    Function.Injective (SymmetricGroup.youngSubgroupInclusion a b) := by
  exact finSumFinEquiv.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective

/-- On the first block, the Young-subgroup inclusion acts by its first permutation. -/
@[simp]
theorem SymmetricGroup.youngSubgroupInclusion_apply_castAdd {a b : ℕ}
    (sigma : SymmetricGroup a) (tau : SymmetricGroup b) (i : Fin a) :
    SymmetricGroup.youngSubgroupInclusion a b (sigma, tau) (Fin.castAdd b i) =
      Fin.castAdd b (sigma i) := by
  simp [SymmetricGroup.youngSubgroupInclusion]

/-- On the second block, the Young-subgroup inclusion acts by its second permutation. -/
@[simp]
theorem SymmetricGroup.youngSubgroupInclusion_apply_natAdd {a b : ℕ}
    (sigma : SymmetricGroup a) (tau : SymmetricGroup b) (i : Fin b) :
    SymmetricGroup.youngSubgroupInclusion a b (sigma, tau) (Fin.natAdd a i) =
      Fin.natAdd a (tau i) := by
  simp [SymmetricGroup.youngSubgroupInclusion]
