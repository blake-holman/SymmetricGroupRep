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

/-- The standard Young subgroup consists of the permutations preserving the first block. -/
theorem SymmetricGroup.mem_youngSubgroupInclusion_range_iff (a b : ℕ)
    (sigma : SymmetricGroup (a + b)) :
    sigma ∈ (SymmetricGroup.youngSubgroupInclusion a b).range ↔
      ∀ i : Fin (a + b), (i : ℕ) < a → (sigma i : ℕ) < a := by
  constructor
  · rintro ⟨⟨_, _⟩, rfl⟩ i
    induction i using Fin.addCases with
    | left j => simp
    | right j => simp
  · intro hmaps
    have hblock : Set.MapsTo (finSumFinEquiv.permCongrHom.symm sigma)
        (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro x ⟨j, rfl⟩
      refine ⟨⟨_, hmaps (Fin.castAdd b j) (by simp)⟩, ?_⟩
      simp [Equiv.eq_symm_apply]
    obtain ⟨pair, hpair⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hblock
    refine ⟨pair, ?_⟩
    simp only [SymmetricGroup.youngSubgroupInclusion, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hpair, MulEquiv.apply_symm_apply]
