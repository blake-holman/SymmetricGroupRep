import SymmetricGroupRep.Branching
import SymmetricGroupRep.OuterTensor
import SymmetricGroupRep.TwoBoxInduction
import SymmetricGroupRep.YoungSubgroup
import Mathlib.GroupTheory.Perm.Sign

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- Induction from the standard Young subgroup `S_a × S_b` to `S_(a+b)`. -/
noncomputable abbrev SymmetricGroupRepresentation.youngSubgroupInduction (a b : ℕ) :
    FDRep ℂ (SymmetricGroup a × SymmetricGroup b) ⥤
      SymmetricGroupRepresentation (a + b) :=
  FDRep.indFunctor ℂ (SymmetricGroup.youngSubgroupInclusion a b)

/-- The complex sign representation of `S_n`. -/
noncomputable def SymmetricGroupRepresentation.sign (n : ℕ) :
    SymmetricGroupRepresentation n :=
  FDRep.of <| (Algebra.lsmul ℂ ℂ ℂ).toMonoidHom.comp <|
    (Int.castRingHom ℂ).toMonoidHom.comp <|
      (Units.coeHom ℤ).comp Equiv.Perm.sign

/-- The transposition acts trivially on the unit representation of `S_2`. -/
theorem SymmetricGroupRepresentation.tensorUnit_rho_swap
    (y : 𝟙_ (SymmetricGroupRepresentation 2)) :
    (𝟙_ (SymmetricGroupRepresentation 2)).ρ (Equiv.swap 0 1) y = (1 : ℂ) • y := by
  rw [one_smul]
  rfl

/-- The transposition acts by `-1` on the sign representation of `S_2`. -/
theorem SymmetricGroupRepresentation.sign_rho_swap (y : SymmetricGroupRepresentation.sign 2) :
    (SymmetricGroupRepresentation.sign 2).ρ (Equiv.swap 0 1) y = (-1 : ℂ) • y := by
  show ((Equiv.Perm.sign (Equiv.swap (0 : Fin 2) 1) : ℤ) : ℂ) • y = (-1 : ℂ) • y
  rw [Equiv.Perm.sign_swap (by decide)]
  norm_num

/-- Inducing `S^μ ⊠ 1` from `S_n × S_2` to `S_(n+2)` adds a horizontal two-strip.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 4.9.4. The proof here reads
the multiplicity off Young's orthogonal form instead: by Frobenius reciprocity it
is the dimension of the space of morphisms out of `S^μ` fixed by the transposition
of the last two labels, and that transposition acts on the two-step branching
multiplicity space through its axial-distance matrix. -/
theorem spechtModule_pieri_horizontal {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.youngSubgroupInduction n 2).obj
    (FDRep.outerTensor (spechtModule μ) (𝟙_ (SymmetricGroupRepresentation 2))) ≅
      ⨁ fun ν : HorizontalTwoStrip μ => spechtModule ν.val) := by
  classical
  refine FDRep.nonempty_iso_of_finrank_hom_eq spechtModule spechtModule_irreducible
    (fun α β h => (spechtModule_iso_iff_eq α β).mp h)
    (fun T hT => @exists_iso_spechtModule (n + 2) T hT) fun ξ => ?_
  rw [FDRep.finrank_hom_symm, FDRep.indFunctor_obj,
    (FDRep.indResHomEquiv (SymmetricGroup.youngSubgroupInclusion n 2)
      (FDRep.outerTensor (spechtModule μ) (𝟙_ (SymmetricGroupRepresentation 2)))
      (spechtModule ξ)).finrank_eq,
    finrank_hom_outerTensor_res (LinearEquiv.refl ℂ ℂ)
      SymmetricGroupRepresentation.tensorUnit_rho_swap,
    (finrank_lastAdjacentEigenspace_eq μ ξ).1,
    finrank_hom_spechtModule_biproduct (fun ν => IsHorizontalTwoStrip μ ν) ξ]

/-- Inducing `S^μ ⊠ sgn` from `S_n × S_2` to `S_(n+2)` adds a vertical two-strip.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 4.9.4. The proof is the
horizontal one with the other eigenvalue: the sign representation of `S_2` turns
the fixed space of the last transposition into its `-1` eigenspace, which is
carried by the two-step paths whose two cells lie in different rows. -/
theorem spechtModule_pieri_vertical {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.youngSubgroupInduction n 2).obj
    (FDRep.outerTensor (spechtModule μ) (SymmetricGroupRepresentation.sign 2)) ≅
      ⨁ fun ν : VerticalTwoStrip μ => spechtModule ν.val) := by
  classical
  refine FDRep.nonempty_iso_of_finrank_hom_eq spechtModule spechtModule_irreducible
    (fun α β h => (spechtModule_iso_iff_eq α β).mp h)
    (fun T hT => @exists_iso_spechtModule (n + 2) T hT) fun ξ => ?_
  rw [FDRep.finrank_hom_symm, FDRep.indFunctor_obj,
    (FDRep.indResHomEquiv (SymmetricGroup.youngSubgroupInclusion n 2)
      (FDRep.outerTensor (spechtModule μ) (SymmetricGroupRepresentation.sign 2))
      (spechtModule ξ)).finrank_eq,
    finrank_hom_outerTensor_res (LinearEquiv.refl ℂ ℂ)
      SymmetricGroupRepresentation.sign_rho_swap,
    (finrank_lastAdjacentEigenspace_eq μ ξ).2,
    finrank_hom_spechtModule_biproduct (fun ν => IsVerticalTwoStrip μ ν) ξ]
