import SymmetricGroupRep.Branching
import SymmetricGroupRep.OuterTensor
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

/-- Inducing `S^μ ⊠ 1` from `S_n × S_2` to `S_(n+2)` adds a horizontal two-strip.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 4.9.4. -/
axiom spechtModule_pieri_horizontal {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.youngSubgroupInduction n 2).obj
    (FDRep.outerTensor (spechtModule μ) (𝟙_ (SymmetricGroupRepresentation 2))) ≅
      ⨁ fun ν : HorizontalTwoStrip μ => spechtModule ν.val)

/-- Inducing `S^μ ⊠ sgn` from `S_n × S_2` to `S_(n+2)` adds a vertical two-strip.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 4.9.4. -/
axiom spechtModule_pieri_vertical {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.youngSubgroupInduction n 2).obj
    (FDRep.outerTensor (spechtModule μ) (SymmetricGroupRepresentation.sign 2)) ≅
      ⨁ fun ν : VerticalTwoStrip μ => spechtModule ν.val)
