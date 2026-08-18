import SymmetricGroupRep.Kostka
import SymmetricGroupRep.ProductClassification
import SymmetricGroupRep.YoungPermutationProduct

/-! # The representation side of the Littlewood-Richardson bridge

The multiplicity of `S^ξ` in the induced product of two Young permutation
modules is a Kostka number, by the combined-weight isomorphism.  Expanding both
permutation modules by Young's rule inside the character pairing turns that
statement into a Kostka convolution identity for the Littlewood-Richardson
multiplicities.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

namespace FDRep

variable {k G : Type} [Field k] [Group G]

/-- The character of a finite biproduct is the sum of the characters. -/
theorem character_biproduct {ι : Type} [Fintype ι] (f : ι → FDRep k G) (g : G) :
    (⨁ f : FDRep k G).character g = ∑ i, (f i).character g := by
  classical
  let ext : ((⨁ f : FDRep k G) ⟶ ⨁ f) →+
      ((⨁ f : FDRep k G) →ₗ[k] (⨁ f : FDRep k G)) :=
    { toFun := fun u => u.hom.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hid : (LinearMap.id : (⨁ f : FDRep k G) →ₗ[k] (⨁ f : FDRep k G)) =
      ∑ i, (biproduct.ι f i).hom.hom.hom ∘ₗ (biproduct.π f i).hom.hom.hom :=
    calc (LinearMap.id : (⨁ f : FDRep k G) →ₗ[k] (⨁ f : FDRep k G))
        = ext (𝟙 (⨁ f : FDRep k G)) := rfl
      _ = ext (∑ i, biproduct.π f i ≫ biproduct.ι f i) := by
          rw [biproduct.total]
      _ = ∑ i, ext (biproduct.π f i ≫ biproduct.ι f i) := map_sum ext _ _
      _ = ∑ i, (biproduct.ι f i).hom.hom.hom ∘ₗ (biproduct.π f i).hom.hom.hom := rfl
  have hπ : ∀ i, (biproduct.π f i).hom.hom.hom ∘ₗ ((⨁ f : FDRep k G).ρ g) =
      (f i).ρ g ∘ₗ (biproduct.π f i).hom.hom.hom := by
    intro i
    have := congrArg (fun u : ((⨁ f : FDRep k G).V ⟶ (f i).V) => u.hom.hom)
      ((biproduct.π f i).comm g)
    simpa using this
  have hPI : ∀ i, (biproduct.π f i).hom.hom.hom ∘ₗ (biproduct.ι f i).hom.hom.hom =
      (LinearMap.id : (f i : Type) →ₗ[k] f i) := by
    intro i
    have := congrArg (fun u : ((f i : FDRep k G) ⟶ f i) => u.hom.hom.hom)
      (biproduct.ι_π_self (f := f) (j := i))
    exact this
  calc (⨁ f : FDRep k G).character g
      = LinearMap.trace k _ (((⨁ f : FDRep k G).ρ g) ∘ₗ LinearMap.id) := by
        rw [LinearMap.comp_id]; rfl
    _ = ∑ i, LinearMap.trace k _ (((⨁ f : FDRep k G).ρ g) ∘ₗ
          ((biproduct.ι f i).hom.hom.hom ∘ₗ (biproduct.π f i).hom.hom.hom)) := by
        rw [hid]
        simp only [← Module.End.mul_eq_comp]
        rw [Finset.mul_sum, map_sum]
    _ = ∑ i, (f i).character g := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc,
          hπ i, LinearMap.comp_assoc, hPI i, LinearMap.comp_id]
        rfl

end FDRep

/-- Young's rule on characters: the character of a Young permutation module is
the Kostka-weighted sum of Specht characters. -/
theorem character_youngPermutationModule {n : ℕ} (α : YoungDiagramOfSize n)
    (σ : SymmetricGroup n) :
    (youngPermutationModule α).character σ =
      ∑ μ : YoungDiagramOfSize n,
        (kostkaNumber μ α : ℂ) * (spechtModule μ).character σ := by
  classical
  obtain ⟨e⟩ := youngsRule α
  rw [FDRep.char_iso e, FDRep.character_biproduct]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [FDRep.character_biproduct]
  simp [Finset.sum_const, mul_comm]

/-- The representation-side Kostka convolution: the Littlewood-Richardson
multiplicities convolved with two Kostka matrices give the Kostka numbers of
the combined weight. -/
theorem sum_kostka_mul_finrank_hom_ind {a b : ℕ}
    (α : YoungDiagramOfSize a) (β : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) :
    ∑ μ : YoungDiagramOfSize a, ∑ ν : YoungDiagramOfSize b,
        kostkaNumber μ α * kostkaNumber ν β *
          Module.finrank ℂ (spechtModule ξ ⟶
            (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
              (spechtOuterTensor μ ν)) =
      kostkaNumber ξ (α.combine β) := by
  classical
  haveI : Invertible ((Fintype.card (SymmetricGroup a × SymmetricGroup b)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  set X := (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion a b)).obj
    (spechtModule ξ) with hX
  have hterm : ∀ V : FDRep ℂ (SymmetricGroup a × SymmetricGroup b),
      (Module.finrank ℂ (spechtModule ξ ⟶
          (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj V) : ℂ) =
        ⅟(Fintype.card (SymmetricGroup a × SymmetricGroup b) : ℂ) •
          ∑ p : SymmetricGroup a × SymmetricGroup b,
            FDRep.character X p * V.character p⁻¹ := by
    intro V
    rw [FDRep.finrank_hom_symm, FDRep.indFunctor_obj,
      (FDRep.indResHomEquiv (SymmetricGroup.youngSubgroupInclusion a b) V
        (spechtModule ξ)).finrank_eq,
      ← FDRep.scalar_product_char_eq_finrank_equivariant]
    rw [hX, invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card]
  have hexpand : ∑ p : SymmetricGroup a × SymmetricGroup b,
      FDRep.character X p * (FDRep.outerTensor (youngPermutationModule α)
        (youngPermutationModule β)).character p⁻¹ =
      ∑ μ : YoungDiagramOfSize a, ∑ ν : YoungDiagramOfSize b,
        (kostkaNumber μ α : ℂ) * (kostkaNumber ν β : ℂ) *
          ∑ p : SymmetricGroup a × SymmetricGroup b,
            FDRep.character X p * (spechtOuterTensor μ ν).character p⁻¹ :=
    calc ∑ p : SymmetricGroup a × SymmetricGroup b,
        FDRep.character X p * (FDRep.outerTensor (youngPermutationModule α)
          (youngPermutationModule β)).character p⁻¹
        = ∑ p : SymmetricGroup a × SymmetricGroup b,
            ∑ μ : YoungDiagramOfSize a, ∑ ν : YoungDiagramOfSize b,
              (kostkaNumber μ α : ℂ) * (kostkaNumber ν β : ℂ) *
                (FDRep.character X p * (spechtOuterTensor μ ν).character p⁻¹) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [show p⁻¹ = (p.1⁻¹, p.2⁻¹) from rfl, FDRep.outerTensor_character,
            character_youngPermutationModule α, character_youngPermutationModule β,
            Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [FDRep.outerTensor_character]
          ring
      _ = ∑ μ : YoungDiagramOfSize a, ∑ ν : YoungDiagramOfSize b,
            (kostkaNumber μ α : ℂ) * (kostkaNumber ν β : ℂ) *
              ∑ p : SymmetricGroup a × SymmetricGroup b,
                FDRep.character X p * (spechtOuterTensor μ ν).character p⁻¹ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum]
  have hcast : ((kostkaNumber ξ (α.combine β) : ℕ) : ℂ) =
      ∑ μ : YoungDiagramOfSize a, ∑ ν : YoungDiagramOfSize b,
        (kostkaNumber μ α : ℂ) * (kostkaNumber ν β : ℂ) *
          (Module.finrank ℂ (spechtModule ξ ⟶
            (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
              (spechtOuterTensor μ ν)) : ℂ) := by
    rw [← YoungTableau.finrank_hom_eq_kostkaNumber ξ (α.combine β),
      (FDRep.homCongrTarget (spechtModule ξ)
        (youngPermutationCombineIso α β).symm).finrank_eq,
      hterm (FDRep.outerTensor (youngPermutationModule α) (youngPermutationModule β)),
      hexpand, Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hterm (spechtOuterTensor μ ν)]
    simp only [invOf_eq_inv, smul_eq_mul]
    ring
  rw [← Nat.cast_inj (R := ℂ)]
  push_cast
  exact hcast.symm
