import SymmetricGroupRep.CharacterProjector

open CategoryTheory
open scoped Classical

/-! # Algebra of character projectors -/

local instance {n : ℕ} (μ : YoungDiagramOfSize n) : Simple (spechtModule μ) :=
  spechtModule_irreducible μ

namespace FDRep

/-- Character projectors commute with every equivariant linear map. -/
theorem characterProjectorLinear_naturality {G : Type} [Group G] [Fintype G]
    (W V U : FDRep ℂ G) [Simple W] (f : V ⟶ U) :
    (characterProjectorLinear W U).comp f.hom.hom.hom =
      f.hom.hom.hom.comp (characterProjectorLinear W V) := by
  have hf (g : G) : f.hom.hom.hom.comp (V.ρ g) =
      (U.ρ g).comp f.hom.hom.hom :=
    congrArg (fun q => q.hom.hom) (f.comm g)
  ext v
  simp only [characterProjectorLinear, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  simpa only [LinearMap.comp_apply] using LinearMap.congr_fun (hf g).symm v

private theorem characterProjectorLinear_trace_comp {G : Type} [Group G] [Fintype G]
    (W U : FDRep ℂ G) [Simple W] [Simple U] (k : G) :
    LinearMap.trace ℂ U ((characterProjectorLinear W U).comp (U.ρ k)) =
      (Module.finrank ℂ W : ℂ) / Fintype.card G *
        ∑ g : G, W.character g⁻¹ * U.character (g * k) := by
  rw [characterProjectorLinear, LinearMap.smul_comp]
  have hsum : (∑ g : G, W.character g⁻¹ • U.ρ g).comp (U.ρ k) =
      ∑ g : G, W.character g⁻¹ • ((U.ρ g).comp (U.ρ k)) := by
    ext v
    simp
  rw [hsum]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change LinearMap.trace ℂ U ((U.ρ g).comp (U.ρ k)) = U.character (g * k)
  change LinearMap.trace ℂ U (U.ρ g * U.ρ k) = U.character (g * k)
  rw [← U.ρ.map_mul, ← FDRep.character]

private theorem characterProjectorLinear_character_convolution {G : Type} [Group G] [Fintype G]
    (W U : FDRep ℂ G) [Simple W] [Simple U] (k : G) :
    (Module.finrank ℂ W : ℂ) / Fintype.card G *
        ∑ g : G, W.character g⁻¹ * U.character (g * k) =
      if Nonempty (U ≅ W) then U.character k else 0 := by
  have hproj := congrArg (fun f : U ⟶ U => f.hom.hom.hom)
    (characterProjector_eq W U)
  simp only [characterProjector_hom_hom_hom] at hproj
  have hcomp := congrArg (fun f : U →ₗ[ℂ] U => f.comp (U.ρ k)) hproj
  have htrace := congrArg (LinearMap.trace ℂ U) hcomp
  rw [characterProjectorLinear_trace_comp] at htrace
  split_ifs at htrace ⊢
  · simpa only [Action.id_hom, ObjectProperty.FullSubcategory.id_hom, ModuleCat.hom_id,
      LinearMap.id_comp, FDRep.character] using htrace
  · simpa using htrace

/-- The normalized character projectors multiply as the central idempotents
indexed by simple representations. -/
theorem characterProjectorLinear_comp {G : Type} [Group G] [Fintype G]
    (W U V : FDRep ℂ G) [Simple W] [Simple U] :
    (characterProjectorLinear W V).comp (characterProjectorLinear U V) =
      if Nonempty (U ≅ W) then characterProjectorLinear U V else 0 := by
  ext v
  simp only [characterProjectorLinear, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, Finset.smul_sum]
  simp_rw [← Module.End.mul_apply, ← V.ρ.map_mul]
  rw [Finset.sum_comm]
  have hreindex (y : G) :
      ∑ x : G, ((Module.finrank ℂ U : ℂ) / Fintype.card G) • U.character x⁻¹ •
          ((Module.finrank ℂ W : ℂ) / Fintype.card G) • W.character y⁻¹ •
            (V.ρ (y * x)) v =
        ∑ k : G, ((Module.finrank ℂ U : ℂ) / Fintype.card G) •
          U.character ((y⁻¹ * k)⁻¹) • ((Module.finrank ℂ W : ℂ) / Fintype.card G) •
            W.character y⁻¹ • (V.ρ k) v := by
    apply Fintype.sum_equiv (Equiv.mulLeft y)
    intro x
    change ((Module.finrank ℂ U : ℂ) / Fintype.card G) • U.character x⁻¹ •
        ((Module.finrank ℂ W : ℂ) / Fintype.card G) • W.character y⁻¹ •
          (V.ρ (y * x)) v =
      ((Module.finrank ℂ U : ℂ) / Fintype.card G) • U.character (y⁻¹ * (y * x))⁻¹ •
        ((Module.finrank ℂ W : ℂ) / Fintype.card G) • W.character y⁻¹ •
          (V.ρ (y * x)) v
    rw [show y⁻¹ * (y * x) = x by group]
  simp_rw [hreindex]
  rw [Finset.sum_comm]
  have hchar (x y : G) : U.character ((x⁻¹ * y)⁻¹) = U.character (x * y⁻¹) := by
    rw [mul_inv_rev, inv_inv]
    exact (FDRep.char_mul_comm U y⁻¹ x).symm
  simp_rw [hchar]
  have hinner (y : G) :
      ∑ x : G, ((Module.finrank ℂ U : ℂ) / Fintype.card G) • U.character (x * y⁻¹) •
          ((Module.finrank ℂ W : ℂ) / Fintype.card G) • W.character x⁻¹ • (V.ρ y) v =
        (((Module.finrank ℂ U : ℂ) / Fintype.card G) *
          (((Module.finrank ℂ W : ℂ) / Fintype.card G) *
            ∑ x : G, W.character x⁻¹ * U.character (x * y⁻¹))) • (V.ρ y) v := by
    simp_rw [smul_smul]
    calc
      ∑ x : G, (((Module.finrank ℂ U : ℂ) / Fintype.card G) *
          (U.character (x * y⁻¹) *
            ((Module.finrank ℂ W : ℂ) / Fintype.card G * W.character x⁻¹))) • (V.ρ y) v =
          ∑ x : G, (((Module.finrank ℂ U : ℂ) / Fintype.card G) *
            (((Module.finrank ℂ W : ℂ) / Fintype.card G) *
              (W.character x⁻¹ * U.character (x * y⁻¹)))) • (V.ρ y) v := by
            apply Finset.sum_congr rfl
            intro x _
            congr 1
            ring
      _ = (∑ x : G, (((Module.finrank ℂ U : ℂ) / Fintype.card G) *
            (((Module.finrank ℂ W : ℂ) / Fintype.card G) *
              (W.character x⁻¹ * U.character (x * y⁻¹)))) ) • (V.ρ y) v := by
            rw [Finset.sum_smul]
      _ = (((Module.finrank ℂ U : ℂ) / Fintype.card G) *
          (((Module.finrank ℂ W : ℂ) / Fintype.card G) *
            ∑ x : G, W.character x⁻¹ * U.character (x * y⁻¹))) • (V.ρ y) v := by
            congr 1
            rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [hinner, characterProjectorLinear_character_convolution]
  split_ifs <;> simp [smul_smul]

/-- A normalized character projector is idempotent on every finite-dimensional
representation. -/
theorem characterProjectorLinear_idempotent {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] :
    (characterProjectorLinear W V).comp (characterProjectorLinear W V) =
      characterProjectorLinear W V := by
  rw [characterProjectorLinear_comp]
  simp

/-- Character projectors with nonisomorphic simple labels have zero product on
every finite-dimensional representation. -/
theorem characterProjectorLinear_comp_eq_zero_of_not_iso {G : Type} [Group G] [Fintype G]
    (W U V : FDRep ℂ G) [Simple W] [Simple U]
    (hWU : ¬ Nonempty (W ≅ U)) :
    (characterProjectorLinear W V).comp (characterProjectorLinear U V) = 0 := by
  rw [characterProjectorLinear_comp]
  apply if_neg
  intro hUW
  apply hWU
  rcases hUW with ⟨e⟩
  exact ⟨e.symm⟩

end FDRep

/-- On a Specht module, the character projector with any fixed Young label is
idempotent. -/
theorem spechtCharacterProjectorLinear_idempotent {n : ℕ}
    (μ ν : YoungDiagramOfSize n) :
    (FDRep.characterProjectorLinear (spechtModule μ) (spechtModule ν)).comp
        (FDRep.characterProjectorLinear (spechtModule μ) (spechtModule ν)) =
      FDRep.characterProjectorLinear (spechtModule μ) (spechtModule ν) := by
  exact FDRep.characterProjectorLinear_idempotent _ _

/-- Projectors with distinct Specht labels have zero product on every
symmetric-group representation. -/
theorem spechtCharacterProjectorLinear_comp_eq_zero_of_ne {n : ℕ}
    {μ ν : YoungDiagramOfSize n} (hμν : μ ≠ ν) (V : SymmetricGroupRepresentation n) :
    (FDRep.characterProjectorLinear (spechtModule μ) V).comp
        (FDRep.characterProjectorLinear (spechtModule ν) V) = 0 := by
  apply FDRep.characterProjectorLinear_comp_eq_zero_of_not_iso
  intro h
  exact hμν ((spechtModule_iso_iff_eq μ ν).mp h)
