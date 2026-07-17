import SymmetricGroupRep.Classification
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic

open CategoryTheory
open scoped BigOperators Classical

/-! # Character projectors -/

namespace FDRep

/-- The normalized character projector associated to a simple `W`, acting on `V`.

The normalization and inverse in the character are those of the standard
central idempotent formula over `ℂ`. -/
noncomputable def characterProjectorLinear {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] : V →ₗ[ℂ] V :=
  ((Module.finrank ℂ W : ℂ) / Fintype.card G) •
    ∑ g : G, W.character g⁻¹ • V.ρ g

/-- The character projector commutes with the action of the group. -/
theorem characterProjectorLinear_comm {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] (h : G) :
    (characterProjectorLinear W V).comp (V.ρ h) =
      (V.ρ h).comp (characterProjectorLinear W V) := by
  ext v
  simp only [characterProjectorLinear, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv
  intro g
  rw [show (MulAut.conj h⁻¹).toEquiv g = h⁻¹ * g * h by
    change MulAut.conj h⁻¹ g = _
    rw [MulAut.conj_apply, inv_inv]]
  simp only [mul_inv_rev, inv_inv, ← mul_assoc]
  congr 1
  · simpa only [inv_inv] using (FDRep.char_conj W g⁻¹ h⁻¹).symm
  · rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    rw [show g * h = h * (h⁻¹ * g * h) by group]

/-- The character projector as an equivariant endomorphism of `V`. -/
noncomputable def characterProjector {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] : V ⟶ V :=
  FDRep.forget₂HomLinearEquiv V V
    (Rep.ofHom ⟨characterProjectorLinear W V,
      characterProjectorLinear_comm W V⟩)

/-- The underlying linear map of `characterProjector`. -/
@[simp]
theorem characterProjector_hom_hom_hom {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] :
    (characterProjector W V).hom.hom.hom = characterProjectorLinear W V :=
  rfl

/-- Trace of the character projector before applying character orthogonality. -/
theorem trace_characterProjectorLinear {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] :
    LinearMap.trace ℂ V (characterProjectorLinear W V) =
      (Module.finrank ℂ W : ℂ) / Fintype.card G *
        ∑ g : G, W.character g⁻¹ * V.character g := by
  simp [characterProjectorLinear, FDRep.character]

/-- On simple representations, the projector trace is determined by whether
the two representations are isomorphic. -/
theorem trace_characterProjectorLinear_simple {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] [Simple V] :
    LinearMap.trace ℂ V (characterProjectorLinear W V) =
      (Module.finrank ℂ W : ℂ) *
        (if Nonempty (V ≅ W) then 1 else 0) := by
  rw [trace_characterProjectorLinear]
  have h := FDRep.char_orthonormal V W
  simp only [invOf_eq_inv, smul_eq_mul] at h
  have hsum : (∑ g : G, W.character g⁻¹ * V.character g) =
      ∑ g : G, V.character g * W.character g⁻¹ := by
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_comm]
  rw [hsum, div_eq_mul_inv, mul_assoc, h]

private theorem simple_finrank_pos {G : Type} [Group G]
    (V : FDRep ℂ G) [Simple V] : 0 < Module.finrank ℂ V := by
  have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.mp fun hs => by
    letI := hs
    apply CategoryTheory.id_nonzero V
    ext v
    exact Subsingleton.elim _ _
  letI := hnt
  exact Module.finrank_pos

/-- A character projector is the identity on an isomorphic simple summand and
zero on every other simple summand. -/
theorem characterProjector_eq {G : Type} [Group G] [Fintype G]
    (W V : FDRep ℂ G) [Simple W] [Simple V] :
    characterProjector W V =
      if Nonempty (V ≅ W) then 𝟙 V else 0 := by
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ
    (characterProjector W V)
  have htrace := congrArg
    (fun f : V ⟶ V => LinearMap.trace ℂ V f.hom.hom.hom) hc
  change LinearMap.trace ℂ V (c • (LinearMap.id : V →ₗ[ℂ] V)) =
    LinearMap.trace ℂ V (characterProjectorLinear W V) at htrace
  simp only [map_smul] at htrace
  rw [trace_characterProjectorLinear_simple] at htrace
  have hV : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (simple_finrank_pos V).ne'
  by_cases hVW : Nonempty (V ≅ W)
  · have hfin : Module.finrank ℂ W = Module.finrank ℂ V :=
      (FDRep.isoToLinearEquiv (Classical.choice hVW).symm).finrank_eq
    simp only [if_pos hVW] at htrace ⊢
    rw [hfin] at htrace
    have hc_one : c = 1 := by
      apply mul_right_cancel₀ hV
      simpa using htrace
    rw [← hc, hc_one, one_smul]
  · simp only [if_neg hVW] at htrace ⊢
    have hc_zero : c = 0 := by
      apply mul_right_cancel₀ hV
      simpa using htrace
    rw [← hc, hc_zero, zero_smul]

end FDRep

/-- The character projector labeled by `μ`, acting on `S^ν`. -/
noncomputable def spechtCharacterProjector {n : ℕ}
    (μ ν : YoungDiagramOfSize n) : spechtModule ν ⟶ spechtModule ν := by
  letI := spechtModule_irreducible μ
  exact FDRep.characterProjector (spechtModule μ) (spechtModule ν)

/-- The character projector labeled by `μ` acts as the identity precisely on
the Specht module with the same label. -/
theorem spechtCharacterProjector_eq {n : ℕ}
    (μ ν : YoungDiagramOfSize n) :
    spechtCharacterProjector μ ν =
      if μ = ν then 𝟙 (spechtModule ν) else 0 := by
  letI := spechtModule_irreducible μ
  letI := spechtModule_irreducible ν
  rw [spechtCharacterProjector]
  rw [FDRep.characterProjector_eq]
  simp [spechtModule_iso_iff_eq, eq_comm]
