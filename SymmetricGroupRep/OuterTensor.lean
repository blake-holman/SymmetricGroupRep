import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero

open CategoryTheory

universe u

namespace FDRep

variable {k G H : Type u} [Field k]

section Monoid

variable [Monoid G] [Monoid H]

/-- The outer tensor product of representations of `G` and `H`, regarded as a
representation of `G × H`. -/
noncomputable def outerTensor (V : FDRep k G) (W : FDRep k H) : FDRep k (G × H) :=
  FDRep.of (Representation.tprod (V.ρ.comp (MonoidHom.fst G H))
    (W.ρ.comp (MonoidHom.snd G H)))

@[simp]
theorem outerTensor_ρ (V : FDRep k G) (W : FDRep k H) (g : G) (h : H) :
    (outerTensor V W).ρ (g, h) = TensorProduct.map (V.ρ g) (W.ρ h) :=
  rfl

@[simp]
theorem outerTensor_ρ_tmul (V : FDRep k G) (W : FDRep k H)
    (g : G) (h : H) (v : V) (w : W) :
    (outerTensor V W).ρ (g, h) (v ⊗ₜ[k] w) = V.ρ g v ⊗ₜ[k] W.ρ h w := by
  rfl

@[simp]
theorem outerTensor_character (V : FDRep k G) (W : FDRep k H) (g : G) (h : H) :
    (outerTensor V W).character (g, h) = V.character g * W.character h := by
  exact LinearMap.trace_tensorProduct' (V.ρ g) (W.ρ h)

end Monoid

section Simple

variable [Group G] [Group H] [Fintype G] [Fintype H] [IsAlgClosed k] [CharZero k]

/-- The outer tensor product of two simple representations of finite groups over an
algebraically closed field of characteristic zero is simple. -/
theorem simple_outerTensor (V : FDRep k G) (W : FDRep k H) [Simple V] [Simple W] :
    Simple (outerTensor V W) := by
  apply (FDRep.simple_iff_char_is_norm_one (outerTensor V W)).mpr
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ (g : G) (h : H), (g, h)⁻¹ = (g⁻¹, h⁻¹) by
      intro g h
      rfl,
    outerTensor_character]
  calc
    ∑ g : G, ∑ h : H,
        (V.character g * W.character h) *
          (V.character g⁻¹ * W.character h⁻¹) =
        ∑ g : G, (V.character g * V.character g⁻¹) *
          ∑ h : H, W.character h * W.character h⁻¹ := by
            apply Finset.sum_congr rfl
            intro g _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro h _
            ring
    _ = (∑ g : G, V.character g * V.character g⁻¹) *
          ∑ h : H, W.character h * W.character h⁻¹ := by
            rw [Finset.sum_mul]
    _ = Nat.card (G × H) := by
            rw [(FDRep.simple_iff_char_is_norm_one V).mp inferInstance,
              (FDRep.simple_iff_char_is_norm_one W).mp inferInstance,
              Nat.card_prod, Nat.cast_mul]

end Simple

end FDRep
