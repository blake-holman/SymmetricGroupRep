import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Induced
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.TensorProduct.Finite

open CategoryTheory

universe u

namespace FDRep

variable {k G H : Type u} [Field k] [Group G] [Group H] [Finite H]

@[implicit_reducible]
private noncomputable def indVModuleFinite (φ : G →* H) (V : FDRep k G) :
    Module.Finite k (Representation.IndV φ
      ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ) := by
  letI : Module.Finite k (H →₀ k) := Module.Finite.finsupp
  letI : Module.Finite k ((forget₂ (FDRep k G) (Rep k G)).obj V) := by
    change Module.Finite k V
    infer_instance
  letI : Module.Finite k (TensorProduct k (H →₀ k)
      ((forget₂ (FDRep k G) (Rep k G)).obj V)) :=
    Module.Finite.tensorProduct k (H →₀ k)
      ((forget₂ (FDRep k G) (Rep k G)).obj V)
  exact Module.Finite.of_surjective (Representation.Coinvariants.mk _)
    (Representation.Coinvariants.mk_surjective _)

/-- Induction of a finite-dimensional representation along a homomorphism into a finite group. -/
noncomputable def ind (φ : G →* H) (V : FDRep k G) : FDRep k H :=
  letI := indVModuleFinite φ V
  FDRep.of (Representation.ind φ ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ)

@[simp]
theorem ind_ρ (φ : G →* H) (V : FDRep k G) :
    (ind φ V).ρ = Representation.ind φ V.ρ := by
  rfl

section

set_option maxHeartbeats 3200000

/-- A morphism of finite-dimensional representations induces a morphism between their
induced representations. -/
noncomputable def indMap (φ : G →* H) {V W : FDRep k G} (f : V ⟶ W) :
    ind φ V ⟶ ind φ W := by
  exact FDRep.forget₂HomLinearEquiv (ind φ V) (ind φ W)
    (Rep.indMap φ ((forget₂ (FDRep k G) (Rep k G)).map f))

variable (k) in
/-- Induction along a homomorphism into a finite group, as a functor on
finite-dimensional representations. -/
@[simps obj map]
noncomputable def indFunctor (φ : G →* H) : FDRep k G ⥤ FDRep k H := by
  exact
    { obj := fun V ↦ ind φ V
      map := fun f ↦ indMap φ f
      map_id := fun V ↦ by
        apply (FDRep.forget₂HomLinearEquiv (ind φ V) (ind φ V)).symm.injective
        simp [indMap]
        ext
        rfl
      map_comp := fun f g ↦ by
        apply (FDRep.forget₂HomLinearEquiv (ind φ _) (ind φ _)).symm.injective
        simp [indMap]
        ext
        rfl }

/-- Frobenius reciprocity for finite-dimensional representations: morphisms out of an
induced representation are equivalent to morphisms into the restricted representation. -/
noncomputable def indResHomEquiv (φ : G →* H) (V : FDRep k G) (W : FDRep k H) :
    (ind φ V ⟶ W) ≃ₗ[k]
      (V ⟶ (Action.res (FGModuleCat k) φ).obj W) := by
  exact (FDRep.forget₂HomLinearEquiv (ind φ V) W).symm |>.trans
    ((Rep.indResHomEquiv φ
      ((forget₂ (FDRep k G) (Rep k G)).obj V)
      ((forget₂ (FDRep k H) (Rep k H)).obj W)).trans
    (FDRep.forget₂HomLinearEquiv V ((Action.res (FGModuleCat k) φ).obj W)))

end

end FDRep
