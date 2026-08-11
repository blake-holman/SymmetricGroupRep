import SymmetricGroupRep.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Maschke semisimplicity for symmetric groups

Mathlib's Maschke-derived instances — `IsSemisimpleModule` over the group
algebra, and `Injective` and `Projective` in `FDRep` — are all gated on
`NeZero (Nat.card G : k)`, which does not synthesise on its own. Supplying it
once here makes complete reducibility available throughout the package.

The character of the rigid dual is recorded here too, since it is the other
fact about `FDRep ℂ (S_n)` that mathlib leaves to its callers.
-/

open CategoryTheory
open scoped MonoidalCategory

noncomputable instance symmetricGroupCardNeZero (n : ℕ) :
    NeZero (Nat.card (SymmetricGroup n) : ℂ) := by
  refine ⟨?_⟩
  have hpos : 0 < Nat.card (SymmetricGroup n) := Nat.card_pos
  exact_mod_cast Nat.cast_ne_zero.mpr (by omega : Nat.card (SymmetricGroup n) ≠ 0)

/-- Maschke's theorem in the form the isotypic decomposition needs: every
subrepresentation of a finite-dimensional complex symmetric-group representation
is a direct summand, because every object of `FDRep ℂ (S_n)` is injective. -/
theorem SymmetricGroupRepresentation.exists_retraction {n : ℕ}
    {W V : SymmetricGroupRepresentation n} (f : W ⟶ V) [Mono f] :
    ∃ r : V ⟶ W, f ≫ r = 𝟙 W :=
  ⟨Injective.factorThru (𝟙 W) f, Injective.comp_factorThru (𝟙 W) f⟩

/-- Every monomorphism of symmetric-group representations splits. -/
noncomputable instance {n : ℕ} {W V : SymmetricGroupRepresentation n}
    (f : W ⟶ V) [Mono f] : IsSplitMono f :=
  IsSplitMono.mk' ⟨Injective.factorThru (𝟙 W) f, Injective.comp_factorThru (𝟙 W) f⟩

/-- The inclusion of a subrepresentation, as a morphism of finite-dimensional
representations.

This is the bridge between the submodule level, where mathlib's semisimplicity
API lives, and the `FDRep` level, where this package's statements live. -/
noncomputable def Subrepresentation.toFDRepHom {n : ℕ}
    (V : SymmetricGroupRepresentation n) (W : Subrepresentation V.ρ) :
    FDRep.of W.toRepresentation ⟶ V :=
  Action.Hom.mk (FGModuleCat.ofHom W.toSubmodule.subtype) (by
    intro g
    apply FGModuleCat.hom_ext
    ext w
    rfl)

instance {n : ℕ} (V : SymmetricGroupRepresentation n) (W : Subrepresentation V.ρ) :
    Mono (Subrepresentation.toFDRepHom V W) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Every subrepresentation is a direct summand: Maschke applied through the
inclusion. -/
theorem Subrepresentation.exists_retraction_toFDRepHom {n : ℕ}
    (V : SymmetricGroupRepresentation n) (W : Subrepresentation V.ρ) :
    ∃ r : V ⟶ FDRep.of W.toRepresentation,
      Subrepresentation.toFDRepHom V W ≫ r = 𝟙 _ :=
  SymmetricGroupRepresentation.exists_retraction _

/-- The character of the rigid dual `Vᘁ` at `g` is the character of `V` at `g⁻¹`.

Mathlib's `FDRep.char_dual` states this only for `FDRep.of (Representation.dual V.ρ)`,
and its own TODO records the omission. `Action.rightDual_ρ` identifies the action
of `Vᘁ` with the right adjoint mate of the action of `g⁻¹`, and
`rightAdjointMate_comp_evaluation` read at `x ⊗ₜ v` says that mate is the transpose. -/
theorem FDRep.char_rightDual {n : ℕ} (V : SymmetricGroupRepresentation n)
    (g : SymmetricGroup n) : (Vᘁ).character g = V.character g⁻¹ := by
  have hρ : (Vᘁ).ρ g = Module.Dual.transpose (V.ρ g⁻¹) := by
    rw [← FDRep.hom_hom_action_ρ Vᘁ g, Action.rightDual_ρ]
    exact LinearMap.ext fun x => LinearMap.ext fun v =>
      congrArg (fun m : V.Vᘁ ⊗ V.V ⟶ 𝟙_ (FGModuleCat ℂ) => m.hom.hom (x ⊗ₜ[ℂ] v))
        (rightAdjointMate_comp_evaluation (Action.ρ V g⁻¹))
  simp only [FDRep.character, hρ]
  exact LinearMap.trace_transpose' (V.ρ g⁻¹)
