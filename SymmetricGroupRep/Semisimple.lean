import SymmetricGroupRep.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Maschke semisimplicity, and symmetric-group characters

Mathlib's Maschke-derived instances — `IsSemisimpleModule` over the group
algebra, and `Injective` and `Projective` in `FDRep` — are all gated on
`NeZero (Nat.card G : k)`, which does not synthesise on its own. Supplying it
once here, for every finite group, makes complete reducibility available
throughout the package; the symmetric groups and their products are both used.

Two character facts about `FDRep ℂ (S_n)` that mathlib leaves to its callers are
recorded here as well: the character of the rigid dual, and the invariance of
every symmetric-group character under inversion.
-/

open CategoryTheory
open scoped MonoidalCategory

/-- The order of a finite group is nonzero in `ℂ`, which is the hypothesis every Maschke-derived
instance is gated on. -/
noncomputable instance finiteGroupCardNeZero (G : Type) [Group G] [Finite G] :
    NeZero (Nat.card G : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- The order of a finite group is invertible in `ℂ`, in the `Fintype.card` form that mathlib's
character-pairing lemmas ask for. -/
noncomputable instance finiteGroupCardInvertible (G : Type) [Group G] [Fintype G] :
    Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

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

/-- Every symmetric-group element is conjugate to its inverse. -/
theorem symmetricGroup_inverse_isConj {n : ℕ} (g : SymmetricGroup n) :
    IsConj g⁻¹ g :=
  Equiv.Perm.isConj_of_cycleType_eq (Equiv.Perm.cycleType_inv g)

/-- A symmetric-group character is invariant under inversion. -/
theorem symmetricGroup_character_inv {n : ℕ} (V : SymmetricGroupRepresentation n)
    (g : SymmetricGroup n) : V.character (g⁻¹) = V.character g := by
  obtain ⟨h, hh⟩ := (isConj_iff.1 (symmetricGroup_inverse_isConj g))
  calc
    V.character (g⁻¹) = V.character (h * g⁻¹ * h⁻¹) := (FDRep.char_conj V (g⁻¹) h).symm
    _ = V.character g := by rw [hh]
