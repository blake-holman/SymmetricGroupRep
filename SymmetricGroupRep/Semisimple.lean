import SymmetricGroupRep.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Maschke

/-! # Maschke semisimplicity for symmetric groups

Mathlib's Maschke-derived instances — `IsSemisimpleModule` over the group
algebra, and `Injective` and `Projective` in `FDRep` — are all gated on
`NeZero (Nat.card G : k)`, which does not synthesise on its own. Supplying it
once here makes complete reducibility available throughout the package.
-/

open CategoryTheory

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
