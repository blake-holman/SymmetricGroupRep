import SymmetricGroupRep.Classification
import Mathlib.RepresentationTheory.Basic

/-! # Regular representations of symmetric groups -/

/-- The left-regular complex representation of `S_n`. -/
noncomputable def symmetricGroupLeftRegular (n : ℕ) :
    SymmetricGroupRepresentation n :=
  FDRep.of (Representation.leftRegular ℂ (SymmetricGroup n))

/-- A permutation acts on the standard group-algebra basis by left multiplication. -/
@[simp]
theorem symmetricGroupLeftRegular_ρ_single (n : ℕ)
    (g h : SymmetricGroup n) (c : ℂ) :
    (symmetricGroupLeftRegular n).ρ g (Finsupp.single h c) =
      Finsupp.single (g * h) c := by
  exact Representation.ofMulAction_single g h c
