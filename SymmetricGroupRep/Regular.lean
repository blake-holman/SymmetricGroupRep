import SymmetricGroupRep.Classification
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RepresentationTheory.Basic

/-! # Regular representations of symmetric groups

The character of the left-regular representation counts fixed points of left
multiplication, so it is the order of the group at `1` and zero elsewhere. Paired
against any other character it therefore returns a dimension, which is the
multiplicity input to the regular decomposition. -/

open CategoryTheory

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

/-- The regular character: left multiplication by `g` fixes a basis vector only when `g = 1`, and
then it fixes all of them. -/
theorem symmetricGroupLeftRegular_character (n : ℕ) (g : SymmetricGroup n) :
    (symmetricGroupLeftRegular n).character g =
      if g = 1 then (Fintype.card (SymmetricGroup n) : ℂ) else 0 := by
  have hsingle : ∀ x : SymmetricGroup n,
      Representation.leftRegular ℂ (SymmetricGroup n) g (Finsupp.single x 1) =
        Finsupp.single (g * x) (1 : ℂ) := fun x => Representation.ofMulAction_single g x 1
  have htrace : (symmetricGroupLeftRegular n).character g =
      Matrix.trace (LinearMap.toMatrix (Finsupp.basisSingleOne (ι := SymmetricGroup n) (R := ℂ))
        Finsupp.basisSingleOne (Representation.leftRegular ℂ (SymmetricGroup n) g)) :=
    LinearMap.trace_eq_matrix_trace ℂ _ _
  rw [htrace]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, hsingle,
    Finsupp.single_apply, mul_eq_right]
  split <;> simp

/-- Every representation occurs in the left-regular representation with multiplicity its own
dimension: the character pairing collapses to the single term at `g = 1`. -/
theorem finrank_hom_symmetricGroupLeftRegular (n : ℕ) (V : SymmetricGroupRepresentation n) :
    Module.finrank ℂ (V ⟶ symmetricGroupLeftRegular n) = Module.finrank ℂ V := by
  have hsum : ∑ g : SymmetricGroup n,
      (symmetricGroupLeftRegular n).character g * V.character g⁻¹ =
        (Fintype.card (SymmetricGroup n) : ℂ) * Module.finrank ℂ V := by
    rw [Finset.sum_eq_single (1 : SymmetricGroup n)]
    · rw [symmetricGroupLeftRegular_character, if_pos rfl, inv_one, FDRep.char_one]
    · intro b _ hb
      rw [symmetricGroupLeftRegular_character, if_neg hb, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have h := FDRep.scalar_product_char_eq_finrank_equivariant V (symmetricGroupLeftRegular n)
  rw [hsum, smul_eq_mul, invOf_mul_cancel_left] at h
  exact_mod_cast h.symm
