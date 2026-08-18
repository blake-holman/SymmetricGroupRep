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
    (symmetricGroupLeftRegular n).ρ g (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (g * h) c := by
  exact Representation.ofMulAction_single g h c

/-- The regular character: left multiplication by `g` fixes a basis vector only when `g = 1`, and
then it fixes all of them. -/
theorem symmetricGroupLeftRegular_character (n : ℕ) (g : SymmetricGroup n) :
    (symmetricGroupLeftRegular n).character g =
      if g = 1 then (Fintype.card (SymmetricGroup n) : ℂ) else 0 := by
  have hsingle : ∀ x : SymmetricGroup n,
      Representation.leftRegular ℂ (SymmetricGroup n) g (MonoidAlgebra.single x 1) =
        MonoidAlgebra.single (g * x) (1 : ℂ) :=
    fun x => Representation.ofMulAction_single g x 1
  have htrace : (symmetricGroupLeftRegular n).character g =
      Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis (SymmetricGroup n) ℂ)
        (MonoidAlgebra.basis (SymmetricGroup n) ℂ)
        (Representation.leftRegular ℂ (SymmetricGroup n) g)) :=
    LinearMap.trace_eq_matrix_trace ℂ _ _
  rw [htrace]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    MonoidAlgebra.basis_apply, hsingle]
  change (∑ x : SymmetricGroup n, (MonoidAlgebra.single (g * x) (1 : ℂ)).coeff x) = _
  by_cases hg : g = 1
  · subst g
    simp
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro x _
    simp [hg]

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
  rw [hsum, Fintype.card_eq_nat_card] at h
  have hcard : (Nat.card (SymmetricGroup n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  field_simp [hcard] at h
  exact_mod_cast h.symm
