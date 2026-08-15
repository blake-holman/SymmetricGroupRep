import SymmetricGroupRep.CharacterProjector
import SymmetricGroupRep.YoungPermutation
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Hermitian

open CategoryTheory
open scoped BigOperators Classical

/-! # Real character averages on permutation modules -/

namespace FDRep

/-- A real weighted average of a finite group action on a permutation module. -/
noncomputable def realGroupAverage {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) :
    MonoidAlgebra ℝ X →ₗ[ℝ] MonoidAlgebra ℝ X :=
  ∑ g : G, a g • Representation.ofMulAction ℝ G X g

/-- The same weighted average over the complex permutation module. -/
noncomputable def complexGroupAverage {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) :
    MonoidAlgebra ℂ X →ₗ[ℂ] MonoidAlgebra ℂ X :=
  ∑ g : G, (a g : ℂ) • Representation.ofMulAction ℂ G X g

@[simp]
theorem realGroupAverage_apply_single {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) (x : X) (r : ℝ) :
    realGroupAverage a (MonoidAlgebra.single x r) =
      ∑ h : G, MonoidAlgebra.single (h • x) (a h * r) := by
  simp [realGroupAverage, mul_comm]

@[simp]
theorem complexGroupAverage_apply_single {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) (x : X) (z : ℂ) :
    complexGroupAverage a (MonoidAlgebra.single x z) =
      ∑ h : G, MonoidAlgebra.single (h • x) (z * (a h : ℂ)) := by
  simp only [complexGroupAverage, LinearMap.sum_apply, LinearMap.smul_apply,
    Representation.ofMulAction_single, MonoidAlgebra.smul_single]
  apply Finset.sum_congr rfl
  intro h _
  simp [smul_eq_mul, mul_comm]

/-- The matrix of the complex average in the permutation basis. -/
noncomputable def complexGroupAverageMatrix {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) : Matrix X X ℂ :=
  fun y x => (complexGroupAverage a (MonoidAlgebra.single x 1)).coeff y

/-- The complex average has real entries in the permutation basis. -/
theorem complexGroupAverageMatrix_entry_im {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) (x y : X) :
    (complexGroupAverageMatrix a y x).im = 0 := by
  rw [complexGroupAverageMatrix, complexGroupAverage_apply_single]
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro h _
  by_cases hxy : h • x = y <;> simp [hxy]

/-- Inverse-invariant weights give a Hermitian matrix in the permutation basis. -/
theorem complexGroupAverageMatrix_isHermitian {G X : Type} [Group G] [Fintype G]
    [MulAction G X] (a : G → ℝ) (hinv : ∀ g : G, a g⁻¹ = a g) :
    (complexGroupAverageMatrix (G := G) (X := X) a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  rw [complexGroupAverageMatrix]
  rw [complexGroupAverageMatrix]
  rw [complexGroupAverage_apply_single, complexGroupAverage_apply_single]
  rw [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_apply']
  rw [star_sum]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  by_cases hxy : g • x = y
  · have hxy' : g⁻¹ • y = x := by
      rw [← hxy, inv_smul_smul]
    simp [hxy, hxy', hinv]
  · have hxy' : g⁻¹ • y ≠ x := by
      intro h
      apply hxy
      rw [← h, smul_inv_smul]
    simp [hxy, hxy']

/-- The real coefficient in the normalized character average. -/
noncomputable def characterProjectorRealWeight {G : Type} [Group G] [Fintype G]
    (W : FDRep ℂ G) (g : G) : ℝ :=
  (Module.finrank ℂ W : ℝ) / Fintype.card G * (W.character (g⁻¹)).re

/-- A character projector on a permutation module is the complexification of its
real group average whenever its character values are real. -/
theorem characterProjectorLinear_eq_complexGroupAverage {G X : Type} [Group G] [Fintype G]
    [MulAction G X] [Finite X] (W : FDRep ℂ G) [Simple W]
    (hreal : ∀ g : G, (W.character (g⁻¹)).im = 0) :
    characterProjectorLinear W (FDRep.of (Representation.ofMulAction ℂ G X)) =
      complexGroupAverage (characterProjectorRealWeight W) := by
  simp only [characterProjectorLinear, complexGroupAverage]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [smul_smul]
  congr 1
  rw [show W.character (g⁻¹) = ((W.character (g⁻¹)).re : ℂ) by
    apply Complex.ext
    · simp
    · simpa using hreal g]
  simp only [characterProjectorRealWeight]
  push_cast
  norm_cast

/-- The real weights of a symmetric-group character average are invariant under inversion. -/
theorem symmetricGroup_characterProjectorRealWeight_inv {n : ℕ}
    (W : SymmetricGroupRepresentation n) (g : SymmetricGroup n) :
    characterProjectorRealWeight W g⁻¹ = characterProjectorRealWeight W g := by
  simp only [characterProjectorRealWeight, inv_inv]
  rw [symmetricGroup_character_inv W g]

/-- The explicit real average associated to a Specht character is Hermitian in every
permutation basis. -/
theorem spechtCharacterProjectorRealAverage_isHermitian {n : ℕ}
    (μ : YoungDiagramOfSize n) (X : Type) [Finite X] [MulAction (SymmetricGroup n) X] :
    (complexGroupAverageMatrix (G := SymmetricGroup n) (X := X)
      (characterProjectorRealWeight (spechtModule μ))).IsHermitian :=
  complexGroupAverageMatrix_isHermitian _
    (symmetricGroup_characterProjectorRealWeight_inv (spechtModule μ))

/-- Under the real-character property, the Specht character projector on a Young
permutation module is exactly the complexification of the displayed real average. -/
theorem spechtCharacterProjectorLinear_eq_realAverage {n : ℕ}
    (μ ν : YoungDiagramOfSize n) [Simple (spechtModule μ)]
    (hreal : ∀ g : SymmetricGroup n, ((spechtModule μ).character (g⁻¹)).im = 0) :
    characterProjectorLinear (spechtModule μ) (youngPermutationModule ν) =
      complexGroupAverage (characterProjectorRealWeight (spechtModule μ)) := by
  exact characterProjectorLinear_eq_complexGroupAverage (W := spechtModule μ) hreal

end FDRep
