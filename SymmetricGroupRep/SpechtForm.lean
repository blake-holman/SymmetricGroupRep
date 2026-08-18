import SymmetricGroupRep.ContentEigenvalue

/-! # The invariant form on a Specht module

The Specht module inherits the Hermitian tabloid form, which is positive
definite and invariant under the group. Transpositions are their own inverses,
so they are self-adjoint, and so are the Jucys–Murphy operators. Joint
eigenvectors of the Jucys–Murphy operators with different integer eigenvalue
tuples are therefore orthogonal, and a nonzero vector has a positive length.
-/

/-- A Specht vector as an element of the Young permutation module. -/
noncomputable def spechtInclusion {n : ℕ} (μ : YoungDiagramOfSize n) :
    spechtModule μ →ₗ[ℂ] MonoidAlgebra ℂ (Tabloid μ) :=
  (spechtSubrepresentation μ).toSubmodule.subtype

theorem spechtInclusion_injective {n : ℕ} (μ : YoungDiagramOfSize n) :
    Function.Injective (spechtInclusion μ) :=
  Subtype.val_injective

theorem spechtInclusion_rho {n : ℕ} (μ : YoungDiagramOfSize n) (g : SymmetricGroup n)
    (v : spechtModule μ) :
    spechtInclusion μ ((spechtModule μ).ρ g v) =
      Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g (spechtInclusion μ v) :=
  rfl

/-- The invariant Hermitian form on `S^μ`, restricted from the tabloid form. -/
noncomputable def spechtForm {n : ℕ} {μ : YoungDiagramOfSize n} (x y : spechtModule μ) : ℂ :=
  tabloidForm (spechtInclusion μ x) (spechtInclusion μ y)

namespace spechtForm

variable {n : ℕ} {μ : YoungDiagramOfSize n}

@[simp]
theorem zero_left (y : spechtModule μ) : spechtForm 0 y = 0 := by
  rw [spechtForm, map_zero, tabloidForm_zero_left]

@[simp]
theorem zero_right (x : spechtModule μ) : spechtForm x 0 = 0 := by
  rw [spechtForm, map_zero, tabloidForm_zero_right]

theorem smul_left (c : ℂ) (x y : spechtModule μ) :
    spechtForm (c • x) y = c * spechtForm x y := by
  rw [spechtForm, spechtForm, map_smul, tabloidForm_smul_left]

theorem smul_right (c : ℂ) (x y : spechtModule μ) :
    spechtForm x (c • y) = (starRingEnd ℂ) c * spechtForm x y := by
  rw [spechtForm, spechtForm, map_smul, tabloidForm_smul_right]

theorem add_left (x y z : spechtModule μ) :
    spechtForm (x + y) z = spechtForm x z + spechtForm y z := by
  rw [spechtForm, spechtForm, spechtForm, map_add, tabloidForm_add_left]

theorem add_right (x y z : spechtModule μ) :
    spechtForm x (y + z) = spechtForm x y + spechtForm x z := by
  rw [spechtForm, spechtForm, spechtForm, map_add, tabloidForm_add_right]

theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → spechtModule μ) (y : spechtModule μ) :
    spechtForm (∑ i ∈ s, f i) y = ∑ i ∈ s, spechtForm (f i) y := by
  rw [spechtForm, map_sum, tabloidForm_sum_left]
  rfl

theorem sum_right {ι : Type*} (x : spechtModule μ) (s : Finset ι) (f : ι → spechtModule μ) :
    spechtForm x (∑ i ∈ s, f i) = ∑ i ∈ s, spechtForm x (f i) := by
  rw [spechtForm, map_sum, tabloidForm_sum_right]
  rfl

/-- The group acts by isometries. -/
theorem rho (g : SymmetricGroup n) (x y : spechtModule μ) :
    spechtForm ((spechtModule μ).ρ g x) ((spechtModule μ).ρ g y) = spechtForm x y := by
  rw [spechtForm, spechtForm, spechtInclusion_rho, spechtInclusion_rho, tabloidForm_ofMulAction]

/-- A permutation moves across the form by inverting. -/
theorem rho_left (g : SymmetricGroup n) (x y : spechtModule μ) :
    spechtForm ((spechtModule μ).ρ g x) y = spechtForm x ((spechtModule μ).ρ g⁻¹ y) := by
  rw [spechtForm, spechtForm, spechtInclusion_rho, spechtInclusion_rho,
    tabloidForm_ofMulAction_left]

/-- Transpositions are self-adjoint. -/
theorem swap (a b : Fin n) (x y : spechtModule μ) :
    spechtForm ((spechtModule μ).ρ (Equiv.swap a b) x) y =
      spechtForm x ((spechtModule μ).ρ (Equiv.swap a b) y) := by
  rw [rho_left, Equiv.swap_inv]

/-- The Jucys–Murphy operators are self-adjoint. -/
theorem jucysMurphy (k : Fin n) (x y : spechtModule μ) :
    spechtForm (_root_.jucysMurphy (spechtModule μ) k x) y =
      spechtForm x (_root_.jucysMurphy (spechtModule μ) k y) := by
  rw [jucysMurphy_apply, jucysMurphy_apply, sum_left, sum_right]
  exact Finset.sum_congr rfl fun j _ => swap j k x y

theorem eq_zero_of_self_eq_zero {x : spechtModule μ} (h : spechtForm x x = 0) : x = 0 :=
  spechtInclusion_injective μ (eq_zero_of_tabloidForm_self_eq_zero h)

theorem self_eq_ofReal (x : spechtModule μ) :
    spechtForm x x = ((spechtForm x x).re : ℂ) :=
  tabloidForm_self_eq_ofReal _

theorem self_re_nonneg (x : spechtModule μ) : 0 ≤ (spechtForm x x).re :=
  tabloidForm_self_re_nonneg _

end spechtForm

/-- The length of a Specht vector for the invariant form. -/
noncomputable def spechtNorm {n : ℕ} {μ : YoungDiagramOfSize n} (x : spechtModule μ) : ℝ :=
  Real.sqrt (spechtForm x x).re

namespace spechtNorm

variable {n : ℕ} {μ : YoungDiagramOfSize n}

theorem nonneg (x : spechtModule μ) : 0 ≤ spechtNorm x := Real.sqrt_nonneg _

theorem sq (x : spechtModule μ) : spechtForm x x = ((spechtNorm x ^ 2 : ℝ) : ℂ) := by
  rw [spechtNorm, Real.sq_sqrt (spechtForm.self_re_nonneg x), ← spechtForm.self_eq_ofReal]

theorem eq_zero_iff {x : spechtModule μ} : spechtNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    refine spechtForm.eq_zero_of_self_eq_zero ?_
    rw [sq, h]
    norm_num
  · rintro rfl
    rw [spechtNorm]
    simp [spechtForm, spechtInclusion]

theorem pos {x : spechtModule μ} (h : x ≠ 0) : 0 < spechtNorm x :=
  lt_of_le_of_ne (nonneg x) fun hzero => h (eq_zero_iff.mp hzero.symm)

end spechtNorm

/-- **Joint eigenvectors with different eigenvalue tuples are orthogonal.** -/
theorem spechtForm_eq_zero_of_jucysMurphy_ne {n : ℕ} {μ : YoungDiagramOfSize n}
    {x y : spechtModule μ} {α β : Fin n → ℤ}
    (hx : ∀ k, jucysMurphy (spechtModule μ) k x = (α k : ℂ) • x)
    (hy : ∀ k, jucysMurphy (spechtModule μ) k y = (β k : ℂ) • y)
    (hne : α ≠ β) : spechtForm x y = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have hstep : (α k : ℂ) * spechtForm x y = (β k : ℂ) * spechtForm x y := by
    rw [← spechtForm.smul_left, ← hx k, spechtForm.jucysMurphy, hy k, spechtForm.smul_right]
    simp
  have hcoef : ((α k : ℂ) - (β k : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr fun h => hk (by exact_mod_cast h)
  exact (mul_eq_zero.mp (by rw [sub_mul, hstep, sub_self])).resolve_left hcoef
