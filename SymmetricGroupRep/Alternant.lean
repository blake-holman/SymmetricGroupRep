import SymmetricGroupRep.SchurPolynomial

/-! # Alternants

Antisymmetrising a monomial gives an alternant.  Alternants change sign when the
exponent vector is permuted, so they vanish when it repeats a value, and a
symmetric factor passes through the antisymmetriser.
-/

namespace MvPolynomial

variable {N : ℕ}

/-- Antisymmetrisation over the variables. -/
noncomputable def asym (p : MvPolynomial (Fin N) ℤ) : MvPolynomial (Fin N) ℤ :=
  ∑ w : Equiv.Perm (Fin N), C (Equiv.Perm.sign w : ℤ) * rename w p

theorem asym_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin N) ℤ) :
    asym (∑ i ∈ s, f i) = ∑ i ∈ s, asym (f i) := by
  simp only [asym, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- A symmetric factor passes through the antisymmetriser. -/
theorem asym_mul_isSymmetric {s : MvPolynomial (Fin N) ℤ} (hs : s.IsSymmetric)
    (p : MvPolynomial (Fin N) ℤ) : asym (p * s) = asym p * s := by
  rw [asym, asym, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, hs w, mul_assoc]

private theorem sign_mul_sign_mul (σ w : Equiv.Perm (Fin N)) :
    (Equiv.Perm.sign w : ℤ) = (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign (w * σ) : ℤ) := by
  rw [map_mul, Units.val_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num

/-- Renaming the variables of an antisymmetrised polynomial multiplies it by the
sign of the renaming. -/
theorem asym_rename (σ : Equiv.Perm (Fin N)) (p : MvPolynomial (Fin N) ℤ) :
    asym (rename σ p) = C (Equiv.Perm.sign σ : ℤ) * asym p := by
  rw [asym, asym, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight σ)
    (fun w => C (Equiv.Perm.sign w : ℤ) * rename ⇑w (rename ⇑σ p))
    (fun w => C (Equiv.Perm.sign σ : ℤ) * (C (Equiv.Perm.sign w : ℤ) * rename ⇑w p)) fun w => ?_
  show C (Equiv.Perm.sign w : ℤ) * rename ⇑w (rename ⇑σ p) =
    C (Equiv.Perm.sign σ : ℤ) * (C (Equiv.Perm.sign (w * σ) : ℤ) * rename ⇑(w * σ) p)
  rw [rename_rename, show (⇑w ∘ ⇑σ : Fin N → Fin N) = ⇑(w * σ) from rfl, ← mul_assoc, ← map_mul,
    ← sign_mul_sign_mul]

/-- The alternant of an exponent vector. -/
noncomputable def alt (α : Fin N →₀ ℕ) : MvPolynomial (Fin N) ℤ := asym (monomial α 1)

theorem alt_mapDomain (σ : Equiv.Perm (Fin N)) (α : Fin N →₀ ℕ) :
    alt (Finsupp.mapDomain σ α) = C (Equiv.Perm.sign σ : ℤ) * alt α := by
  rw [alt, alt, ← rename_monomial, asym_rename]

/-- Transposing two exponents negates an alternant. -/
theorem alt_mapDomain_swap {α : Fin N →₀ ℕ} {i j : Fin N} (hij : i ≠ j) :
    alt (Finsupp.mapDomain (Equiv.swap i j) α) = -alt α := by
  rw [alt_mapDomain, Equiv.Perm.sign_swap hij]
  simp

/-- The polynomial ring over the integers has no two-torsion. -/
theorem eq_zero_of_eq_neg {p : MvPolynomial (Fin N) ℤ} (h : p = -p) : p = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  have hcoeff := congrArg (MvPolynomial.coeff m) h
  rw [MvPolynomial.coeff_neg] at hcoeff
  rw [MvPolynomial.coeff_zero]
  omega

/-- An alternant with a repeated exponent vanishes. -/
theorem alt_eq_zero_of_eq {α : Fin N →₀ ℕ} {i j : Fin N} (hij : i ≠ j) (h : α i = α j) :
    alt α = 0 := by
  have hmap : Finsupp.mapDomain (Equiv.swap i j) α = α := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    ext x
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap]
    rcases eq_or_ne x i with rfl | hx
    · rw [Equiv.swap_apply_left]
      exact h.symm
    rcases eq_or_ne x j with rfl | hx'
    · rw [Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  refine eq_zero_of_eq_neg ?_
  conv_lhs => rw [← hmap, alt_mapDomain_swap hij]

/-- Multiplying an alternant by a Schur polynomial spreads it over the tableaux
of the shape. -/
theorem alt_mul_schurPoly (κ : Fin N →₀ ℕ) (lam : YoungDiagram) :
    alt κ * schurPoly N lam =
      ∑ T : BoundedSemistandardTableau N lam, alt (κ + T.weight) := by
  simp only [alt]
  rw [← asym_mul_isSymmetric schurPoly_isSymmetric, schurPoly, Finset.mul_sum, asym_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [monomial_mul, mul_one]

end MvPolynomial
