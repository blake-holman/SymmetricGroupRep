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

open scoped Classical in
/-- The coefficients of an alternant collect the permutations that carry the
exponent vector to the exponent read off. -/
theorem coeff_alt (α β : Fin N →₀ ℕ) :
    (alt α).coeff β =
      ∑ w : Equiv.Perm (Fin N),
        if Finsupp.mapDomain w α = β then (Equiv.Perm.sign w : ℤ) else 0 := by
  rw [alt, asym, coeff_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [rename_monomial, C_mul_monomial, mul_one, coeff_monomial]

private theorem apply_symm_eq {α : Fin N →₀ ℕ} {w : Equiv.Perm (Fin N)} {β : Fin N →₀ ℕ}
    (h : Finsupp.mapDomain w α = β) (x : Fin N) : α (w.symm x) = β x := by
  have hx : Finsupp.equivMapDomain w α x = β x := by
    rw [Finsupp.equivMapDomain_eq_mapDomain, h]
  rwa [Finsupp.equivMapDomain_apply] at hx

private theorem eq_one_of_symm_eq_one {w : Equiv.Perm (Fin N)} (h : w.symm = 1) : w = 1 := by
  rw [← Equiv.symm_symm w, h]
  rfl

/-- Only the identity fixes an exponent vector with distinct entries. -/
private theorem eq_one_of_mapDomain_eq {α : Fin N →₀ ℕ} (hα : Function.Injective ⇑α)
    {w : Equiv.Perm (Fin N)} (h : Finsupp.mapDomain w α = α) : w = 1 :=
  eq_one_of_symm_eq_one (Equiv.ext fun x => hα (apply_symm_eq h x))

/-- An exponent vector with distinct entries appears once in its own alternant. -/
theorem coeff_alt_self {α : Fin N →₀ ℕ} (hα : Function.Injective ⇑α) : (alt α).coeff α = 1 := by
  classical
  rw [coeff_alt]
  rw [Finset.sum_eq_single 1 (fun w _ hw => if_neg fun h => hw (eq_one_of_mapDomain_eq hα h))
    fun h => absurd (Finset.mem_univ (1 : Equiv.Perm (Fin N))) h]
  rw [if_pos (show Finsupp.mapDomain (1 : Equiv.Perm (Fin N)) α = α by simp)]
  simp

/-- An increasing permutation of a finite linear order is the identity. -/
private theorem perm_eq_one_of_strictMono {w : Equiv.Perm (Fin N)} (hw : StrictMono w) : w = 1 := by
  have hsymm : StrictMono w.symm := fun x y hxy => by
    by_contra hcon
    exact absurd (hw.monotone (not_lt.mp hcon)) (by simpa using not_le.mpr hxy)
  refine Equiv.ext fun i => le_antisymm ?_ hw.le_apply
  simpa using hw.monotone (hsymm.le_apply (x := i))

/-- A strictly decreasing exponent vector is determined by the multiset of its
entries: a permutation carrying one to another is the identity. -/
theorem eq_of_mapDomain_eq {α β : Fin N →₀ ℕ} (hα : StrictAnti ⇑α) (hβ : StrictAnti ⇑β)
    {w : Equiv.Perm (Fin N)} (h : Finsupp.mapDomain w α = β) : α = β := by
  have hmono : StrictMono ⇑w.symm := fun x y hxy => by
    refine (StrictAnti.lt_iff_gt hα).mp ?_
    rw [apply_symm_eq h, apply_symm_eq h]
    exact hβ hxy
  rw [eq_one_of_symm_eq_one (perm_eq_one_of_strictMono hmono)] at h
  simpa using (Finsupp.mapDomain_id (v := α)).symm.trans h

/-- Distinct strictly decreasing exponent vectors do not meet in their
alternants. -/
theorem coeff_alt_of_ne {α β : Fin N →₀ ℕ} (hα : StrictAnti ⇑α) (hβ : StrictAnti ⇑β)
    (hne : α ≠ β) : (alt α).coeff β = 0 := by
  classical
  rw [coeff_alt]
  exact Finset.sum_eq_zero fun w _ => if_neg fun h => hne (eq_of_mapDomain_eq hα hβ h)

/-- An alternant with distinct exponents is not zero. -/
theorem alt_ne_zero {α : Fin N →₀ ℕ} (hα : Function.Injective ⇑α) : alt α ≠ 0 := fun h => by
  have hone := coeff_alt_self hα
  rw [h, coeff_zero] at hone
  exact zero_ne_one hone

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
