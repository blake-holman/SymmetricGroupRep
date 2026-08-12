import SymmetricGroupRep.Bialternant

/-! # The product of two Schur polynomials

Stembridge's lemma spreads `a_{κ+ρ} · s_λ` over the tableaux of shape `λ` that
are good for `κ`, and the bialternant formula rewrites `a_{κ+ρ}` and every
summand as a staircase alternant times a Schur polynomial.  Cancelling the
staircase alternant leaves the product rule: `s_κ · s_λ` is the sum of the Schur
polynomials of the shapes obtained by lengthening the rows of `κ` by the weight
of a good tableau.

See Stembridge, *A concise proof of the Littlewood-Richardson rule*, Electronic
Journal of Combinatorics 9 (2002), N5, and Grinberg-Reiner, *Hopf Algebras in
Combinatorics*, Corollary 2.6.11.
-/

open Finset

/-- Sorting the cells by their entry counts them by weight. -/
theorem BoundedSemistandardTableau.sum_weight {N : ℕ} {lam : YoungDiagram}
    (T : BoundedSemistandardTableau N lam) :
    ∑ i ∈ Finset.range N, T.tableau.weight i = lam.card := by
  classical
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise
    (f := fun cell : ℕ × ℕ => T.tableau cell.1 cell.2) (t := Finset.range N)
    fun cell hcell => Finset.mem_range.mpr (T.entry_lt cell hcell)]
  exact Finset.sum_congr rfl fun v _ => rfl

namespace Stembridge

open BoundedSemistandardTableau MvPolynomial

variable {N : ℕ} {kap lam : YoungDiagram} {T : BoundedSemistandardTableau N lam}

/-- Goodness for the rows of `kap` says exactly that lengthening those rows by
the weight of `T` keeps them decreasing. -/
theorem rowLen_add_weight_antitone (hgood : IsGood kap.rowLen T) {i j : ℕ} (hij : i ≤ j)
    (hj : j < N) :
    kap.rowLen j + T.tableau.weight j ≤ kap.rowLen i + T.tableau.weight i := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ n ih =>
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · refine le_trans ?_ (ih (by omega) (by omega))
      have hstep : ¬ prof kap.rowLen T 0 n ≤ prof kap.rowLen T 0 (n + 1) :=
        fun hcon => hgood 0 ⟨n, hj, hcon⟩
      simp only [prof_zero] at hstep
      omega

/-- The shape whose rows are the rows of `kap` lengthened by the weight of `T`.
Such a shape exists exactly when those lengths decrease, which is what goodness
provides; the value in the remaining case is never read. -/
noncomputable def addWeight (kap : YoungDiagram) (T : BoundedSemistandardTableau N lam) :
    YoungDiagram :=
  if h : ∀ i j : Fin N, i ≤ j →
      kap.rowLen j + T.tableau.weight j ≤ kap.rowLen i + T.tableau.weight i then
    (exists_youngDiagram_rowLen (fun i : Fin N => kap.rowLen i + T.tableau.weight i) h).choose
  else kap

private theorem addWeight_spec (hgood : IsGood kap.rowLen T) :
    (addWeight kap T).colLen 0 ≤ N ∧
      ∀ i : Fin N, (addWeight kap T).rowLen i = kap.rowLen i + T.tableau.weight i := by
  have h : ∀ i j : Fin N, i ≤ j →
      kap.rowLen j + T.tableau.weight j ≤ kap.rowLen i + T.tableau.weight i :=
    fun i j hij => rowLen_add_weight_antitone hgood hij j.isLt
  rw [addWeight, dif_pos h]
  exact (exists_youngDiagram_rowLen (fun i : Fin N => kap.rowLen i + T.tableau.weight i)
    h).choose_spec

theorem colLen_addWeight (hgood : IsGood kap.rowLen T) : (addWeight kap T).colLen 0 ≤ N :=
  (addWeight_spec hgood).1

theorem rowLen_addWeight (hgood : IsGood kap.rowLen T) (i : Fin N) :
    (addWeight kap T).rowLen i = kap.rowLen i + T.tableau.weight i :=
  (addWeight_spec hgood).2 i

open scoped Classical in
/-- **The product rule for Schur polynomials.**  `s_κ · s_λ` sums the Schur
polynomials of the shapes `κ + wt T` over the tableaux `T` of shape `λ` that are
good for `κ`. -/
theorem schurPoly_mul_schurPoly (hkap : kap.colLen 0 ≤ N) :
    schurPoly N kap * schurPoly N lam =
      ∑ T ∈ univ.filter (fun T : BoundedSemistandardTableau N lam => IsGood kap.rowLen T),
        schurPoly N (addWeight kap T) := by
  refine mul_left_cancel₀ alt_staircase_ne_zero ?_
  rw [← mul_assoc, alt_staircase_mul_schurPoly hkap,
    alt_mul_schurPoly_eq_sum_isGood fun i => kap.rowLen_anti i (i + 1) (Nat.le_succ i),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hgood := (mem_filter.mp hT).2
  rw [alt_staircase_mul_schurPoly (colLen_addWeight hgood)]
  congr 1
  ext i
  rw [expo_apply, expo_apply, prof_zero, rowLen_addWeight hgood]
  omega

/-- Lengthening the rows of `kap` by the weight of `T` adds the two sizes. -/
theorem card_addWeight (hgood : IsGood kap.rowLen T) (hkap : kap.colLen 0 ≤ N) :
    (addWeight kap T).card = kap.card + lam.card := by
  rw [YoungDiagram.card_eq_sum_rowLen (colLen_addWeight hgood),
    YoungDiagram.card_eq_sum_rowLen hkap, ← T.sum_weight, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    rowLen_addWeight hgood ⟨i, Finset.mem_range.mp hi⟩

/-- The tableaux of shape `lam` that are good for `kap` and lengthen its rows to
`xi`.  This is Stembridge's index set for the Littlewood-Richardson coefficient
`c^xi_{kap,lam}`. -/
noncomputable def stembridgeCount {a b : ℕ} (kap : YoungDiagramOfSize a)
    (lam : YoungDiagramOfSize b) (xi : YoungDiagramOfSize (a + b)) : ℕ :=
  Nat.card {T : BoundedSemistandardTableau (a + b) lam.val //
    IsGood kap.val.rowLen T ∧ addWeight kap.val T = xi.val}

open scoped Classical in
/-- **The product rule collected by shape.**  Grouping the good tableaux by the
shape they produce turns the product rule into a sum over shapes. -/
theorem schurPoly_mul_schurPoly_eq_sum {a b : ℕ} (kap : YoungDiagramOfSize a)
    (lam : YoungDiagramOfSize b) :
    schurPoly (a + b) kap.val * schurPoly (a + b) lam.val =
      ∑ xi : YoungDiagramOfSize (a + b),
        C (stembridgeCount kap lam xi : ℤ) * schurPoly (a + b) xi.val := by
  have hkap : kap.val.colLen 0 ≤ a + b :=
    le_trans (YoungDiagramOfSize.colLen_zero_le kap) (Nat.le_add_right a b)
  have hfib : ∀ xi : YoungDiagramOfSize (a + b),
      C (stembridgeCount kap lam xi : ℤ) * schurPoly (a + b) xi.val =
        ∑ T ∈ univ.filter (fun T : BoundedSemistandardTableau (a + b) lam.val =>
          IsGood kap.val.rowLen T ∧ addWeight kap.val T = xi.val),
          schurPoly (a + b) (addWeight kap.val T) := by
    intro xi
    have hconst : ∀ T ∈ univ.filter (fun T : BoundedSemistandardTableau (a + b) lam.val =>
        IsGood kap.val.rowLen T ∧ addWeight kap.val T = xi.val),
        schurPoly (a + b) (addWeight kap.val T) = schurPoly (a + b) xi.val :=
      fun T hT => by rw [(mem_filter.mp hT).2.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, stembridgeCount,
      Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul, map_natCast]
  rw [schurPoly_mul_schurPoly hkap, Finset.sum_congr rfl fun xi (_ : xi ∈ univ) => hfib xi]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : IsGood kap.val.rowLen T
  · rw [Finset.sum_eq_single_of_mem
      (⟨addWeight kap.val T, by rw [card_addWeight hT hkap, kap.2, lam.2]⟩ :
        YoungDiagramOfSize (a + b)) (Finset.mem_univ _)
      fun xi _ hne => if_neg fun hc => hne (Subtype.ext hc.2.symm),
      if_pos (And.intro hT rfl), if_pos hT]
  · simp [hT]

end Stembridge
