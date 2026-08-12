import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # The Vandermonde product of a decreasing vector

The hook-length formula and the hook-content formula are both proved in
first-column coordinates, where the shape of a diagram is recorded by the
strictly decreasing vector of its first-column hook lengths. The algebra those
proofs need is the Vandermonde product of that vector: how it behaves when one
coordinate drops by one, the weighted sum of all such drops, and the sum of the
products of all shorter vectors that interlace it.

The weighted sum is Bandlow, *An elementary proof of the hook length formula*,
Electronic Journal of Combinatorics 15 (2008), R45, equation (4); it is proved
here by Lagrange interpolation, as Bandlow does. The interlacing sum is the
Weyl dimension formula read backwards, and is proved here by evaluating the
determinant of the Vandermonde matrix in the binomial-coefficient basis, where
summing a row over an interval telescopes.
-/

open Finset Polynomial

/-- The Vandermonde product of `b 0, ..., b (m - 1)`, taking each factor as an
earlier entry minus a later one. -/
def vanderDec (m : ℕ) (b : ℕ → ℚ) : ℚ :=
  ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (b i - b j)

theorem vanderDec_eq_zero_of_eq {m : ℕ} {b : ℕ → ℚ} {i j : ℕ} (hij : i < j) (hjm : j < m)
    (hb : b i = b j) : vanderDec m b = 0 :=
  Finset.prod_eq_zero (mem_range.mpr (hij.trans hjm))
    (Finset.prod_eq_zero (mem_Ico.mpr ⟨hij, hjm⟩) (sub_eq_zero_of_eq hb))

theorem vanderDec_ne_zero {m : ℕ} {b : ℕ → ℚ} (hb : Set.InjOn b (range m)) :
    vanderDec m b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [mem_range] at hi
  rw [mem_Ico] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  have := hb (mem_range.mpr hi) (mem_range.mpr hj.2) h
  omega

/-- The indices other than `i` below `m` are those before `i` and those after it. -/
theorem prod_erase_range_eq {m i : ℕ} (hi : i < m) (f : ℕ → ℚ) :
    ∏ j ∈ (range m).erase i, f j = (∏ p ∈ range i, f p) * ∏ q ∈ Ico (i + 1) m, f q := by
  have hsplit : (range m).erase i = range i ∪ Ico (i + 1) m := by
    ext p
    simp only [Finset.mem_erase, mem_range, Finset.mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range i) (Ico (i + 1) m) := by
    refine Finset.disjoint_left.mpr fun p hp hp' => ?_
    rw [mem_range] at hp
    rw [mem_Ico] at hp'
    omega
  rw [hsplit, Finset.prod_union hdisj]

/-- Splitting off the factors that involve the coordinate `i`. -/
theorem vanderDec_peel {m i : ℕ} (hi : i < m) (b : ℕ → ℚ) :
    vanderDec m b =
      ((∏ p ∈ range i, (b p - b i)) * ∏ q ∈ Ico (i + 1) m, (b i - b q)) *
        ∏ p ∈ (range m).erase i, ∏ q ∈ (Ico (p + 1) m).erase i, (b p - b q) := by
  have hrest : ∀ p ∈ (range m).erase i,
      ∏ q ∈ Ico (p + 1) m, (b p - b q) =
        (if p < i then b p - b i else 1) * ∏ q ∈ (Ico (p + 1) m).erase i, (b p - b q) := by
    intro p _
    by_cases hpi : p < i
    · rw [if_pos hpi]
      exact (Finset.mul_prod_erase _ _ (show i ∈ Ico (p + 1) m by
        simp only [mem_Ico]; omega)).symm
    · rw [if_neg hpi, Finset.erase_eq_of_notMem (by simp only [mem_Ico]; omega), one_mul]
  have hfront : ∏ p ∈ (range m).erase i, (if p < i then b p - b i else 1) =
      ∏ p ∈ range i, (b p - b i) := by
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, mem_range]
    omega
  rw [vanderDec, ← Finset.mul_prod_erase _ _ (mem_range.mpr hi),
    Finset.prod_congr rfl hrest, Finset.prod_mul_distrib, hfront]
  ring

/-- Lowering the coordinate `i` to `c` replaces the differences at `i`. -/
theorem vanderDec_update_mul_prod {m i : ℕ} (hi : i < m) (b : ℕ → ℚ) (c : ℚ) :
    vanderDec m (Function.update b i c) * ∏ j ∈ (range m).erase i, (b i - b j) =
      vanderDec m b * ∏ j ∈ (range m).erase i, (c - b j) := by
  have hne : ∀ p, p ≠ i → Function.update b i c p = b p := fun p hp =>
    Function.update_of_ne hp _ _
  have hself : Function.update b i c i = c := Function.update_self _ _ _
  have hupdate : vanderDec m (Function.update b i c) =
      ((∏ p ∈ range i, (b p - c)) * ∏ q ∈ Ico (i + 1) m, (c - b q)) *
        ∏ p ∈ (range m).erase i, ∏ q ∈ (Ico (p + 1) m).erase i, (b p - b q) := by
    rw [vanderDec_peel hi]
    congr 1
    · congr 1
      · exact Finset.prod_congr rfl fun p hp => by
          rw [hne p (by rw [mem_range] at hp; omega), hself]
      · exact Finset.prod_congr rfl fun q hq => by
          rw [hne q (by rw [mem_Ico] at hq; omega), hself]
    · refine Finset.prod_congr rfl fun p hp => Finset.prod_congr rfl fun q hq => ?_
      rw [hne p (Finset.mem_erase.mp hp).1, hne q (Finset.mem_erase.mp hq).1]
  have key : (∏ p ∈ range i, (b p - c)) * ∏ p ∈ range i, (b i - b p) =
      (∏ p ∈ range i, (b p - b i)) * ∏ p ∈ range i, (c - b p) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hupdate, vanderDec_peel hi, prod_erase_range_eq hi fun j => b i - b j,
    prod_erase_range_eq hi fun j => c - b j]
  set B := ∏ q ∈ Ico (i + 1) m, (c - b q)
  set D := ∏ q ∈ Ico (i + 1) m, (b i - b q)
  set R := ∏ p ∈ (range m).erase i, ∏ q ∈ (Ico (p + 1) m).erase i, (b p - b q)
  linear_combination B * D * R * key

/-- The second coefficient from the top of `∏ (X - b j)` is minus the sum of the
`b j`. -/
theorem coeff_nodal_range_sub_one (m : ℕ) (hm : 1 ≤ m) (b : ℕ → ℚ) :
    (Lagrange.nodal (range m) b).coeff (m - 1) = -∑ j ∈ range m, b j := by
  induction m, hm using Nat.le_induction with
  | base => simp [Lagrange.nodal_eq]
  | succ m hm ih =>
    have hmonic : (Lagrange.nodal (range m) b).coeff m = 1 := by
      have := (Lagrange.nodal_monic (s := range m) (v := b)).coeff_natDegree
      rwa [Lagrange.natDegree_nodal, card_range] at this
    have hstep : Lagrange.nodal (range (m + 1)) b =
        Lagrange.nodal (range m) b * (X - C (b m)) := by
      rw [Lagrange.nodal_eq, Lagrange.nodal_eq, Finset.prod_range_succ]
    have hindex : m + 1 - 1 = (m - 1) + 1 := by omega
    have hindex' : (m - 1) + 1 = m := by omega
    rw [hstep, hindex, Polynomial.coeff_mul_X_sub_C, ih, hindex', hmonic,
      Finset.sum_range_succ]
    ring

/-- Raising every root by one raises the third coefficient from the top by an
amount that involves only the sum of the roots. -/
theorem coeff_nodal_shift_sub (m : ℕ) (hm : 2 ≤ m) (b : ℕ → ℚ) :
    (Lagrange.nodal (range m) fun j => b j + 1).coeff (m - 2) -
        (Lagrange.nodal (range m) b).coeff (m - 2) =
      ((m : ℚ) - 1) * (∑ j ∈ range m, b j) + (m.choose 2 : ℚ) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Lagrange.nodal_eq, Lagrange.nodal_eq]
    simp [Finset.prod_range_succ, Finset.sum_range_succ]
    ring
  | succ m hm ih =>
    have hstep : ∀ c : ℕ → ℚ, Lagrange.nodal (range (m + 1)) c =
        Lagrange.nodal (range m) c * (X - C (c m)) := fun c => by
      rw [Lagrange.nodal_eq, Lagrange.nodal_eq, Finset.prod_range_succ]
    have htop := coeff_nodal_range_sub_one m (by omega) b
    have htopShift : (Lagrange.nodal (range m) fun j => b j + 1).coeff (m - 1) =
        -(∑ j ∈ range m, b j) - m := by
      rw [coeff_nodal_range_sub_one m (by omega)]
      simp only [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
      ring
    have hindex : m + 1 - 2 = (m - 2) + 1 := by omega
    have hindex' : (m - 2) + 1 = m - 1 := by omega
    have hchoose : ((m + 1).choose 2 : ℚ) = (m.choose 2 : ℚ) + m := by
      rw [Nat.choose_succ_succ' m 1]
      push_cast [Nat.choose_one_right]
      ring
    rw [hstep, hstep, hindex, Polynomial.coeff_mul_X_sub_C, Polynomial.coeff_mul_X_sub_C,
      hindex', htop, htopShift, Finset.sum_range_succ, hchoose]
    push_cast
    linear_combination ih

/-- Bandlow's identity: the sum over the coordinates of the Vandermonde product
with that coordinate lowered by one, weighted by the coordinate. -/
theorem sum_mul_vanderDec_update {m : ℕ} {b : ℕ → ℚ} (hb : Set.InjOn b (range m)) :
    ∑ i ∈ range m, b i * vanderDec m (Function.update b i (b i - 1)) =
      ((∑ i ∈ range m, b i) - (m.choose 2 : ℚ)) * vanderDec m b := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [vanderDec]
  set N := Lagrange.nodal (range m) b with hNdef
  set M := Lagrange.nodal (range m) (fun j => b j + 1) with hMdef
  set R := X * (M - N) + C (m : ℚ) * N with hRdef
  have hNtop : N.coeff (m - 1) = -∑ j ∈ range m, b j :=
    coeff_nodal_range_sub_one m (by omega) b
  have hMtop : M.coeff (m - 1) = -(∑ j ∈ range m, b j) - m := by
    rw [hMdef, coeff_nodal_range_sub_one m (by omega)]
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
    ring
  have hNdegree : N.degree = (m : ℕ) := by rw [hNdef, Lagrange.degree_nodal, card_range]
  have hNleading : N.coeff m = 1 := by
    have := (Lagrange.nodal_monic (s := range m) (v := b)).coeff_natDegree
    rwa [Lagrange.natDegree_nodal, card_range] at this
  have hdiff : (M - N).degree < (m : ℕ) := by
    have hMdegree : M.degree = N.degree := by
      rw [hMdef, hNdef, Lagrange.degree_nodal, Lagrange.degree_nodal]
    have := Polynomial.degree_sub_lt hMdegree Lagrange.nodal_ne_zero
      ((Lagrange.nodal_monic).trans (Lagrange.nodal_monic (s := range m) (v := b)).symm)
    rwa [hMdegree, hNdegree] at this
  have hdiffTop : (M - N).coeff (m - 1) = -(m : ℚ) := by
    rw [Polynomial.coeff_sub, hMtop, hNtop]; ring
  have hRdegree : R.degree < (#(range m) : ℕ) := by
    rw [card_range]
    refine (Polynomial.degree_lt_iff_coeff_zero R m).mpr fun k hk => ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hRdef, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le hk with heq | hlt
    · have hj' : j + 1 = m := by omega
      have hj : j = m - 1 := by omega
      rw [hj', hj, hdiffTop, hNleading]
      ring
    · have hj : m ≤ j := by omega
      rw [Polynomial.coeff_eq_zero_of_degree_lt (hdiff.trans_le (by exact_mod_cast hj)),
        Polynomial.coeff_eq_zero_of_degree_lt (n := j + 1)
          (by rw [hNdegree]; exact_mod_cast by omega)]
      ring
  have heval : ∀ i ∈ range m, R.eval (b i) =
      -(b i * ∏ j ∈ (range m).erase i, (b i - 1 - b j)) := by
    intro i hi
    have hMeval : M.eval (b i) = -∏ j ∈ (range m).erase i, (b i - 1 - b j) := by
      rw [hMdef, Lagrange.eval_nodal, ← Finset.mul_prod_erase _ _ hi]
      rw [Finset.prod_congr rfl fun j _ => (by ring : b i - (b j + 1) = b i - 1 - b j)]
      ring
    rw [hRdef]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, hNdef, Lagrange.eval_nodal_at_node hi, hMdef] at *
    rw [hMeval]
    ring
  have hRtop : R.coeff (m - 1) = (m.choose 2 : ℚ) - ∑ j ∈ range m, b j := by
    have hindex : m - 1 = (m - 2) + 1 := by omega
    rw [hRdef, Polynomial.coeff_add, hindex, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_sub, ← hindex, hNtop, hMdef, hNdef]
    linear_combination coeff_nodal_shift_sub m hm b
  have hlag := Lagrange.coeff_eq_sum hb hRdegree
  rw [card_range, hRtop] at hlag
  have hP : ∀ i ∈ range m, (∏ j ∈ (range m).erase i, (b i - b j)) ≠ 0 := by
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne fun h => ?_
    exact (Finset.mem_erase.mp hj).1 (hb (Finset.mem_of_mem_erase hj) hi h.symm)
  have hsum : ∑ i ∈ range m, b i * vanderDec m (Function.update b i (b i - 1)) =
      -(vanderDec m b * ∑ i ∈ range m,
        R.eval (b i) / ∏ j ∈ (range m).erase i, (b i - b j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hupd := vanderDec_update_mul_prod (mem_range.mp hi) b (b i - 1)
    have hPi := hP i hi
    rw [heval i hi]
    field_simp
    linear_combination b i * hupd
  rw [hsum, ← hlag]
  ring

/-- The Vandermonde product read as a product over `Fin m`. -/
theorem vanderDec_eq_prod_fin (m : ℕ) (b : ℕ → ℚ) :
    vanderDec m b = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (b i - b j) := by
  rw [vanderDec, ← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Ico (i + 1) m, (b i - b j)) m]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := Finset.prod_map (Finset.Ioi i) Fin.valEmbedding (fun j => b i - b j)
  rw [Fin.map_valEmbedding_Ioi, ← Finset.Ico_add_one_left_eq_Ioo] at this
  simpa using this

/-- Reversing the coordinates turns the decreasing convention into mathlib's
Vandermonde determinant, which takes each factor as a later entry minus an
earlier one. -/
private theorem prod_sub_eq_det_vandermonde {m : ℕ} (g : Fin m → ℚ) :
    ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (g i - g j) =
      (Matrix.vandermonde fun i => g i.rev).det := by
  rw [Matrix.det_vandermonde,
    Finset.prod_sigma' Finset.univ (fun i : Fin m => Finset.Ioi i) (fun i j => g i - g j),
    Finset.prod_sigma' Finset.univ (fun i : Fin m => Finset.Ioi i)
      (fun i j => g j.rev - g i.rev)]
  refine Finset.prod_nbij' (fun x => ⟨x.2.rev, x.1.rev⟩) (fun x => ⟨x.2.rev, x.1.rev⟩)
    ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual [Fin.rev_lt_rev]

/-- Summing a column of Pascal's triangle: the hockey-stick identity. -/
private theorem sum_range_choose_eq_choose_succ (n k : ℕ) :
    ∑ t ∈ range n, t.choose k = n.choose (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, Nat.add_comm]

/-- The Vandermonde determinant in the binomial-coefficient basis: the falling
factorials are monic of the right degrees, and column `j` then carries the
common factor `j !`. -/
private theorem det_vandermonde_eq_prod_factorial_mul_det_choose {m : ℕ} (v : Fin m → ℕ) :
    (Matrix.vandermonde fun i => (v i : ℚ)).det =
      (∏ j : Fin m, ((j : ℕ).factorial : ℚ)) *
        (Matrix.of fun i j : Fin m => ((v i).choose j : ℚ)).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i => ((v i : ℕ) : ℚ))
      (fun j => descPochhammer ℚ (j : ℕ)) (fun j => descPochhammer_natDegree ℚ (j : ℕ))
      (fun j => monic_descPochhammer ℚ (j : ℕ)),
    ← Matrix.det_mul_row (fun j : Fin m => ((j : ℕ).factorial : ℚ))]
  congr 1
  ext i j
  simp [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]

/-- Each row of the binomial matrix depends only on its own coordinate, so
summing the coordinates over independent ranges sums the rows. -/
private theorem sum_det_choose_eq_det_sum {q : ℕ} (A : Fin q → Finset ℕ) :
    ∑ δ ∈ Fintype.piFinset A, (Matrix.of fun i j : Fin q => ((δ i).choose j : ℚ)).det =
      (Matrix.of fun i j : Fin q => ∑ t ∈ A i, ((t.choose j : ℕ) : ℚ)).det := by
  have h := (Matrix.detRowAlternating (R := ℚ) (n := Fin q)).toMultilinearMap.map_sum_finset
    (fun (_ : Fin q) (t : ℕ) (j : Fin q) => ((t.choose (j : ℕ) : ℕ) : ℚ)) A
  have hrow : (fun i : Fin q => ∑ t ∈ A i, fun j : Fin q => ((t.choose (j : ℕ) : ℕ) : ℚ)) =
      (Matrix.of fun i j : Fin q => ∑ t ∈ A i, ((t.choose (j : ℕ) : ℕ) : ℚ)) := by
    funext i j
    simp [Finset.sum_apply]
  rw [hrow] at h
  exact h.symm

/-- Subtracting each row of the binomial matrix from the next one clears its
first column except at the top, and what is left is the matrix of differences
one size down. -/
private theorem det_choose_eq_det_choose_diff {q : ℕ} (c : ℕ → ℕ) :
    (Matrix.of fun i j : Fin (q + 1) => ((c i).choose j : ℚ)).det =
      (Matrix.of fun i j : Fin q =>
        ((c (i + 1)).choose (j + 1) : ℚ) - ((c i).choose (j + 1) : ℚ)).det := by
  set A : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
    Matrix.of fun i j => ((c i).choose j : ℚ) with hA
  set B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
    Matrix.of fun i j => Fin.cases (A 0 j) (fun i' => A i'.succ j - A i'.castSucc j) i with hB
  have hdet : A.det = B.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
      (fun j => by simp [hB]) (fun i j => by simp [hB])
  rw [hdet, Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, Fin.succAbove_zero, one_mul]
    rw [show B 0 0 = 1 by simp [hB, hA], one_mul]
    congr 1
  · intro i _ hi
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    simp [hB, hA]
  · simp

/-- The interlacing sum in mathlib's increasing convention. -/
private theorem factorial_mul_sum_det_vandermonde {q : ℕ} (c : ℕ → ℕ)
    (hc : ∀ i < q, c i ≤ c (i + 1)) :
    (q.factorial : ℚ) *
        ∑ δ ∈ Fintype.piFinset fun i : Fin q => Finset.Ico (c i) (c (i + 1)),
          (Matrix.vandermonde fun i => ((δ i : ℕ) : ℚ)).det =
      (Matrix.vandermonde fun i : Fin (q + 1) => ((c i : ℕ) : ℚ)).det := by
  have hN : (Matrix.of fun i j : Fin q =>
      ∑ t ∈ Finset.Ico (c i) (c (i + 1)), ((t.choose (j : ℕ) : ℕ) : ℚ)) =
      Matrix.of fun i j : Fin q =>
        ((c ((i : ℕ) + 1)).choose ((j : ℕ) + 1) : ℚ) - ((c i).choose ((j : ℕ) + 1) : ℚ) := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, Finset.sum_Ico_eq_sub _ (hc i i.isLt),
      ← Nat.cast_sum, ← Nat.cast_sum, sum_range_choose_eq_choose_succ,
      sum_range_choose_eq_choose_succ]
  rw [Finset.sum_congr rfl fun δ _ => det_vandermonde_eq_prod_factorial_mul_det_choose δ,
    ← Finset.mul_sum, sum_det_choose_eq_det_sum, hN,
    det_vandermonde_eq_prod_factorial_mul_det_choose (fun i : Fin (q + 1) => c i),
    det_choose_eq_det_choose_diff, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  ring

/-- The interlacing sum: for a decreasing vector `b` of length `q + 1`, the
Vandermonde products of the vectors of length `q` that interlace it add up,
after multiplication by `q !`, to the Vandermonde product of `b`.

This is the Weyl dimension formula for `GL q` at the identity, read as a
recursion in `q`. -/
theorem factorial_mul_sum_vanderDec {q : ℕ} (b : ℕ → ℕ) (hb : ∀ i < q, b (i + 1) ≤ b i) :
    (q.factorial : ℚ) *
        ∑ γ ∈ Fintype.piFinset fun i : Fin q => Finset.Ico (b (i + 1)) (b i),
          ∏ i : Fin q, ∏ j ∈ Finset.Ioi i, ((γ i : ℚ) - (γ j : ℚ)) =
      vanderDec (q + 1) fun i => (b i : ℚ) := by
  have hsum : ∑ γ ∈ Fintype.piFinset fun i : Fin q => Finset.Ico (b (i + 1)) (b i),
        (∏ i : Fin q, ∏ j ∈ Finset.Ioi i, ((γ i : ℚ) - (γ j : ℚ))) =
      ∑ δ ∈ Fintype.piFinset fun i : Fin q => Finset.Ico (b (q - i)) (b (q - (i + 1))),
        (Matrix.vandermonde fun i => ((δ i : ℕ) : ℚ)).det := by
    refine Finset.sum_nbij' (fun γ i => γ i.rev) (fun δ i => δ i.rev) ?_ ?_ ?_ ?_ ?_
    · intro γ hγ
      rw [Fintype.mem_piFinset] at hγ ⊢
      intro i
      have h := hγ i.rev
      rw [Finset.mem_Ico, Fin.val_rev, show q - ((i : ℕ) + 1) + 1 = q - (i : ℕ) from by omega] at h
      rw [Finset.mem_Ico]
      exact h
    · intro δ hδ
      rw [Fintype.mem_piFinset] at hδ ⊢
      intro i
      have h := hδ i.rev
      rw [Finset.mem_Ico, Fin.val_rev,
        show q - (q - ((i : ℕ) + 1)) = (i : ℕ) + 1 from by omega,
        show q - (q - ((i : ℕ) + 1) + 1) = (i : ℕ) from by omega] at h
      rw [Finset.mem_Ico]
      exact h
    · exact fun γ _ => funext fun i => by simp
    · exact fun δ _ => funext fun i => by simp
    · exact fun γ _ => prod_sub_eq_det_vandermonde fun i => (γ i : ℚ)
  have hc : ∀ i < q, b (q - i) ≤ b (q - (i + 1)) := by
    intro i hi
    rw [show q - i = q - (i + 1) + 1 from by omega]
    exact hb _ (by omega)
  have hvec : (fun i : Fin (q + 1) => ((b ((Fin.rev i : Fin (q + 1)) : ℕ) : ℕ) : ℚ)) =
      fun i : Fin (q + 1) => ((b (q - (i : ℕ)) : ℕ) : ℚ) := by
    funext i
    rw [Fin.val_rev, show q + 1 - ((i : ℕ) + 1) = q - (i : ℕ) from by omega]
  rw [hsum, factorial_mul_sum_det_vandermonde (fun i => b (q - i)) hc, vanderDec_eq_prod_fin,
    prod_sub_eq_det_vandermonde fun i : Fin (q + 1) => ((b i : ℕ) : ℚ), hvec]
