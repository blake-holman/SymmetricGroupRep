import SymmetricGroupRep.ColumnSplit

/-! # Stembridge's sign-reversing involution

Stembridge's proof of the Littlewood-Richardson rule multiplies an alternant by a
Schur polynomial and cancels the contributions of the tableaux that are not
*good* for the exponent vector.  The cancelling involution applies the
Bender-Knuth involution to an initial block of columns; the block and the value
are read off from the last column at which goodness fails.

See Stembridge, *A concise proof of the Littlewood-Richardson rule*, Electronic
Journal of Combinatorics 9 (2002), N5, and Grinberg-Reiner, *Hopf Algebras in
Combinatorics*, Theorem 2.6.6.
-/

open Finset

/-- Reading a function on `ℕ` as an exponent vector in `N` variables. -/
noncomputable def expo (N : ℕ) (f : ℕ → ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Fin N => f i

@[simp]
theorem expo_apply (N : ℕ) (f : ℕ → ℕ) (i : Fin N) : expo N f i = f i := rfl

namespace BoundedSemistandardTableau

variable {N : ℕ} {lam : YoungDiagram}

/-- The restriction of a bounded tableau to its first `j` columns. -/
def restrictCols (T : BoundedSemistandardTableau N lam) (j : ℕ) :
    BoundedSemistandardTableau N (lam.truncCols j) where
  tableau := T.tableau.restrictCols j
  entry_lt := fun cell hcell => by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_truncCols] at hcell
    show (if cell.2 < j then T.tableau cell.1 cell.2 else 0) < N
    rw [if_pos hcell.2]
    exact T.entry_lt cell hcell.1

/-- Gluing a bounded tableau on the first `j` columns to one on the whole shape. -/
def glueCols {j : ℕ} (S : BoundedSemistandardTableau N (lam.truncCols j))
    (T : BoundedSemistandardTableau N lam)
    (hb : ∀ r c, c < j → (r, j) ∈ lam → S.tableau r c ≤ T.tableau r j) :
    BoundedSemistandardTableau N lam where
  tableau := SemistandardYoungTableau.glueCols S.tableau T.tableau hb
  entry_lt := fun cell hcell => by
    show (if cell.2 < j then S.tableau cell.1 cell.2 else T.tableau cell.1 cell.2) < N
    split_ifs with h
    · exact S.entry_lt cell (YoungDiagram.mem_truncCols.mpr ⟨hcell, h⟩)
    · exact T.entry_lt cell hcell

/-- Column `j` carrying no `k` is what makes the two blocks of the Stembridge
swap glue together. -/
theorem swapAt_boundary (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) (r c : ℕ) (hc : c < j)
    (hcell : (r, j) ∈ lam) : ((T.restrictCols j).bk hk).tableau r c ≤ T.tableau r j := by
  show (T.tableau.restrictCols j).bkEntry k r c ≤ T.tableau r j
  have hrestrict : (T.tableau.restrictCols j) r c = T.tableau r c := if_pos hc
  have hrow : T.tableau r c ≤ T.tableau r j := T.tableau.row_weak_of_le (by omega) hcell
  rcases eq_or_ne ((T.tableau.restrictCols j).bkEntry k r c)
    ((T.tableau.restrictCols j) r c) with heq | hne
  · rw [heq, hrestrict]
    exact hrow
  · have h1 := SemistandardYoungTableau.le_entry_of_bkEntry_ne hne
    have h2 := SemistandardYoungTableau.bkEntry_le_succ_of_ne hne
    have h3 := hcol r hcell
    rw [hrestrict] at h1
    omega

/-- The Stembridge swap: the Bender-Knuth involution at `k` applied to the first
`j` columns. -/
def swapAt (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) : BoundedSemistandardTableau N lam :=
  glueCols ((T.restrictCols j).bk hk) T (swapAt_boundary T j k hk hcol)

theorem swapAt_apply (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) (r c : ℕ) :
    (T.swapAt j k hk hcol).tableau r c =
      if c < j then (T.tableau.restrictCols j).bkEntry k r c else T.tableau r c := rfl

theorem swapAt_col (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) (r : ℕ) :
    (T.swapAt j k hk hcol).tableau r j = T.tableau r j := by
  rw [swapAt_apply, if_neg (show ¬ j < j by omega)]

theorem colWeight_swapAt (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) {j' : ℕ} (hj : j ≤ j') (v : ℕ) :
    (T.swapAt j k hk hcol).tableau.colWeight j' v = T.tableau.colWeight j' v :=
  SemistandardYoungTableau.colWeight_glueCols _ _ (swapAt_boundary T j k hk hcol) hj v

theorem swapAt_swapAt (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k)
    (U : BoundedSemistandardTableau N lam) (hU : U = T.swapAt j k hk hcol)
    (hcolU : ∀ r, (r, j) ∈ lam → U.tableau r j ≠ k) :
    U.swapAt j k hk hcolU = T := by
  subst hU
  ext r c
  rw [swapAt_apply]
  rcases lt_or_ge c j with hc | hc
  · rw [if_pos hc, show (T.swapAt j k hk hcol).tableau.restrictCols j =
      (T.tableau.restrictCols j).benderKnuth k from
      SemistandardYoungTableau.restrictCols_glueCols _ _ (swapAt_boundary T j k hk hcol)]
    have hinv := congrFun (congrFun (congrArg DFunLike.coe
      (SemistandardYoungTableau.benderKnuth_benderKnuth
        (T := T.tableau.restrictCols j) (k := k))) r) c
    rw [show ((T.tableau.restrictCols j).benderKnuth k).bkEntry k r c =
      (((T.tableau.restrictCols j).benderKnuth k).benderKnuth k) r c from rfl, hinv,
      SemistandardYoungTableau.restrictCols_apply, if_pos hc]
  · rw [if_neg (show ¬ c < j by omega), swapAt_apply, if_neg (show ¬ c < j by omega)]

/-- The value the Bender-Knuth involution at `k` exchanges with `v`. -/
def swapVal (k v : ℕ) : ℕ := if v = k then k + 1 else if v = k + 1 then k else v

@[simp]
theorem swapVal_self (k : ℕ) : swapVal k k = k + 1 := if_pos rfl

@[simp]
theorem swapVal_succ (k : ℕ) : swapVal k (k + 1) = k := by
  rw [swapVal, if_neg (show ¬ k + 1 = k by omega), if_pos rfl]

theorem swapVal_of_ne {k v : ℕ} (h1 : v ≠ k) (h2 : v ≠ k + 1) : swapVal k v = v := by
  simp only [swapVal, if_neg h1, if_neg h2]

theorem weight_swapAt (T : BoundedSemistandardTableau N lam) (j k : ℕ) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) (v : ℕ) :
    (T.swapAt j k hk hcol).tableau.weight v =
      (T.tableau.restrictCols j).weight (swapVal k v) + T.tableau.colWeight j v := by
  rw [show (T.swapAt j k hk hcol).tableau =
    SemistandardYoungTableau.glueCols ((T.tableau.restrictCols j).benderKnuth k) T.tableau
      (swapAt_boundary T j k hk hcol) from rfl, SemistandardYoungTableau.weight_glueCols]
  congr 1
  rcases eq_or_ne v k with rfl | hv
  · rw [swapVal_self]
    exact SemistandardYoungTableau.weight_benderKnuth_self
  rcases eq_or_ne v (k + 1) with rfl | hv1
  · rw [swapVal_succ]
    exact SemistandardYoungTableau.weight_benderKnuth_succ
  · rw [swapVal_of_ne hv hv1]
    exact SemistandardYoungTableau.weight_benderKnuth_of_ne hv hv1

end BoundedSemistandardTableau

namespace Stembridge

open BoundedSemistandardTableau MvPolynomial

variable {N : ℕ} {lam : YoungDiagram} (κ : ℕ → ℕ)

/-- The exponent profile carried by the columns from `j` on, shifted by the
staircase. -/
def prof (T : BoundedSemistandardTableau N lam) (j i : ℕ) : ℕ :=
  κ i + (N - 1 - i) + T.tableau.colWeight j i

/-- Column `j` witnesses a failure of goodness. -/
def Fails (T : BoundedSemistandardTableau N lam) (j : ℕ) : Prop :=
  ∃ i, i + 1 < N ∧ prof κ T j i ≤ prof κ T j (i + 1)

/-- A tableau is good for `κ` when every column suffix keeps the profile strictly
decreasing. -/
def IsGood (T : BoundedSemistandardTableau N lam) : Prop := ∀ j, ¬ Fails κ T j

variable {κ}

theorem prof_zero (T : BoundedSemistandardTableau N lam) (i : ℕ) :
    prof κ T 0 i = κ i + (N - 1 - i) + T.tableau.weight i := by
  simp only [prof, SemistandardYoungTableau.colWeight_zero]

theorem prof_succ (T : BoundedSemistandardTableau N lam) (j i : ℕ) :
    prof κ T j i = prof κ T (j + 1) i + T.tableau.colCell j i := by
  have h := T.tableau.colWeight_succ j i
  simp only [prof]
  omega

theorem lt_rowLen_of_fails (hκ : ∀ i, κ (i + 1) ≤ κ i)
    {T : BoundedSemistandardTableau N lam} {j : ℕ} (h : Fails κ T j) : j < lam.rowLen 0 := by
  by_contra hcon
  obtain ⟨i, hi, hle⟩ := h
  have h0 := T.tableau.colWeight_eq_zero (j := j) (by omega) i
  have h1 := T.tableau.colWeight_eq_zero (j := j) (by omega) (i + 1)
  have h2 := hκ i
  simp only [prof, h0, h1] at hle
  omega

/-- The swap moves the profile of the whole tableau by the transposition. -/
theorem prof_swapAt (T : BoundedSemistandardTableau N lam) {j k : ℕ} (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k)
    (heq : prof κ T j k = prof κ T j (k + 1)) (v : ℕ) :
    prof κ (T.swapAt j k hk hcol) 0 v = prof κ T 0 (swapVal k v) := by
  have hkey : prof κ T j v = prof κ T j (swapVal k v) := by
    rcases eq_or_ne v k with rfl | hv
    · rw [swapVal_self]
      exact heq
    rcases eq_or_ne v (k + 1) with rfl | hv1
    · rw [swapVal_succ]
      exact heq.symm
    · rw [swapVal_of_ne hv hv1]
  simp only [prof] at hkey
  rw [prof_zero, prof_zero, weight_swapAt,
    T.tableau.weight_eq_restrictCols_add_colWeight j (swapVal k v)]
  omega

open scoped Classical in
/-- The last column at which goodness fails. -/
noncomputable def failCol (f : ℕ → ℕ) (T : BoundedSemistandardTableau N lam) : ℕ :=
  Nat.findGreatest (Fails f T) (lam.rowLen 0)

/-- The first value at which the profile of `failCol` fails to decrease. -/
noncomputable def failRow (f : ℕ → ℕ) (T : BoundedSemistandardTableau N lam) : ℕ :=
  sInf {i | i + 1 < N ∧ prof f T (failCol f T) i ≤ prof f T (failCol f T) (i + 1)}

open scoped Classical in
theorem fails_failCol (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) : Fails κ T (failCol κ T) := by
  obtain ⟨j, hj⟩ := not_forall.mp hbad
  exact Nat.findGreatest_spec (P := Fails κ T)
    (le_of_lt (lt_rowLen_of_fails hκ (not_not.mp hj))) (not_not.mp hj)

open scoped Classical in
theorem not_fails_of_gt (hκ : ∀ i, κ (i + 1) ≤ κ i) (T : BoundedSemistandardTableau N lam)
    {j : ℕ} (hj : failCol κ T < j) : ¬ Fails κ T j := by
  rcases le_or_gt j (lam.rowLen 0) with hle | hgt
  · exact Nat.findGreatest_is_greatest hj hle
  · exact fun h => absurd (lt_rowLen_of_fails hκ h) (by omega)

theorem failRow_spec (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) :
    failRow κ T + 1 < N ∧
      prof κ T (failCol κ T) (failRow κ T) ≤ prof κ T (failCol κ T) (failRow κ T + 1) :=
  Nat.sInf_mem (fails_failCol hκ hbad)

/-- The anatomy of a bad tableau: at the last failing column the profile is
constant across the failing step, and that column carries no `failRow`. -/
theorem failCol_anatomy (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) :
    prof κ T (failCol κ T) (failRow κ T) = prof κ T (failCol κ T) (failRow κ T + 1) ∧
      T.tableau.colCell (failCol κ T) (failRow κ T) = 0 := by
  obtain ⟨hk, hle⟩ := failRow_spec hκ hbad
  have hstrict : prof κ T (failCol κ T + 1) (failRow κ T + 1) <
      prof κ T (failCol κ T + 1) (failRow κ T) := by
    by_contra hcon
    exact not_fails_of_gt (j := failCol κ T + 1) hκ T (by omega) ⟨failRow κ T, hk, by omega⟩
  have h1 := prof_succ (κ := κ) T (failCol κ T) (failRow κ T)
  have h2 := prof_succ (κ := κ) T (failCol κ T) (failRow κ T + 1)
  have h3 := T.tableau.colCell_le_one (failCol κ T) (failRow κ T)
  have h4 := T.tableau.colCell_le_one (failCol κ T) (failRow κ T + 1)
  omega

theorem col_ne_failRow (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) (r : ℕ) (hr : (r, failCol κ T) ∈ lam) :
    T.tableau r (failCol κ T) ≠ failRow κ T :=
  (T.tableau.colCell_eq_zero_iff _ _).mp (failCol_anatomy hκ hbad).2 r hr

open scoped Classical in
/-- The cancelling involution on the tableaux that are not good. -/
noncomputable def swapBad (f : ℕ → ℕ) (T : BoundedSemistandardTableau N lam) :
    BoundedSemistandardTableau N lam :=
  if h : failRow f T + 1 < N ∧
      ∀ r, (r, failCol f T) ∈ lam → T.tableau r (failCol f T) ≠ failRow f T then
    T.swapAt (failCol f T) (failRow f T) h.1 h.2
  else T

open scoped Classical in
theorem swapBad_eq {T : BoundedSemistandardTableau N lam} {j k : ℕ} (hj : j = failCol κ T)
    (hkk : k = failRow κ T) (hk : k + 1 < N)
    (hcol : ∀ r, (r, j) ∈ lam → T.tableau r j ≠ k) :
    swapBad κ T = T.swapAt j k hk hcol := by
  subst hj
  subst hkk
  exact dif_pos ⟨hk, hcol⟩

theorem prof_swapBad_of_le (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) {j : ℕ} (hj : failCol κ T ≤ j) (i : ℕ) :
    prof κ (swapBad κ T) j i = prof κ T j i := by
  rw [swapBad_eq rfl rfl (failRow_spec hκ hbad).1 (col_ne_failRow hκ hbad)]
  simp only [prof, colWeight_swapAt _ _ _ _ _ hj]

open scoped Classical in
theorem failCol_swapBad (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) : failCol κ (swapBad κ T) = failCol κ T := by
  have hfail : Fails κ (swapBad κ T) (failCol κ T) := by
    obtain ⟨i, hi, hle⟩ := fails_failCol hκ hbad
    exact ⟨i, hi, by
      rw [prof_swapBad_of_le hκ hbad le_rfl, prof_swapBad_of_le hκ hbad le_rfl]
      exact hle⟩
  show Nat.findGreatest (Fails κ (swapBad κ T)) (lam.rowLen 0) = failCol κ T
  refine Nat.findGreatest_eq_iff.mpr ⟨Nat.findGreatest_le _, fun _ => hfail, ?_⟩
  rintro n hn _ ⟨i, hi, hle⟩
  refine not_fails_of_gt hκ T hn ⟨i, hi, ?_⟩
  rwa [← prof_swapBad_of_le hκ hbad (by omega), ← prof_swapBad_of_le hκ hbad (by omega)]

theorem failRow_swapBad (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) : failRow κ (swapBad κ T) = failRow κ T := by
  show sInf {i | i + 1 < N ∧ prof κ (swapBad κ T) (failCol κ (swapBad κ T)) i ≤
    prof κ (swapBad κ T) (failCol κ (swapBad κ T)) (i + 1)} = failRow κ T
  rw [failCol_swapBad hκ hbad]
  congr 1
  ext i
  simp only [Set.mem_setOf_eq, prof_swapBad_of_le hκ hbad le_rfl]

theorem not_isGood_swapBad (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) : ¬ IsGood κ (swapBad κ T) := by
  obtain ⟨i, hi, hle⟩ := fails_failCol hκ hbad
  intro hgood
  exact hgood (failCol κ T) ⟨i, hi, by
    rw [prof_swapBad_of_le hκ hbad le_rfl, prof_swapBad_of_le hκ hbad le_rfl]
    exact hle⟩

theorem swapBad_swapBad (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) : swapBad κ (swapBad κ T) = T := by
  have hk := (failRow_spec hκ hbad).1
  have hcol := col_ne_failRow hκ hbad
  have h1 : swapBad κ T = T.swapAt (failCol κ T) (failRow κ T) hk hcol :=
    swapBad_eq rfl rfl hk hcol
  have hcol2 : ∀ r, (r, failCol κ T) ∈ lam →
      (swapBad κ T).tableau r (failCol κ T) ≠ failRow κ T := by
    intro r hr
    rw [h1, swapAt_col]
    exact hcol r hr
  rw [swapBad_eq (failCol_swapBad hκ hbad).symm (failRow_swapBad hκ hbad).symm hk hcol2]
  exact swapAt_swapAt T _ _ hk hcol _ h1 hcol2

/-- The involution transposes the two failing exponents, so it reverses the sign
of the alternant. -/
theorem alt_swapBad (hκ : ∀ i, κ (i + 1) ≤ κ i) {T : BoundedSemistandardTableau N lam}
    (hbad : ¬ IsGood κ T) :
    alt (expo N (prof κ (swapBad κ T) 0)) = -alt (expo N (prof κ T 0)) := by
  obtain ⟨hk, -⟩ := failRow_spec hκ hbad
  have hne : (⟨failRow κ T, by omega⟩ : Fin N) ≠ ⟨failRow κ T + 1, hk⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  rw [← alt_mapDomain_swap (α := expo N (prof κ T 0)) hne,
    ← Finsupp.equivMapDomain_eq_mapDomain]
  congr 1
  ext i
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap, expo_apply, expo_apply,
    swapBad_eq rfl rfl hk (col_ne_failRow hκ hbad),
    prof_swapAt _ _ _ (failCol_anatomy hκ hbad).1]
  congr 1
  rcases eq_or_ne i (⟨failRow κ T, by omega⟩ : Fin N) with rfl | hi
  · rw [Equiv.swap_apply_left]
    exact swapVal_self _
  rcases eq_or_ne i (⟨failRow κ T + 1, hk⟩ : Fin N) with rfl | hi1
  · rw [Equiv.swap_apply_right]
    exact swapVal_succ _
  · rw [Equiv.swap_apply_of_ne_of_ne hi hi1]
    exact swapVal_of_ne (fun h => hi (Fin.ext h)) (fun h => hi1 (Fin.ext h))

open scoped Classical in
/-- The tableaux that are not good contribute nothing. -/
theorem sum_alt_not_isGood (hκ : ∀ i, κ (i + 1) ≤ κ i) :
    ∑ T ∈ univ.filter (fun T : BoundedSemistandardTableau N lam => ¬ IsGood κ T),
      alt (expo N (prof κ T 0)) = 0 := by
  refine Finset.sum_involution (fun T _ => swapBad κ T) (fun T hT => ?_) (fun T hT hne => ?_)
    (fun T hT => ?_) (fun T hT => ?_)
  · rw [alt_swapBad hκ (mem_filter.mp hT).2]
    ring
  · intro hfix
    have hfix' : swapBad κ T = T := hfix
    have h := alt_swapBad hκ (mem_filter.mp hT).2
    rw [hfix'] at h
    exact hne (MvPolynomial.eq_zero_of_eq_neg h)
  · exact mem_filter.mpr ⟨mem_univ _, not_isGood_swapBad hκ (mem_filter.mp hT).2⟩
  · exact swapBad_swapBad hκ (mem_filter.mp hT).2

open scoped Classical in
/-- **Stembridge's lemma.**  Multiplying the alternant of `κ` shifted by the
staircase by a Schur polynomial leaves only the good tableaux. -/
theorem alt_mul_schurPoly_eq_sum_isGood (hκ : ∀ i, κ (i + 1) ≤ κ i) :
    alt (expo N fun i => κ i + (N - 1 - i)) * schurPoly N lam =
      ∑ T ∈ univ.filter (fun T : BoundedSemistandardTableau N lam => IsGood κ T),
        alt (expo N (prof κ T 0)) := by
  have hexpo : ∀ T : BoundedSemistandardTableau N lam,
      (expo N fun i => κ i + (N - 1 - i)) + T.weight = expo N (prof κ T 0) := by
    intro T
    ext i
    rw [Finsupp.add_apply, expo_apply, expo_apply, BoundedSemistandardTableau.weight_apply,
      prof_zero]
  rw [alt_mul_schurPoly]
  simp only [hexpo]
  rw [← Finset.sum_filter_add_sum_filter_not univ
    (fun T : BoundedSemistandardTableau N lam => IsGood κ T),
    sum_alt_not_isGood hκ, add_zero]

end Stembridge
