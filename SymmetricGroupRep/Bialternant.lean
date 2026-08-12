import SymmetricGroupRep.Stembridge

/-! # The bialternant formula

Stembridge's lemma at `κ = 0` leaves a single good tableau, the one whose row `i`
consists of `i`s.  That turns the lemma into the classical bialternant formula
`a_ρ · s_λ = a_{λ + ρ}`.
-/

open Finset

namespace Stembridge

open BoundedSemistandardTableau MvPolynomial

variable {N : ℕ} {lam : YoungDiagram}

/-- The tableau whose row `i` consists of `i`s. -/
def superstandard (N : ℕ) (lam : YoungDiagram) (h : lam.colLen 0 ≤ N) :
    BoundedSemistandardTableau N lam where
  tableau := SemistandardYoungTableau.highestWeight lam
  entry_lt := fun cell hcell => by
    obtain ⟨i, j⟩ := cell
    rw [YoungDiagram.mem_cells] at hcell
    show (if (i, j) ∈ lam then i else 0) < N
    rw [if_pos hcell]
    exact lt_of_lt_of_le (lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hcell)
      (lam.colLen_anti 0 j (Nat.zero_le j))) h

@[simp]
theorem superstandard_apply (h : lam.colLen 0 ≤ N) (i j : ℕ) :
    (superstandard N lam h).tableau i j = if (i, j) ∈ lam then i else 0 := rfl

theorem colWeight_superstandard (h : lam.colLen 0 ≤ N) (j v : ℕ) :
    (superstandard N lam h).tableau.colWeight j v = lam.rowLen v - j := by
  have hset : (lam.cells.filter fun c =>
      j ≤ c.2 ∧ (superstandard N lam h).tableau c.1 c.2 = v) =
      (Finset.Ico j (lam.rowLen v)).image (Prod.mk v) := by
    ext ⟨i, c⟩
    constructor
    · intro hmem
      rw [Finset.mem_filter, YoungDiagram.mem_cells, superstandard_apply] at hmem
      obtain ⟨hcell, hj, hv⟩ := hmem
      rw [if_pos hcell] at hv
      subst hv
      exact Finset.mem_image.mpr ⟨c, Finset.mem_Ico.mpr
        ⟨hj, YoungDiagram.mem_iff_lt_rowLen.mp hcell⟩, rfl⟩
    · intro hmem
      obtain ⟨d, hd, hcd⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_Ico] at hd
      rw [← hcd]
      have hcell : (v, d) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr hd.2
      refine Finset.mem_filter.mpr ⟨hcell, hd.1, ?_⟩
      rw [superstandard_apply, if_pos hcell]
  rw [SemistandardYoungTableau.colWeight, hset,
    Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Nat.card_Ico]

theorem weight_superstandard (h : lam.colLen 0 ≤ N) (v : ℕ) :
    (superstandard N lam h).tableau.weight v = lam.rowLen v := by
  rw [← SemistandardYoungTableau.colWeight_zero, colWeight_superstandard]
  omega

theorem isGood_superstandard (h : lam.colLen 0 ≤ N) :
    IsGood (fun _ => 0) (superstandard N lam h) := by
  rintro j ⟨i, hi, hle⟩
  simp only [prof, colWeight_superstandard] at hle
  have := lam.rowLen_anti i (i + 1) (by omega)
  omega

/-- Goodness for the zero vector says exactly that every column suffix has a
weakly decreasing weight. -/
theorem colWeight_antitone {T : BoundedSemistandardTableau N lam}
    (hgood : IsGood (fun _ => 0) T) (j : ℕ) {i i' : ℕ} (hii : i ≤ i') (hi' : i' < N) :
    T.tableau.colWeight j i' ≤ T.tableau.colWeight j i := by
  induction i' with
  | zero =>
    rw [Nat.le_zero.mp hii]
  | succ n ih =>
    rcases eq_or_lt_of_le hii with h | h
    · rw [h]
    · refine le_trans ?_ (ih (by omega) (by omega))
      have hstep : ¬ (prof (fun _ => 0) T j n ≤ prof (fun _ => 0) T j (n + 1)) :=
        fun hcon => hgood j ⟨n, hi', hcon⟩
      simp only [prof] at hstep
      omega

/-- The inductive step for the uniqueness of the good tableau: if every column to
the right of `c` is superstandard and every row above `r` already carries its own
index in column `c`, then so does row `r`. -/
private theorem entry_eq_row_step {T : BoundedSemistandardTableau N lam}
    (hgood : IsGood (fun _ => 0) T) {c r : ℕ} (hcell : (r, c) ∈ lam)
    (hnext : ∀ r' c', c + 1 ≤ c' → (r', c') ∈ lam → T.tableau r' c' = r')
    (ihr : ∀ r', r' < r → (r', c) ∈ lam → T.tableau r' c = r') : T.tableau r c = r := by
  have hge : r ≤ T.tableau r c := T.tableau.row_le_entry hcell
  rcases Classical.em ((r, c + 1) ∈ lam) with hnc | hnc
  · have h1 : T.tableau r c ≤ T.tableau r (c + 1) := T.tableau.row_weak (by omega) hnc
    rw [hnext r (c + 1) le_rfl hnc] at h1
    omega
  by_contra hne
  have hvN : T.tableau r c < N := T.entry_lt (r, c) hcell
  have hcv : T.tableau.colCell c (T.tableau r c) = 1 :=
    (T.tableau.colCell_eq_one_iff c _).mpr ⟨r, hcell, rfl⟩
  have hsplit_v := T.tableau.colWeight_succ c (T.tableau r c)
  have hanti := colWeight_antitone hgood c (i := r) (by omega) hvN
  have hrowlen : lam.rowLen r = c + 1 := by
    have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have h2 : ¬ c + 1 < lam.rowLen r := fun h => hnc (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega
  have hcw1 : T.tableau.colWeight (c + 1) r = 0 := by
    rw [SemistandardYoungTableau.colWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨r', c'⟩ hcell'
    rw [YoungDiagram.mem_cells] at hcell'
    simp only [not_and]
    intro hc'
    rw [hnext r' c' hc' hcell']
    rintro rfl
    have := YoungDiagram.mem_iff_lt_rowLen.mp hcell'
    omega
  have hsplit_r := T.tableau.colWeight_succ c r
  have hone := T.tableau.colCell_le_one c r
  obtain ⟨r'', hr'', hval⟩ := (T.tableau.colCell_eq_one_iff c r).mp (by omega)
  rcases lt_trichotomy r'' r with h | h | h
  · have := ihr r'' h hr''
    omega
  · rw [h] at hval
    omega
  · have := T.tableau.col_strict h hr''
    omega

/-- **The only tableau that is good for the zero vector is the superstandard
one.** -/
theorem entry_eq_row_of_isGood {T : BoundedSemistandardTableau N lam}
    (hgood : IsGood (fun _ => 0) T) (r c : ℕ) (hcell : (r, c) ∈ lam) :
    T.tableau r c = r := by
  suffices H : ∀ d c, lam.rowLen 0 ≤ c + d →
      ∀ r c', c ≤ c' → (r, c') ∈ lam → T.tableau r c' = r from
    H (lam.rowLen 0) 0 (by omega) r c (Nat.zero_le c) hcell
  clear hcell r c
  intro d
  induction d with
  | zero =>
    intro c hc r c' hcc hcell
    have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have h2 := lam.rowLen_anti 0 r (Nat.zero_le r)
    omega
  | succ d ih =>
    intro c hc r c' hcc hcell
    have hnext : ∀ r' c'', c + 1 ≤ c'' → (r', c'') ∈ lam → T.tableau r' c'' = r' :=
      ih (c + 1) (by omega)
    rcases eq_or_lt_of_le hcc with rfl | hlt
    · suffices H : ∀ n r, r ≤ n → (r, c) ∈ lam → T.tableau r c = r from H r r le_rfl hcell
      intro n
      induction n with
      | zero =>
        intro r hr hcell'
        exact entry_eq_row_step hgood hcell' hnext fun r' hr' _ => absurd hr' (by omega)
      | succ n ihn =>
        intro r hr hcell'
        rcases le_or_gt r n with hle | hgt
        · exact ihn r hle hcell'
        · exact entry_eq_row_step hgood hcell' hnext fun r' hr' hcell'' =>
            ihn r' (by omega) hcell''
    · exact hnext r c' hlt hcell

open scoped Classical in
theorem filter_isGood_zero (h : lam.colLen 0 ≤ N) :
    univ.filter (fun T : BoundedSemistandardTableau N lam => IsGood (fun _ => 0) T) =
      {superstandard N lam h} := by
  ext T
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hgood
    ext r c
    rw [superstandard_apply]
    rcases Classical.em ((r, c) ∈ lam) with hcell | hcell
    · rw [if_pos hcell]
      exact entry_eq_row_of_isGood hgood r c hcell
    · rw [if_neg hcell]
      exact T.tableau.zeros hcell
  · rintro rfl
    exact isGood_superstandard h

/-- **The bialternant formula.**  `a_ρ · s_λ = a_{λ + ρ}`. -/
theorem alt_staircase_mul_schurPoly (h : lam.colLen 0 ≤ N) :
    alt (expo N fun i => N - 1 - i) * schurPoly N lam =
      alt (expo N fun i => lam.rowLen i + (N - 1 - i)) := by
  classical
  have key := alt_mul_schurPoly_eq_sum_isGood (N := N) (lam := lam) (κ := fun _ => 0)
    (fun _ => le_rfl)
  rw [filter_isGood_zero h, Finset.sum_singleton] at key
  simp only [zero_add] at key
  rw [key]
  congr 1
  ext i
  rw [expo_apply, expo_apply, prof_zero, weight_superstandard]
  omega

end Stembridge
