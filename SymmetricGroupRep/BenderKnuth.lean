import SymmetricGroupRep.SchurWeyl

/-! # The Bender-Knuth involution

Bender and Knuth's involution exchanges the number of `k`s with the number of
`k + 1`s in a semistandard tableau of a fixed shape.  A cell carrying `k` with a
`k + 1` directly below it, and a cell carrying `k + 1` with a `k` directly above
it, are left alone; in every row the remaining `k`s and `(k + 1)`s form two
adjacent blocks of columns whose lengths the involution exchanges.

Rows increase weakly, so a row is described by the columns `rowSplit T r v` at
which its entries first reach `v`.  Everything below is phrased through those
numbers.
-/

namespace SemistandardYoungTableau

variable {μ : YoungDiagram} (T : SemistandardYoungTableau μ)

/-- The number of cells in row `r` whose entry is below `v`. -/
def rowSplit (r v : ℕ) : ℕ :=
  ((Finset.range (μ.rowLen r)).filter fun c => T r c < v).card

theorem rowSplit_le_rowLen (r v : ℕ) : T.rowSplit r v ≤ μ.rowLen r :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))

/-- Rows increase weakly, so the cells of row `r` with entry below `v` are
exactly the cells in the columns below `rowSplit T r v`. -/
theorem lt_rowSplit_iff {r v c : ℕ} (hc : c < μ.rowLen r) :
    c < T.rowSplit r v ↔ T r c < v := by
  constructor
  · intro h
    by_contra hcon
    have hsub : ((Finset.range (μ.rowLen r)).filter fun d => T r d < v) ⊆ Finset.range c := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_range] at hd
      rw [Finset.mem_range]
      by_contra hdc
      exact absurd (le_trans (not_lt.mp hcon)
        (T.row_weak_of_le (not_lt.mp hdc) (YoungDiagram.mem_iff_lt_rowLen.mpr hd.1)))
        (not_le.mpr hd.2)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    exact absurd h (not_lt.mpr hcard)
  · intro h
    have hsub : Finset.range (c + 1) ⊆ (Finset.range (μ.rowLen r)).filter fun d => T r d < v := by
      intro d hd
      rw [Finset.mem_range] at hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        lt_of_le_of_lt (T.row_weak_of_le (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hc)) h⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    exact hcard

theorem rowSplit_mono (r : ℕ) {v w : ℕ} (h : v ≤ w) : T.rowSplit r v ≤ T.rowSplit r w := by
  refine Finset.card_le_card fun c hc => ?_
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 h⟩

/-- Columns increase strictly, so the entries of a row reach `v + 1` no later
than the entries of the row above reach `v`. -/
theorem rowSplit_succ_row_le (r v : ℕ) : T.rowSplit (r + 1) (v + 1) ≤ T.rowSplit r v := by
  refine Finset.card_le_card fun c hc => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
  have hcol := T.col_strict (show r < r + 1 by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hc.1)
  exact ⟨lt_of_lt_of_le hc.1 (μ.rowLen_anti r (r + 1) (by omega)), by omega⟩

/-- The cells between two consecutive splitting points carry the value between
them. -/
theorem entry_eq_of_rowSplit {r v c : ℕ} (h1 : T.rowSplit r v ≤ c)
    (h2 : c < T.rowSplit r (v + 1)) : T r c = v := by
  have hc : c < μ.rowLen r := lt_of_lt_of_le h2 (T.rowSplit_le_rowLen r (v + 1))
  have h3 : ¬ T r c < v := by
    rw [← T.lt_rowSplit_iff hc]
    omega
  have h4 : T r c < v + 1 := (T.lt_rowSplit_iff hc).mp h2
  omega

/-! ### The free block -/

variable (k : ℕ)

/-- The first column of row `r` carrying a `k` with no `k + 1` directly below. -/
def freeStart (r : ℕ) : ℕ := max (T.rowSplit r k) (T.rowSplit (r + 1) (k + 2))

/-- The splitting point of the row above `r`, with row `0` given no row above. -/
def capAbove (r : ℕ) : ℕ := if r = 0 then T.rowSplit 0 (k + 2) else T.rowSplit (r - 1) k

/-- One past the last column of row `r` carrying a `k + 1` with no `k` directly
above. -/
def freeEnd (r : ℕ) : ℕ := min (T.rowSplit r (k + 2)) (T.capAbove k r)

variable {T k}

@[simp]
theorem capAbove_zero : T.capAbove k 0 = T.rowSplit 0 (k + 2) := if_pos rfl

@[simp]
theorem capAbove_succ (r : ℕ) : T.capAbove k (r + 1) = T.rowSplit r k := if_neg (by omega)

theorem rowSplit_le_freeStart (r : ℕ) : T.rowSplit r k ≤ T.freeStart k r := le_max_left _ _

theorem rowSplit_succ_le_freeStart (r : ℕ) :
    T.rowSplit (r + 1) (k + 2) ≤ T.freeStart k r := le_max_right _ _

theorem freeStart_le_rowSplit (r : ℕ) : T.freeStart k r ≤ T.rowSplit r (k + 1) :=
  max_le (T.rowSplit_mono r (by omega)) (T.rowSplit_succ_row_le r (k + 1))

theorem rowSplit_le_freeEnd (r : ℕ) : T.rowSplit r (k + 1) ≤ T.freeEnd k r := by
  refine le_min (T.rowSplit_mono r (by omega)) ?_
  cases r with
  | zero => rw [capAbove_zero]; exact T.rowSplit_mono 0 (by omega)
  | succ r => rw [capAbove_succ]; exact T.rowSplit_succ_row_le r k

theorem freeEnd_le_rowSplit (r : ℕ) : T.freeEnd k r ≤ T.rowSplit r (k + 2) := min_le_left _ _

theorem freeEnd_le_capAbove (r : ℕ) : T.freeEnd k r ≤ T.capAbove k r := min_le_right _ _

/-! ### The swap -/

variable (T k)

/-- One past the last column of the block of `k`s produced by the swap in row
`r`: the free block keeps its position while its two parts trade lengths. -/
def bkMid (r : ℕ) : ℕ := T.freeStart k r + (T.freeEnd k r - T.rowSplit r (k + 1))

/-- The filling obtained from `T` by exchanging, in every row, the lengths of
the two parts of the free block. -/
def bkEntry (r c : ℕ) : ℕ :=
  if T.freeStart k r ≤ c ∧ c < T.bkMid k r then k
  else if T.bkMid k r ≤ c ∧ c < T.freeEnd k r then k + 1
  else T r c

/-- The splitting points of the swapped filling. -/
def bkSplit (r v : ℕ) : ℕ := if v = k + 1 then T.bkMid k r else T.rowSplit r v

variable {T k}

theorem freeStart_le_bkMid (r : ℕ) : T.freeStart k r ≤ T.bkMid k r := Nat.le_add_right _ _

theorem bkMid_le_freeEnd (r : ℕ) : T.bkMid k r ≤ T.freeEnd k r := by
  have h1 := freeStart_le_rowSplit (T := T) (k := k) r
  have h2 := rowSplit_le_freeEnd (T := T) (k := k) r
  simp only [bkMid]
  omega

theorem bkEntry_of_lt_freeStart {r c : ℕ} (h : c < T.freeStart k r) : T.bkEntry k r c = T r c := by
  have h1 := freeStart_le_bkMid (T := T) (k := k) r
  simp only [bkEntry]
  split_ifs with ha hb
  · exact absurd ha.1 (by omega)
  · exact absurd hb.1 (by omega)
  · rfl

theorem bkEntry_of_freeEnd_le {r c : ℕ} (h : T.freeEnd k r ≤ c) : T.bkEntry k r c = T r c := by
  have h1 := bkMid_le_freeEnd (T := T) (k := k) r
  simp only [bkEntry]
  split_ifs with ha hb
  · exact absurd ha.2 (by omega)
  · exact absurd hb.2 (by omega)
  · rfl

theorem bkEntry_eq_self {r c : ℕ} (h1 : T.freeStart k r ≤ c) (h2 : c < T.bkMid k r) :
    T.bkEntry k r c = k := by
  simp only [bkEntry]
  split_ifs with ha hb
  · rfl
  · exact absurd ⟨h1, h2⟩ ha
  · exact absurd ⟨h1, h2⟩ ha

theorem bkEntry_eq_succ {r c : ℕ} (h1 : T.bkMid k r ≤ c) (h2 : c < T.freeEnd k r) :
    T.bkEntry k r c = k + 1 := by
  have hsb := freeStart_le_bkMid (T := T) (k := k) r
  simp only [bkEntry]
  split_ifs with ha hb
  · exact absurd ha.2 (by omega)
  · rfl
  · exact absurd ⟨h1, h2⟩ hb

theorem bkEntry_le_succ {r c : ℕ} (h : c < T.freeEnd k r) : T.bkEntry k r c ≤ k + 1 := by
  rcases lt_or_ge c (T.freeStart k r) with hc | hc
  · rw [bkEntry_of_lt_freeStart hc]
    have hlt : c < μ.rowLen r :=
      lt_of_lt_of_le hc (le_trans (freeStart_le_rowSplit r) (T.rowSplit_le_rowLen r (k + 1)))
    have := (T.lt_rowSplit_iff hlt (v := k + 1)).mp (lt_of_lt_of_le hc (freeStart_le_rowSplit r))
    omega
  · rcases lt_or_ge c (T.bkMid k r) with hm | hm
    · rw [bkEntry_eq_self hc hm]
      omega
    · rw [bkEntry_eq_succ hm h]

/-- Only the cells of the free block move. -/
theorem mem_free_of_bkEntry_ne {r c : ℕ} (h : T.bkEntry k r c ≠ T r c) :
    T.freeStart k r ≤ c ∧ c < T.freeEnd k r := by
  constructor
  · by_contra hc
    exact h (bkEntry_of_lt_freeStart (by omega))
  · by_contra hc
    exact h (bkEntry_of_freeEnd_le (by omega))

/-- A cell that moves carried at least `k`. -/
theorem le_entry_of_bkEntry_ne {r c : ℕ} (h : T.bkEntry k r c ≠ T r c) : k ≤ T r c := by
  obtain ⟨h1, h2⟩ := mem_free_of_bkEntry_ne h
  have hc : c < μ.rowLen r :=
    lt_of_lt_of_le h2 (le_trans (freeEnd_le_rowSplit r) (T.rowSplit_le_rowLen r (k + 2)))
  have hps := rowSplit_le_freeStart (T := T) (k := k) r
  by_contra hcon
  exact absurd ((T.lt_rowSplit_iff hc (v := k)).mpr (by omega)) (by omega)

/-- A cell that moves receives at most `k + 1`. -/
theorem bkEntry_le_succ_of_ne {r c : ℕ} (h : T.bkEntry k r c ≠ T r c) :
    T.bkEntry k r c ≤ k + 1 :=
  bkEntry_le_succ (mem_free_of_bkEntry_ne h).2

theorem bkSplit_le_rowLen (r v : ℕ) : T.bkSplit k r v ≤ μ.rowLen r := by
  simp only [bkSplit]
  split_ifs
  · exact le_trans (bkMid_le_freeEnd r)
      (le_trans (freeEnd_le_rowSplit r) (T.rowSplit_le_rowLen r (k + 2)))
  · exact T.rowSplit_le_rowLen r v

/-- The swapped filling reaches `v` exactly at the swapped splitting point. -/
theorem bkEntry_lt_iff {r c : ℕ} (hc : c < μ.rowLen r) (v : ℕ) :
    T.bkEntry k r c < v ↔ c < T.bkSplit k r v := by
  have hps := rowSplit_le_freeStart (T := T) (k := k) r
  have hsm := freeStart_le_rowSplit (T := T) (k := k) r
  have hme := rowSplit_le_freeEnd (T := T) (k := k) r
  have heq := freeEnd_le_rowSplit (T := T) (k := k) r
  have hsb := freeStart_le_bkMid (T := T) (k := k) r
  have hbe := bkMid_le_freeEnd (T := T) (k := k) r
  rcases lt_trichotomy v (k + 1) with hv | hv | hv
  · have hvp : T.rowSplit r v ≤ T.rowSplit r k := T.rowSplit_mono r (by omega)
    rw [show T.bkSplit k r v = T.rowSplit r v from if_neg (by omega)]
    constructor
    · intro h
      by_contra hcon
      rcases lt_or_ge c (T.freeStart k r) with hcs | hcs
      · rw [bkEntry_of_lt_freeStart hcs] at h
        exact hcon ((T.lt_rowSplit_iff hc).mpr h)
      · rcases lt_or_ge c (T.bkMid k r) with hcm | hcm
        · rw [bkEntry_eq_self hcs hcm] at h
          omega
        · rcases lt_or_ge c (T.freeEnd k r) with hce | hce
          · rw [bkEntry_eq_succ hcm hce] at h
            omega
          · rw [bkEntry_of_freeEnd_le hce] at h
            exact hcon ((T.lt_rowSplit_iff hc).mpr h)
    · intro h
      rw [bkEntry_of_lt_freeStart (by omega)]
      exact (T.lt_rowSplit_iff hc).mp h
  · subst hv
    rw [show T.bkSplit k r (k + 1) = T.bkMid k r from if_pos rfl]
    constructor
    · intro h
      by_contra hcon
      rcases lt_or_ge c (T.freeEnd k r) with hce | hce
      · rw [bkEntry_eq_succ (by omega) hce] at h
        omega
      · rw [bkEntry_of_freeEnd_le hce] at h
        have := (T.lt_rowSplit_iff hc (v := k + 1)).mpr h
        omega
    · intro h
      rcases lt_or_ge c (T.freeStart k r) with hcs | hcs
      · rw [bkEntry_of_lt_freeStart hcs]
        exact (T.lt_rowSplit_iff hc).mp (by omega)
      · rw [bkEntry_eq_self hcs h]
        omega
  · have hqv : T.rowSplit r (k + 2) ≤ T.rowSplit r v := T.rowSplit_mono r (by omega)
    rw [show T.bkSplit k r v = T.rowSplit r v from if_neg (by omega)]
    constructor
    · intro h
      rcases lt_or_ge c (T.freeEnd k r) with hce | hce
      · omega
      · rw [bkEntry_of_freeEnd_le hce] at h
        exact (T.lt_rowSplit_iff hc).mpr h
    · intro h
      rcases lt_or_ge c (T.freeEnd k r) with hce | hce
      · exact lt_of_le_of_lt (bkEntry_le_succ hce) (by omega)
      · rw [bkEntry_of_freeEnd_le hce]
        exact (T.lt_rowSplit_iff hc).mp h

theorem bkSplit_succ_row_le (r v : ℕ) : T.bkSplit k (r + 1) (v + 1) ≤ T.bkSplit k r v := by
  rcases eq_or_ne v k with hv | hv
  · subst hv
    have h1 := freeStart_le_rowSplit (T := T) (k := v) (r + 1)
    have h2 : T.freeEnd v (r + 1) ≤ T.rowSplit r v := by
      have := freeEnd_le_capAbove (T := T) (k := v) (r + 1)
      rwa [capAbove_succ] at this
    have h3 := rowSplit_le_freeEnd (T := T) (k := v) (r + 1)
    rw [show T.bkSplit v (r + 1) (v + 1) = T.bkMid v (r + 1) from if_pos rfl,
      show T.bkSplit v r v = T.rowSplit r v from if_neg (by omega)]
    simp only [bkMid]
    omega
  · rcases eq_or_ne v (k + 1) with hv1 | hv1
    · subst hv1
      have h1 := rowSplit_succ_le_freeStart (T := T) (k := k) r
      have h2 := freeStart_le_bkMid (T := T) (k := k) r
      rw [show T.bkSplit k (r + 1) (k + 1 + 1) = T.rowSplit (r + 1) (k + 2) from if_neg (by omega),
        show T.bkSplit k r (k + 1) = T.bkMid k r from if_pos rfl]
      omega
    · rw [show T.bkSplit k (r + 1) (v + 1) = T.rowSplit (r + 1) (v + 1) from if_neg (by omega),
        show T.bkSplit k r v = T.rowSplit r v from if_neg hv1]
      exact T.rowSplit_succ_row_le r v

private theorem col_strict_of_adjacent {f : ℕ → ℕ → ℕ}
    (h : ∀ {i j : ℕ}, (i + 1, j) ∈ μ → f i j < f (i + 1) j) {i1 i2 j : ℕ} (hi : i1 < i2)
    (hcell : (i2, j) ∈ μ) : f i1 j < f i2 j := by
  induction i2 with
  | zero => omega
  | succ i ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
    · exact lt_trans (ih h1 (μ.up_left_mem (Nat.le_succ i) le_rfl hcell)) (h hcell)
    · subst h1
      exact h hcell

variable (T k)

/-- The Bender-Knuth involution at `k`. -/
def benderKnuth : SemistandardYoungTableau μ where
  entry := T.bkEntry k
  row_weak' := fun {r j1 j2} hj hcell => by
    have hc2 : j2 < μ.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have hc1 : j1 < μ.rowLen r := by omega
    by_contra hcon
    have h2 := (bkEntry_lt_iff (T := T) (k := k) hc2 (T.bkEntry k r j1)).mp (by omega)
    have h1 := (bkEntry_lt_iff (T := T) (k := k) hc1 (T.bkEntry k r j1)).not.mp (by omega)
    omega
  col_strict' := fun {i1 i2 j} hi hcell => by
    refine col_strict_of_adjacent (fun {r c} hcell' => ?_) hi hcell
    have hc1 : c < μ.rowLen (r + 1) := YoungDiagram.mem_iff_lt_rowLen.mp hcell'
    have hc0 : c < μ.rowLen r := lt_of_lt_of_le hc1 (μ.rowLen_anti r (r + 1) (by omega))
    have h1 : c < T.bkSplit k (r + 1) (T.bkEntry k (r + 1) c + 1) :=
      (bkEntry_lt_iff hc1 _).mp (Nat.lt_succ_self _)
    exact (bkEntry_lt_iff hc0 _).mpr (lt_of_lt_of_le h1 (bkSplit_succ_row_le r _))
  zeros' := fun {r c} hcell => by
    have hc : μ.rowLen r ≤ c := by
      by_contra hcon
      exact hcell (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
    rw [bkEntry_of_freeEnd_le
      (le_trans (le_trans (freeEnd_le_rowSplit r) (T.rowSplit_le_rowLen r (k + 2))) hc),
      T.zeros hcell]

@[simp]
theorem benderKnuth_apply (r c : ℕ) : (T.benderKnuth k) r c = T.bkEntry k r c := rfl

variable {T k}

theorem rowSplit_benderKnuth (r v : ℕ) : (T.benderKnuth k).rowSplit r v = T.bkSplit k r v := by
  have hle1 := (T.benderKnuth k).rowSplit_le_rowLen r v
  have hle2 := bkSplit_le_rowLen (T := T) (k := k) r v
  rcases lt_trichotomy ((T.benderKnuth k).rowSplit r v) (T.bkSplit k r v) with hlt | heq | hgt
  · exfalso
    have hc : (T.benderKnuth k).rowSplit r v < μ.rowLen r := by omega
    exact ((T.benderKnuth k).lt_rowSplit_iff hc (v := v)).not.mp (by omega)
      ((bkEntry_lt_iff hc v).mpr hlt)
  · exact heq
  · exfalso
    have hc : T.bkSplit k r v < μ.rowLen r := by omega
    exact absurd ((bkEntry_lt_iff hc v).mp
      (((T.benderKnuth k).lt_rowSplit_iff hc (v := v)).mp (by omega))) (by omega)

theorem freeStart_benderKnuth (r : ℕ) : (T.benderKnuth k).freeStart k r = T.freeStart k r := by
  simp only [freeStart, rowSplit_benderKnuth, bkSplit, if_neg (by omega : ¬ k = k + 1),
    if_neg (by omega : ¬ k + 2 = k + 1)]

theorem capAbove_benderKnuth (r : ℕ) : (T.benderKnuth k).capAbove k r = T.capAbove k r := by
  cases r with
  | zero =>
    rw [capAbove_zero, capAbove_zero, rowSplit_benderKnuth, bkSplit, if_neg (by omega)]
  | succ r =>
    rw [capAbove_succ, capAbove_succ, rowSplit_benderKnuth, bkSplit, if_neg (by omega)]

theorem freeEnd_benderKnuth (r : ℕ) : (T.benderKnuth k).freeEnd k r = T.freeEnd k r := by
  simp only [freeEnd, rowSplit_benderKnuth, capAbove_benderKnuth, bkSplit,
    if_neg (by omega : ¬ k + 2 = k + 1)]

theorem bkMid_benderKnuth (r : ℕ) :
    (T.benderKnuth k).bkMid k r = T.freeStart k r + (T.freeEnd k r - T.bkMid k r) := by
  show (T.benderKnuth k).freeStart k r +
    ((T.benderKnuth k).freeEnd k r - (T.benderKnuth k).rowSplit r (k + 1)) = _
  rw [freeStart_benderKnuth, freeEnd_benderKnuth, rowSplit_benderKnuth,
    show T.bkSplit k r (k + 1) = T.bkMid k r from if_pos rfl]

/-- The Bender-Knuth involution is an involution. -/
theorem benderKnuth_benderKnuth : (T.benderKnuth k).benderKnuth k = T := by
  ext r c
  have hps := rowSplit_le_freeStart (T := T) (k := k) r
  have hsm := freeStart_le_rowSplit (T := T) (k := k) r
  have hme := rowSplit_le_freeEnd (T := T) (k := k) r
  have heq := freeEnd_le_rowSplit (T := T) (k := k) r
  have hmid : T.bkMid k r = T.freeStart k r + (T.freeEnd k r - T.rowSplit r (k + 1)) := rfl
  have hmid' : (T.benderKnuth k).bkMid k r = T.rowSplit r (k + 1) := by
    rw [bkMid_benderKnuth]
    omega
  show (T.benderKnuth k).bkEntry k r c = T r c
  rcases lt_or_ge c (T.freeStart k r) with hcs | hcs
  · rw [bkEntry_of_lt_freeStart (T := T.benderKnuth k)
      (by rw [freeStart_benderKnuth]; exact hcs)]
    exact bkEntry_of_lt_freeStart hcs
  rcases lt_or_ge c (T.rowSplit r (k + 1)) with hcm | hcm
  · rw [bkEntry_eq_self (T := T.benderKnuth k) (by rw [freeStart_benderKnuth]; exact hcs)
      (by rw [hmid']; exact hcm)]
    exact (T.entry_eq_of_rowSplit (by omega) hcm).symm
  rcases lt_or_ge c (T.freeEnd k r) with hce | hce
  · rw [bkEntry_eq_succ (T := T.benderKnuth k) (by rw [hmid']; exact hcm)
      (by rw [freeEnd_benderKnuth]; exact hce)]
    exact (T.entry_eq_of_rowSplit hcm (by rw [show k + 1 + 1 = k + 2 from by omega]; omega)).symm
  · rw [bkEntry_of_freeEnd_le (T := T.benderKnuth k)
      (by rw [freeEnd_benderKnuth]; exact hce)]
    exact bkEntry_of_freeEnd_le hce

/-! ### Weights -/

variable (T)

/-- The number of cells of `T` carrying the entry `v`. -/
def weight (v : ℕ) : ℕ := (μ.cells.filter fun c => T c.1 c.2 = v).card

variable {T}

private theorem filter_row_eq_Ico (r v : ℕ) :
    ((Finset.range (μ.rowLen r)).filter fun c => T r c = v) =
      Finset.Ico (T.rowSplit r v) (T.rowSplit r (v + 1)) := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hc, hval⟩
    have h1 : ¬ c < T.rowSplit r v := by
      rw [T.lt_rowSplit_iff hc]
      omega
    have h2 : c < T.rowSplit r (v + 1) := (T.lt_rowSplit_iff hc).mpr (by omega)
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_lt_of_le h2 (T.rowSplit_le_rowLen r (v + 1)), T.entry_eq_of_rowSplit h1 h2⟩

theorem weight_eq_sum (v : ℕ) {n : ℕ} (hn : μ.colLen 0 ≤ n) :
    T.weight v = ∑ r ∈ Finset.range n, (T.rowSplit r (v + 1) - T.rowSplit r v) := by
  have hmaps : ∀ c ∈ μ.cells.filter fun c => T c.1 c.2 = v, c.1 ∈ Finset.range n := by
    rintro ⟨i, j⟩ hc
    simp only [Finset.mem_filter, YoungDiagram.mem_cells] at hc
    have hlt := YoungDiagram.mem_iff_lt_colLen.mp hc.1
    have hcol := μ.colLen_anti 0 j (Nat.zero_le j)
    exact Finset.mem_range.mpr (by omega)
  rw [weight, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun r _ => ?_
  have himage : ((μ.cells.filter fun c => T c.1 c.2 = v).filter fun c => c.1 = r) =
      ((Finset.range (μ.rowLen r)).filter fun c => T r c = v).image fun c => (r, c) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, YoungDiagram.mem_cells,
      YoungDiagram.mem_iff_lt_rowLen, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hcell, hval⟩, rfl⟩
      exact ⟨j, ⟨hcell, hval⟩, rfl, rfl⟩
    · rintro ⟨c, ⟨hc, hval⟩, rfl, rfl⟩
      exact ⟨⟨hc, hval⟩, rfl⟩
  rw [himage, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab),
    filter_row_eq_Ico, Nat.card_Ico]

private theorem sum_freeStart_sub {n : ℕ} (hn : μ.colLen 0 ≤ n) :
    ∑ r ∈ Finset.range (n + 1), (T.freeStart k r - T.rowSplit r k) =
      ∑ r ∈ Finset.range (n + 1), (T.rowSplit r (k + 2) - T.freeEnd k r) := by
  have hleft : ∀ r, T.freeStart k r - T.rowSplit r k =
      T.rowSplit (r + 1) (k + 2) - T.rowSplit r k := fun r => by
    simp only [freeStart]
    omega
  have hright : ∀ r, T.rowSplit r (k + 2) - T.freeEnd k r =
      T.rowSplit r (k + 2) - T.capAbove k r := fun r => by
    simp only [freeEnd]
    omega
  simp only [hleft, hright]
  rw [Finset.sum_range_succ (fun r => T.rowSplit (r + 1) (k + 2) - T.rowSplit r k) n,
    Finset.sum_range_succ' (fun r => T.rowSplit r (k + 2) - T.capAbove k r) n]
  have hzero : T.rowSplit (n + 1) (k + 2) = 0 := by
    have h := T.rowSplit_le_rowLen (n + 1) (k + 2)
    rw [YoungDiagram.rowLen_eq_zero hn (by omega)] at h
    omega
  simp only [capAbove_zero, capAbove_succ, hzero, Nat.zero_sub, add_zero, Nat.sub_self]

theorem weight_benderKnuth_of_ne {v : ℕ} (hv : v ≠ k) (hv1 : v ≠ k + 1) :
    (T.benderKnuth k).weight v = T.weight v := by
  rw [weight_eq_sum (T := T.benderKnuth k) v (le_refl _),
    weight_eq_sum (T := T) v (le_refl (μ.colLen 0))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rowSplit_benderKnuth, rowSplit_benderKnuth, bkSplit, bkSplit, if_neg (by omega),
    if_neg (by omega)]

theorem weight_benderKnuth_self : (T.benderKnuth k).weight k = T.weight (k + 1) := by
  rw [weight_eq_sum (T := T.benderKnuth k) k (Nat.le_succ (μ.colLen 0)),
    weight_eq_sum (T := T) (k + 1) (Nat.le_succ (μ.colLen 0))]
  simp only [show k + 1 + 1 = k + 2 from by omega]
  have hleft : ∀ r, (T.benderKnuth k).rowSplit r (k + 1) - (T.benderKnuth k).rowSplit r k =
      (T.freeStart k r - T.rowSplit r k) + (T.freeEnd k r - T.rowSplit r (k + 1)) := fun r => by
    rw [rowSplit_benderKnuth, rowSplit_benderKnuth, bkSplit, bkSplit, if_pos rfl,
      if_neg (by omega : ¬ k = k + 1)]
    have h1 := rowSplit_le_freeStart (T := T) (k := k) r
    simp only [bkMid]
    omega
  have hright : ∀ r, T.rowSplit r (k + 2) - T.rowSplit r (k + 1) =
      (T.rowSplit r (k + 2) - T.freeEnd k r) + (T.freeEnd k r - T.rowSplit r (k + 1)) := fun r => by
    have h1 := rowSplit_le_freeEnd (T := T) (k := k) r
    have h2 := freeEnd_le_rowSplit (T := T) (k := k) r
    omega
  simp only [hleft, hright, Finset.sum_add_distrib,
    sum_freeStart_sub (T := T) (k := k) (le_refl (μ.colLen 0))]

theorem weight_benderKnuth_succ : (T.benderKnuth k).weight (k + 1) = T.weight k := by
  rw [weight_eq_sum (T := T.benderKnuth k) (k + 1) (Nat.le_succ (μ.colLen 0)),
    weight_eq_sum (T := T) k (Nat.le_succ (μ.colLen 0))]
  simp only [show k + 1 + 1 = k + 2 from by omega]
  have hleft : ∀ r, (T.benderKnuth k).rowSplit r (k + 2) -
      (T.benderKnuth k).rowSplit r (k + 1) =
      (T.rowSplit r (k + 2) - T.freeEnd k r) + (T.rowSplit r (k + 1) - T.freeStart k r) :=
    fun r => by
      rw [rowSplit_benderKnuth, rowSplit_benderKnuth, bkSplit, bkSplit, if_pos rfl,
        if_neg (by omega : ¬ k + 2 = k + 1)]
      have h1 := freeStart_le_rowSplit (T := T) (k := k) r
      have h2 := rowSplit_le_freeEnd (T := T) (k := k) r
      have h3 := freeEnd_le_rowSplit (T := T) (k := k) r
      simp only [bkMid]
      omega
  have hright : ∀ r, T.rowSplit r (k + 1) - T.rowSplit r k =
      (T.freeStart k r - T.rowSplit r k) + (T.rowSplit r (k + 1) - T.freeStart k r) := fun r => by
    have h1 := rowSplit_le_freeStart (T := T) (k := k) r
    have h2 := freeStart_le_rowSplit (T := T) (k := k) r
    omega
  simp only [hleft, hright, Finset.sum_add_distrib,
    sum_freeStart_sub (T := T) (k := k) (le_refl (μ.colLen 0))]

end SemistandardYoungTableau
