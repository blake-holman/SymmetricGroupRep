import SymmetricGroupRep.Dimensions
import SymmetricGroupRep.PaddedDiagrams
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Dimension bounds for padded Young diagrams

This file contains the hook-length estimate used for the padded diagrams in
Rosmanis's element-distinctness construction.
-/

open scoped BigOperators

namespace YoungDiagram

/-- The zeroth row of a padded diagram is precisely its padding. -/
theorem padded_rowLen_zero (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (padded N eta h).rowLen 0 = N - eta.card := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen (μ := padded N eta h) (i := 0) (j := j)]
  exact mem_padded_zero_iff N j eta h

/-- Rows below the padding agree with the original diagram. -/
theorem padded_rowLen_succ (N i : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (padded N eta h).rowLen (i + 1) = eta.rowLen i := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen (μ := padded N eta h) (i := i + 1) (j := j),
    ← YoungDiagram.mem_iff_lt_rowLen (μ := eta) (i := i) (j := j)]
  exact mem_padded_succ_iff N i j eta h

/-- A column of a padded diagram consists of the corresponding column of the
original diagram together with its cell in the padded first row. -/
theorem padded_colLen (N j : ℕ) (eta : YoungDiagram) (h : CanPad N eta)
    (hj : j < N - eta.card) :
    (padded N eta h).colLen j = eta.colLen j + 1 := by
  apply eq_of_forall_lt_iff
  intro i
  cases i with
  | zero =>
    rw [← YoungDiagram.mem_iff_lt_colLen (μ := padded N eta h) (i := 0) (j := j)]
    rw [mem_padded_zero_iff]
    omega
  | succ i =>
    rw [← YoungDiagram.mem_iff_lt_colLen (μ := padded N eta h) (i := i + 1) (j := j),
      mem_padded_succ_iff, YoungDiagram.mem_iff_lt_colLen]
    omega

/-- A cell of `eta` lies strictly before the end of every valid padding row. -/
theorem col_lt_padding_of_mem {N i j : ℕ} {eta : YoungDiagram} (h : CanPad N eta)
    (hcell : (i, j) ∈ eta) :
    j < N - eta.card := by
  rw [YoungDiagram.mem_iff_lt_rowLen] at hcell
  exact hcell.trans_le ((eta.rowLen_anti 0 i (Nat.zero_le _)).trans h.2)

/-- Columns at or beyond the number of cells of a diagram are empty. -/
theorem colLen_eq_zero_of_card_le (eta : YoungDiagram) {j : ℕ} (hj : eta.card ≤ j) :
    eta.colLen j = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hcol
  have hcell : (0, j) ∈ eta := YoungDiagram.mem_iff_lt_colLen.mpr hcol
  have hrow : j < eta.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hcell
  have hrow_card : eta.rowLen 0 ≤ eta.card := by
    rw [YoungDiagram.rowLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  exact (Nat.not_lt_of_ge hj) (hrow.trans_le hrow_card)

/-- The descending product from `m` down to one is `m!`. -/
theorem prod_range_desc (m : ℕ) :
    (∏ j ∈ Finset.range m, (m - j)) = m.factorial := by
  calc
    (∏ j ∈ Finset.range m, (m - j)) = m.descFactorial m :=
      (Nat.descFactorial_eq_prod_range m m).symm
    _ = m.factorial := Nat.descFactorial_self m

/-- Extending a row by one box multiplies its hook product by at least the
number of columns not occupied by an `r`-box diagram. -/
theorem top_hook_product_step
    (L r : ℕ) (a : ℕ → ℕ) (hr : r ≤ L)
    (ha : ∀ j, r ≤ j → a j = 0) :
    (L + 1 - r) * (∏ j ∈ Finset.range L, (L - (j + 1) + a j + 1)) ≤
      ∏ j ∈ Finset.range (L + 1), ((L + 1) - (j + 1) + a j + 1) := by
  let d := L - r
  let f₀ : ℕ → ℕ := fun j => L - (j + 1) + a j + 1
  let f₁ : ℕ → ℕ := fun j => (L + 1) - (j + 1) + a j + 1
  have hL : L = r + d := by
    dsimp [d]
    omega
  have hL' : L + 1 = r + (d + 1) := by omega
  have hprefix :
      (∏ j ∈ Finset.range r, f₀ j) ≤ ∏ j ∈ Finset.range r, f₁ j := by
    apply Finset.prod_le_prod
    · intro j _
      exact Nat.zero_le _
    · intro j hj
      simp only [Finset.mem_range] at hj
      dsimp [f₀, f₁]
      omega
  have htail₀ : (∏ x ∈ Finset.range d, f₀ (r + x)) = d.factorial := by
    calc
      (∏ x ∈ Finset.range d, f₀ (r + x)) = ∏ x ∈ Finset.range d, (d - x) := by
        refine Finset.prod_congr rfl ?_
        intro x hx
        simp only [Finset.mem_range] at hx
        have hax : a (r + x) = 0 := ha (r + x) (by omega)
        dsimp [f₀]
        rw [hax]
        omega
      _ = d.factorial := prod_range_desc d
  have htail₁ : (∏ x ∈ Finset.range (d + 1), f₁ (r + x)) = (d + 1).factorial := by
    calc
      (∏ x ∈ Finset.range (d + 1), f₁ (r + x)) =
          ∏ x ∈ Finset.range (d + 1), ((d + 1) - x) := by
        refine Finset.prod_congr rfl ?_
        intro x hx
        simp only [Finset.mem_range] at hx
        have hax : a (r + x) = 0 := ha (r + x) (by omega)
        dsimp [f₁]
        rw [hax]
        omega
      _ = (d + 1).factorial := prod_range_desc (d + 1)
  suffices (d + 1) * (∏ j ∈ Finset.range L, f₀ j) ≤
      ∏ j ∈ Finset.range (L + 1), f₁ j by
    have hcoeff : L + 1 - r = d + 1 := by
      dsimp [d]
      omega
    rw [hcoeff]
    simpa only [f₀, f₁] using this
  rw [hL, Finset.prod_range_add,
    show r + d + 1 = r + (d + 1) by omega, Finset.prod_range_add, htail₀, htail₁,
    Nat.factorial_succ]
  nlinarith [Nat.mul_le_mul_left d.factorial hprefix]

/-- Hook lengths in the added first row. -/
theorem padded_hookLength_zero (N j : ℕ) (eta : YoungDiagram) (h : CanPad N eta)
    (hj : j < N - eta.card) :
    (padded N eta h).hookLength (0, j) =
      (N - eta.card - (j + 1)) + eta.colLen j + 1 := by
  rw [hookLength, padded_rowLen_zero, padded_colLen _ _ _ h hj]
  omega

set_option maxHeartbeats 800000
/-- The hook product in the first row of a padding has the lower bound used
in Rosmanis's Claim 5.6. -/
theorem padded_top_hook_product_step (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta)
    (hlarge : 2 * eta.card ≤ N) :
    (N + 1 - 2 * eta.card) *
        (∏ j ∈ Finset.range (N - eta.card),
          (padded N eta h).hookLength (0, j)) ≤
      ∏ j ∈ Finset.range (N + 1 - eta.card),
        (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (0, j) := by
  let L := N - eta.card
  have hL : eta.card ≤ L := by
    dsimp [L]
    omega
  have hzero : ∀ j, eta.card ≤ j → eta.colLen j = 0 :=
    fun j hj => colLen_eq_zero_of_card_le eta hj
  have hnum := top_hook_product_step L eta.card eta.colLen hL hzero
  have hcoeff : N + 1 - 2 * eta.card = L + 1 - eta.card := by
    dsimp [L]
    omega
  have hLsucc : N + 1 - eta.card = L + 1 := by
    dsimp [L]
    omega
  have htop :
      (∏ j ∈ Finset.range (N - eta.card),
        (padded N eta h).hookLength (0, j)) =
        ∏ j ∈ Finset.range L, (L - (j + 1) + eta.colLen j + 1) := by
    rw [show N - eta.card = L by rfl]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simpa only [L] using padded_hookLength_zero N j eta h hj
  have htopSucc :
      (∏ j ∈ Finset.range (N + 1 - eta.card),
        (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (0, j)) =
        ∏ j ∈ Finset.range (L + 1), ((L + 1) - (j + 1) + eta.colLen j + 1) := by
    rw [hLsucc]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hj' : j < N + 1 - eta.card := by rwa [hLsucc]
    rw [padded_hookLength_zero (N + 1) j eta (canPad_add N 1 eta h) hj']
    dsimp [L]
    omega
  rw [hcoeff, htop, htopSucc]
  exact hnum

set_option maxHeartbeats 200000

/-- Adding one cell to the padded first row leaves all hooks below that row
unchanged. -/
theorem padded_lower_hookLength_stable (N i j : ℕ) (eta : YoungDiagram)
    (h : CanPad N eta) (hcell : (i, j) ∈ eta) :
    (padded N eta h).hookLength (i + 1, j) =
      (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (i + 1, j) := by
  have hj : j < N - eta.card := col_lt_padding_of_mem h hcell
  have hj' : j < N + 1 - eta.card :=
    hj.trans_le (Nat.sub_le_sub_right (Nat.le_add_right N 1) eta.card)
  simp only [hookLength, padded_rowLen_succ, padded_colLen _ _ _ h hj,
    padded_colLen _ _ _ (canPad_add N 1 eta h) hj']

/-- The cells of a padded diagram split into its first row and the shifted
copy of the original diagram. -/
theorem padded_cells_eq_union (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (padded N eta h).cells =
      ({0} ×ˢ Finset.range (N - eta.card)) ∪
        eta.cells.image (fun c : ℕ × ℕ => (c.1 + 1, c.2)) := by
  ext ⟨i, j⟩
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_range, Finset.mem_image]
  constructor
  · intro hcell
    cases i with
    | zero => exact Or.inl ⟨rfl, (mem_padded_zero_iff N j eta h).mp hcell⟩
    | succ i =>
      right
      exact ⟨(i, j), (mem_padded_succ_iff N i j eta h).mp hcell, rfl⟩
  · rintro (⟨hi, hj⟩ | ⟨⟨i, k⟩, hcell, heq⟩)
    · subst i
      exact (mem_padded_zero_iff N j eta h).mpr hj
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact (mem_padded_succ_iff N i k eta h).mpr hcell

set_option maxHeartbeats 800000
/-- The hook product of a padded diagram, separated into the hooks in the new
first row and the hooks in the shifted original diagram. -/
lemma padded_hookProduct_eq (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (padded N eta h).hookProduct =
      (∏ j ∈ Finset.range (N - eta.card), (padded N eta h).hookLength (0, j)) *
        ∏ c ∈ eta.cells, (padded N eta h).hookLength (c.1 + 1, c.2) := by
  let top : Finset (ℕ × ℕ) := {0} ×ˢ Finset.range (N - eta.card)
  let lower : Finset (ℕ × ℕ) :=
    eta.cells.image (fun c : ℕ × ℕ => (c.1 + 1, c.2))
  have hdisjoint : Disjoint top lower := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ htop hlower
    simp only [top, Finset.mem_product, Finset.mem_singleton] at htop
    simp only [lower, Finset.mem_image] at hlower
    obtain ⟨rfl, -⟩ := htop
    obtain ⟨⟨k, l⟩, -, hEq⟩ := hlower
    have := congrArg Prod.fst hEq
    omega
  rw [hookProduct, padded_cells_eq_union, Finset.prod_union hdisjoint]
  congr 1
  · apply Finset.prod_bij (fun c _ => c.2)
    · rintro ⟨i, j⟩ hcell
      simp only [top, Finset.mem_product, Finset.mem_singleton] at hcell
      simpa [hcell.1] using hcell.2
    · rintro ⟨i, j⟩ h₁ ⟨i', j'⟩ h₂ hEq
      simp only [top, Finset.mem_product, Finset.mem_singleton] at h₁ h₂
      obtain ⟨rfl, -⟩ := h₁
      obtain ⟨rfl, -⟩ := h₂
      simp only [Prod.mk.injEq, true_and]
      exact hEq
    · intro j hj
      exact ⟨(0, j), by simp [top, hj], rfl⟩
    · rintro ⟨i, j⟩ hcell
      simp only [top, Finset.mem_product, Finset.mem_singleton] at hcell
      obtain ⟨rfl, -⟩ := hcell
      rfl
  · rw [Finset.prod_image]
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ hEq
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨hEq₁, hEq₂⟩ := hEq
      have : a = c := by omega
      simp [this, hEq₂]

/-- The factors below the added first row cancel from the hook-product ratio
of two consecutive paddings. -/
theorem padded_hookProduct_cross (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta) :
    (padded N eta h).hookProduct *
        (∏ j ∈ Finset.range (N + 1 - eta.card),
          (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (0, j)) =
      (padded (N + 1) eta (canPad_add N 1 eta h)).hookProduct *
        ∏ j ∈ Finset.range (N - eta.card), (padded N eta h).hookLength (0, j) := by
  have hlower :
      (∏ c ∈ eta.cells, (padded N eta h).hookLength (c.1 + 1, c.2)) =
        ∏ c ∈ eta.cells,
          (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (c.1 + 1, c.2) := by
    apply Finset.prod_congr rfl
    intro c hc
    exact padded_lower_hookLength_stable N c.1 c.2 eta h hc
  rw [padded_hookProduct_eq, padded_hookProduct_eq, hlower]
  ac_rfl

/-- The full hook-product form of the padded first-row estimate. -/
theorem padded_hookProduct_step (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta)
    (hlarge : 2 * eta.card ≤ N) :
    (N + 1 - 2 * eta.card) * (padded N eta h).hookProduct ≤
      (padded (N + 1) eta (canPad_add N 1 eta h)).hookProduct := by
  have htop := padded_top_hook_product_step N eta h hlarge
  have hlower :
      (∏ c ∈ eta.cells, (padded N eta h).hookLength (c.1 + 1, c.2)) =
        ∏ c ∈ eta.cells,
          (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (c.1 + 1, c.2) := by
    apply Finset.prod_congr rfl
    intro c hc
    exact padded_lower_hookLength_stable N c.1 c.2 eta h hc
  rw [padded_hookProduct_eq, padded_hookProduct_eq, ← hlower]
  calc
    (N + 1 - 2 * eta.card) *
        ((∏ j ∈ Finset.range (N - eta.card), (padded N eta h).hookLength (0, j)) *
          ∏ c ∈ eta.cells, (padded N eta h).hookLength (c.1 + 1, c.2)) =
        ((N + 1 - 2 * eta.card) *
          ∏ j ∈ Finset.range (N - eta.card), (padded N eta h).hookLength (0, j)) *
          ∏ c ∈ eta.cells, (padded N eta h).hookLength (c.1 + 1, c.2) := by ac_rfl
    _ ≤ (∏ j ∈ Finset.range (N + 1 - eta.card),
          (padded (N + 1) eta (canPad_add N 1 eta h)).hookLength (0, j)) *
          ∏ c ∈ eta.cells, (padded N eta h).hookLength (c.1 + 1, c.2) :=
      Nat.mul_le_mul_right _ htop

/-- A hook-product lower bound gives the corresponding dimension-ratio bound. -/
theorem one_sub_hook_ratio_le_two_mul_div
    (N r hc hp : ℕ) (hcpos : 0 < hc) (hlarge : 2 * r ≤ N + 1)
    (hhp : (N + 1 - 2 * r) * hc ≤ hp) :
    1 - (hp : ℚ) / ((N + 1) * hc) ≤ (2 * r : ℚ) / (N + 1) := by
  have hn : (N + 1 : ℚ) ≠ 0 := by positivity
  have hcne : (hc : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcpos.ne'
  have hhpq : ((N + 1 - 2 * r : ℕ) : ℚ) * hc ≤ hp := by
    exact_mod_cast hhp
  have hcast : ((N + 1 - 2 * r : ℕ) : ℚ) = (N + 1 : ℚ) - 2 * r := by
    rw [Nat.cast_sub hlarge]
    push_cast
    ring
  rw [hcast] at hhpq
  field_simp
  linarith

/-- Rosmanis's Claim 5.6 in finite form: removing the final cell of a padded
first row loses at most `2r / (N + 1)` of the Specht dimension. -/
theorem one_sub_padded_finrank_ratio_le_two_mul_div
    (N : ℕ) (eta : YoungDiagram) (h : CanPad N eta)
    (hlarge : 2 * eta.card ≤ N) :
    1 - (Module.finrank ℂ (spechtModule (paddedOfSize N eta h)) : ℚ) /
      Module.finrank ℂ (spechtModule (paddedOfSize (N + 1) eta (canPad_add N 1 eta h))) ≤
        (2 * eta.card : ℚ) / (N + 1) := by
  let μ := paddedOfSize N eta h
  let ν := paddedOfSize (N + 1) eta (canPad_add N 1 eta h)
  have hhook := padded_hookProduct_step N eta h hlarge
  have hratio :
      (Module.finrank ℂ (spechtModule μ) : ℚ) /
          Module.finrank ℂ (spechtModule ν) =
        (ν.val.hookProduct : ℚ) / ((N + 1) * μ.val.hookProduct) := by
    rw [spechtModule_finrank_cast_eq_factorial_div_hookProduct,
      spechtModule_finrank_cast_eq_factorial_div_hookProduct,
      Nat.factorial_succ]
    push_cast
    field_simp [μ.val.hookProduct_pos.ne', ν.val.hookProduct_pos.ne', Nat.factorial_ne_zero]
  change 1 - (Module.finrank ℂ (spechtModule μ) : ℚ) /
      Module.finrank ℂ (spechtModule ν) ≤ (2 * eta.card : ℚ) / (N + 1)
  rw [hratio]
  apply one_sub_hook_ratio_le_two_mul_div N eta.card μ.val.hookProduct ν.val.hookProduct
    μ.val.hookProduct_pos
  · omega
  · exact hhook

set_option maxHeartbeats 200000

end YoungDiagram
