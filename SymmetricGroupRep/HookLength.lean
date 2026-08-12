import SymmetricGroupRep.Tableaux
import SymmetricGroupRep.Vandermonde
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Hook lengths and the hook-length formula

The formula is proved in the first-column coordinates of Frame, Robinson, and
Thrall, *The Hook Graphs of the Symmetric Group*, Canadian Journal of
Mathematics 6 (1954): a diagram read as `m` rows is recorded by the strictly
decreasing vector `firstColumnHook`, and their Lemma 1 (equation (2.1)) turns
the hook product into a product of factorials divided by a Vandermonde product.
The corner recursion of `StandardTableaux.lean` then becomes the weighted sum
identity `sum_mul_vanderDec_update`.
-/

open Finset

namespace YoungDiagram

/-- The hook length of a cell: one plus the number of cells strictly to its
right in the same row and strictly below it in the same column. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (μ.rowLen c.1 - (c.2 + 1)) + (μ.colLen c.2 - (c.1 + 1)) + 1

/-- The product of the hook lengths of all cells of a Young diagram. -/
def hookProduct (μ : YoungDiagram) : ℕ :=
  μ.cells.prod μ.hookLength

/-- Every hook length is positive. -/
theorem hookLength_pos (μ : YoungDiagram) (c : ℕ × ℕ) :
    0 < μ.hookLength c := by
  simp [hookLength]

/-- The hook product is positive, including for the empty diagram. -/
theorem hookProduct_pos (μ : YoungDiagram) : 0 < μ.hookProduct := by
  exact Finset.prod_pos fun c _ => μ.hookLength_pos c

/-- The descending product from `m` down to one is `m!`. -/
theorem prod_range_desc (m : ℕ) :
    (∏ j ∈ Finset.range m, (m - j)) = m.factorial := by
  calc
    (∏ j ∈ Finset.range m, (m - j)) = m.descFactorial m :=
      (Nat.descFactorial_eq_prod_range m m).symm
    _ = m.factorial := Nat.descFactorial_self m

/-- The first-column hook lengths of `μ` read as a diagram with `m` rows: row
`i` contributes its length plus the number of rows below it. -/
def firstColumnHook (μ : YoungDiagram) (m i : ℕ) : ℕ := μ.rowLen i + (m - 1 - i)

/-- The values omitted by the first-column hook lengths, one for each column. -/
def columnHole (μ : YoungDiagram) (m j : ℕ) : ℕ := j + m - μ.colLen j

variable {μ : YoungDiagram} {m : ℕ}

theorem colLen_le_of_colLen_zero_le (hm : μ.colLen 0 ≤ m) (j : ℕ) : μ.colLen j ≤ m :=
  (μ.colLen_anti 0 j (Nat.zero_le j)).trans hm

/-- Frame--Robinson--Thrall: the hook length of a cell and the hole of its
column add up to the first-column hook length of its row. -/
theorem hookLength_add_columnHole (hm : μ.colLen 0 ≤ m) {i j : ℕ} (hc : (i, j) ∈ μ) :
    μ.hookLength (i, j) + μ.columnHole m j = μ.firstColumnHook m i := by
  have hrow : j < μ.rowLen i := mem_iff_lt_rowLen.mp hc
  have hcol : i < μ.colLen j := mem_iff_lt_colLen.mp hc
  have hle := colLen_le_of_colLen_zero_le hm j
  simp only [hookLength, columnHole, firstColumnHook]
  omega

theorem columnHole_lt_firstColumnHook (hm : μ.colLen 0 ≤ m) {i j : ℕ} (hc : (i, j) ∈ μ) :
    μ.columnHole m j < μ.firstColumnHook m i := by
  have hsum := hookLength_add_columnHole hm hc
  have hpos := μ.hookLength_pos (i, j)
  omega

theorem firstColumnHook_lt_columnHole {i j : ℕ} (hi : i < m)
    (hc : (i, j) ∉ μ) : μ.firstColumnHook m i < μ.columnHole m j := by
  have hrow : μ.rowLen i ≤ j := by
    by_contra hlt
    exact hc (mem_iff_lt_rowLen.mpr (by omega))
  have hcol : μ.colLen j ≤ i := by
    by_contra hlt
    exact hc (mem_iff_lt_colLen.mpr (by omega))
  simp only [columnHole, firstColumnHook]
  omega

theorem firstColumnHook_strictAnti {i k : ℕ} (hik : i < k) (hk : k < m) :
    μ.firstColumnHook m k < μ.firstColumnHook m i := by
  have := μ.rowLen_anti i k hik.le
  simp only [firstColumnHook]
  omega

theorem columnHole_strictMono (hm : μ.colLen 0 ≤ m) {j j' : ℕ} (hjj : j < j') :
    μ.columnHole m j < μ.columnHole m j' := by
  have := μ.colLen_anti j j' hjj.le
  have := colLen_le_of_colLen_zero_le hm j
  simp only [columnHole]
  omega

/-- Frame--Robinson--Thrall, equation (2.1): the hook lengths of a row, together
with the differences of its first-column hook length from the later ones,
exhaust `1, ..., firstColumnHook m i`. -/
theorem prod_hookLength_row_mul_prod_sub (hm : μ.colLen 0 ≤ m) {i : ℕ} (hi : i < m) :
    (∏ j ∈ range (μ.rowLen i), μ.hookLength (i, j)) *
        ∏ k ∈ Ico (i + 1) m, (μ.firstColumnHook m i - μ.firstColumnHook m k) =
      (μ.firstColumnHook m i).factorial := by
  have hinjHole : Set.InjOn (μ.columnHole m) (range (μ.rowLen i)) := by
    intro a _ b _ hab
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab (Nat.ne_of_lt (columnHole_strictMono hm h))
    · exact absurd hab.symm (Nat.ne_of_lt (columnHole_strictMono hm (by omega)))
  have hinjHook : Set.InjOn (μ.firstColumnHook m) (Ico (i + 1) m) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab.symm (Nat.ne_of_lt (firstColumnHook_strictAnti h hb.2))
    · exact absurd hab (Nat.ne_of_lt (firstColumnHook_strictAnti (by omega) ha.2))
  have hdisj : Disjoint ((range (μ.rowLen i)).image (μ.columnHole m))
      ((Ico (i + 1) m).image (μ.firstColumnHook m)) := by
    refine Finset.disjoint_left.mpr ?_
    rintro x hx hx'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx'
    rw [mem_Ico] at hk
    by_cases hcell : (k, j) ∈ μ
    · exact absurd hkx (Nat.ne_of_lt (columnHole_lt_firstColumnHook hm hcell)).symm
    · exact absurd hkx (Nat.ne_of_lt (firstColumnHook_lt_columnHole hk.2 hcell))
  have hunion : (range (μ.rowLen i)).image (μ.columnHole m) ∪
      (Ico (i + 1) m).image (μ.firstColumnHook m) = range (μ.firstColumnHook m i) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        exact mem_range.mpr
          (columnHole_lt_firstColumnHook hm (mem_iff_lt_rowLen.mpr (mem_range.mp hj)))
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
        rw [mem_Ico] at hk
        exact mem_range.mpr (firstColumnHook_strictAnti (by omega) hk.2)
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinjHole,
        Finset.card_image_of_injOn hinjHook, card_range, card_range, Nat.card_Ico]
      simp only [firstColumnHook]
      omega
  have hrow : ∏ x ∈ (range (μ.rowLen i)).image (μ.columnHole m),
      (μ.firstColumnHook m i - x) = ∏ j ∈ range (μ.rowLen i), μ.hookLength (i, j) := by
    rw [Finset.prod_image hinjHole]
    refine Finset.prod_congr rfl fun j hj => ?_
    have := hookLength_add_columnHole hm (mem_iff_lt_rowLen.mpr (mem_range.mp hj))
    omega
  have hlater : ∏ x ∈ (Ico (i + 1) m).image (μ.firstColumnHook m),
      (μ.firstColumnHook m i - x) =
        ∏ k ∈ Ico (i + 1) m, (μ.firstColumnHook m i - μ.firstColumnHook m k) :=
    Finset.prod_image hinjHook
  rw [← hrow, ← hlater, ← Finset.prod_union hdisj, hunion, prod_range_desc]

/-- Reading a diagram with at least as many rows as it has: its cells are the
cells of its first `m` rows. -/
theorem cells_eq_biUnion (hm : μ.colLen 0 ≤ m) :
    μ.cells = (range m).biUnion fun i => (range (μ.rowLen i)).image fun j => (i, j) := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [YoungDiagram.mem_cells, Finset.mem_biUnion, Finset.mem_image, mem_range,
    Prod.mk.injEq]
  constructor
  · intro hc
    exact ⟨i, lt_of_lt_of_le (mem_iff_lt_colLen.mp hc) (colLen_le_of_colLen_zero_le hm j), j,
      mem_iff_lt_rowLen.mp hc, rfl, rfl⟩
  · rintro ⟨i', _, j', hj', rfl, rfl⟩
    exact mem_iff_lt_rowLen.mpr hj'

theorem pairwiseDisjoint_rows (μ : YoungDiagram) :
    ((range m : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun i => (range (μ.rowLen i)).image fun j => ((i, j) : ℕ × ℕ) := by
  intro a _ b _ hab
  refine Finset.disjoint_left.mpr fun c hc hc' => hab ?_
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hc'
  exact (congrArg Prod.fst hj').symm

theorem hookProduct_eq_prod_rows (hm : μ.colLen 0 ≤ m) :
    μ.hookProduct = ∏ i ∈ range m, ∏ j ∈ range (μ.rowLen i), μ.hookLength (i, j) := by
  rw [hookProduct, cells_eq_biUnion hm, Finset.prod_biUnion (pairwiseDisjoint_rows μ)]
  exact Finset.prod_congr rfl fun i _ =>
    Finset.prod_image fun a _ b _ hab => (Prod.mk.injEq .. ▸ hab).2

theorem card_eq_sum_rowLen (hm : μ.colLen 0 ≤ m) :
    μ.card = ∑ i ∈ range m, μ.rowLen i := by
  rw [YoungDiagram.card, cells_eq_biUnion hm, Finset.card_biUnion (pairwiseDisjoint_rows μ)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.card_image_of_injOn fun a _ b _ hab => (Prod.mk.injEq .. ▸ hab).2, card_range]

/-- The first-column hook lengths sum to the number of cells plus the number of
pairs of rows. -/
theorem sum_firstColumnHook (hm : μ.colLen 0 ≤ m) :
    ∑ i ∈ range m, μ.firstColumnHook m i = μ.card + m.choose 2 := by
  have hgauss : ∀ k : ℕ, ∑ i ∈ range k, i = k.choose 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
  simp only [firstColumnHook, Finset.sum_add_distrib]
  rw [← card_eq_sum_rowLen hm, Finset.sum_range_reflect (fun i => i) m, hgauss]

/-- The first-column form of the hook-length product: Frame--Robinson--Thrall,
equation (2.1), summed over the rows. -/
theorem hookProduct_mul_prod_sub (hm : μ.colLen 0 ≤ m) :
    μ.hookProduct * ∏ i ∈ range m, ∏ k ∈ Ico (i + 1) m,
        (μ.firstColumnHook m i - μ.firstColumnHook m k) =
      ∏ i ∈ range m, (μ.firstColumnHook m i).factorial := by
  rw [hookProduct_eq_prod_rows hm, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi => prod_hookLength_row_mul_prod_sub hm (mem_range.mp hi)

theorem hookProduct_mul_vanderDec (hm : μ.colLen 0 ≤ m) :
    (μ.hookProduct : ℚ) * vanderDec m (fun i => (μ.firstColumnHook m i : ℚ)) =
      ∏ i ∈ range m, ((μ.firstColumnHook m i).factorial : ℚ) := by
  have hcast : vanderDec m (fun i => (μ.firstColumnHook m i : ℚ)) =
      ((∏ i ∈ range m, ∏ k ∈ Ico (i + 1) m,
        (μ.firstColumnHook m i - μ.firstColumnHook m k) : ℕ) : ℚ) := by
    rw [vanderDec, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    rw [Nat.cast_sub (firstColumnHook_strictAnti (by omega) hk.2).le]
  rw [hcast, ← Nat.cast_mul, hookProduct_mul_prod_sub hm, Nat.cast_prod]

/-- Delete the last cell of row `i`. This is a diagram exactly when row `i` is
longer than row `i + 1`, that is, when its last cell is a corner. -/
def eraseCorner (μ : YoungDiagram) {i : ℕ} (h : μ.rowLen (i + 1) < μ.rowLen i) :
    YoungDiagram where
  cells := μ.cells.erase (i, μ.rowLen i - 1)
  isLowerSet := by
    intro a b hab ha
    rw [Finset.mem_coe, Finset.mem_erase] at ha ⊢
    refine ⟨?_, μ.isLowerSet hab ha.2⟩
    rintro rfl
    have hlen : a.2 < μ.rowLen a.1 := mem_iff_lt_rowLen.mp ha.2
    have hle : i ≤ a.1 := hab.1
    have hle' : μ.rowLen i - 1 ≤ a.2 := hab.2
    have hanti := μ.rowLen_anti i a.1 hle
    have hrow : a.1 ≠ i := by
      intro hrow
      refine ha.1 (Prod.ext hrow ?_)
      rw [hrow] at hlen
      omega
    have hanti' := μ.rowLen_anti (i + 1) a.1 (by omega)
    omega

theorem mem_eraseCorner {i : ℕ} (h : μ.rowLen (i + 1) < μ.rowLen i) {c : ℕ × ℕ} :
    c ∈ μ.eraseCorner h ↔ c ∈ μ ∧ c ≠ (i, μ.rowLen i - 1) := by
  simp only [eraseCorner, ← YoungDiagram.mem_cells, Finset.mem_erase]
  tauto

theorem eraseCorner_le {i : ℕ} (h : μ.rowLen (i + 1) < μ.rowLen i) : μ.eraseCorner h ≤ μ :=
  fun _ hc => ((mem_eraseCorner h).mp hc).1

theorem card_eraseCorner {i : ℕ} (h : μ.rowLen (i + 1) < μ.rowLen i) :
    (μ.eraseCorner h).card = μ.card - 1 :=
  Finset.card_erase_of_mem (mem_iff_lt_rowLen.mpr (by omega))

theorem rowLen_eraseCorner {i : ℕ} (h : μ.rowLen (i + 1) < μ.rowLen i) (k : ℕ) :
    (μ.eraseCorner h).rowLen k = if k = i then μ.rowLen i - 1 else μ.rowLen k := by
  refine eq_of_forall_lt_iff fun j => ?_
  rw [← mem_iff_lt_rowLen, mem_eraseCorner h, mem_iff_lt_rowLen]
  simp only [ne_eq, Prod.mk.injEq, not_and]
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl]
    exact ⟨fun hc => by have := hc.2 rfl; omega, fun hj => ⟨by omega, fun _ => by omega⟩⟩
  · rw [if_neg hk]
    exact ⟨fun hc => hc.1, fun hj => ⟨hj, fun hc => absurd hc hk⟩⟩

/-- Deleting a corner lowers exactly one first-column hook length, by one. -/
theorem firstColumnHook_eraseCorner {i : ℕ} (h : μ.rowLen (i + 1) < μ.rowLen i) :
    (μ.eraseCorner h).firstColumnHook m =
      Function.update (μ.firstColumnHook m) i (μ.firstColumnHook m i - 1) := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self]
    simp only [firstColumnHook, rowLen_eraseCorner h, if_true]
    omega
  · rw [Function.update_of_ne hk]
    simp only [firstColumnHook, rowLen_eraseCorner h, if_neg hk]

end YoungDiagram

/-- A one-box removal deletes a corner: it is the erasure of the last cell of
the unique row whose length it lowers. -/
theorem exists_eq_eraseCorner {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    {ν : YoungDiagramOfSize n} (hν : ν.val ≤ μ.val) :
    ∃ (i : ℕ) (h : μ.val.rowLen (i + 1) < μ.val.rowLen i),
      ν.val = μ.val.eraseCorner h := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (IsOneBoxRemoval.card_sdiff hν)
  have hmem : c ∈ μ.val.cells ∧ c ∉ ν.val.cells := by
    rw [← Finset.mem_sdiff, hc]
    exact Finset.mem_singleton_self c
  have hcells : ν.val.cells = μ.val.cells.erase c := by
    have hμ : μ.val.cells.card = n + 1 := μ.property
    have hν' : ν.val.cells.card = n := ν.property
    refine Finset.eq_of_subset_of_card_le
      (Finset.subset_erase.mpr ⟨YoungDiagram.cells_subset_iff.mpr hν, hmem.2⟩) ?_
    rw [Finset.card_erase_of_mem hmem.1, hμ, hν']
    omega
  have habove : ∀ d, c ≤ d → d ≠ c → d ∉ μ.val.cells := by
    intro d hd hdc hdμ
    have hdν : d ∈ ν.val.cells := by rw [hcells]; exact Finset.mem_erase.mpr ⟨hdc, hdμ⟩
    exact hmem.2 (ν.val.isLowerSet hd (Finset.mem_coe.mpr hdν))
  have hlen : c.2 < μ.val.rowLen c.1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem.1
  have hright : μ.val.rowLen c.1 = c.2 + 1 := by
    have hnot := habove (c.1, c.2 + 1) (Prod.le_def.mpr ⟨le_rfl, by omega⟩)
      (fun hd => by simpa using congrArg Prod.snd hd)
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hnot
    omega
  have hdown : μ.val.rowLen (c.1 + 1) < μ.val.rowLen c.1 := by
    have hnot := habove (c.1 + 1, c.2) (Prod.le_def.mpr ⟨by omega, le_rfl⟩)
      (fun hd => by simpa using congrArg Prod.fst hd)
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hnot
    omega
  refine ⟨c.1, hdown, YoungDiagram.ext ?_⟩
  rw [hcells]
  congr 1
  rw [show μ.val.rowLen c.1 - 1 = c.2 by omega]

/-- Summing over the one-box removals of `μ` is summing over the rows of `μ`:
the rows that are not corners contribute nothing. -/
theorem sum_oneBoxRemovals_eq_sum_range {n m : ℕ} (μ : YoungDiagramOfSize (n + 1))
    (f : YoungDiagramOfSize n → ℚ) (g : ℕ → ℚ)
    (hcorner : ∀ (i : ℕ) (h : μ.val.rowLen (i + 1) < μ.val.rowLen i)
        (hcard : (μ.val.eraseCorner h).card = n), f ⟨μ.val.eraseCorner h, hcard⟩ = g i)
    (hzero : ∀ i < m, μ.val.rowLen (i + 1) = μ.val.rowLen i → g i = 0)
    (hm : μ.val.colLen 0 ≤ m) :
    ∑ ν ∈ oneBoxRemovals μ, f ν = ∑ i ∈ range m, g i := by
  have hcard : ∀ (i : ℕ) (h : μ.val.rowLen (i + 1) < μ.val.rowLen i),
      (μ.val.eraseCorner h).card = n := by
    intro i h
    rw [YoungDiagram.card_eraseCorner h, μ.property]
    omega
  have hrowLt : ∀ (i : ℕ), μ.val.rowLen (i + 1) < μ.val.rowLen i → i < m := by
    intro i h
    have hcell : (i, 0) ∈ μ.val := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hcell) hm
  have hfilter : ∑ i ∈ range m, g i =
      ∑ i ∈ (range m).filter fun i => μ.val.rowLen (i + 1) < μ.val.rowLen i, g i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hnot => ?_).symm
    have hanti := μ.val.rowLen_anti i (i + 1) (by omega)
    exact hzero i (mem_range.mp hi)
      (by by_contra hne; exact hnot (Finset.mem_filter.mpr ⟨hi, by omega⟩))
  rw [hfilter]
  symm
  refine Finset.sum_bij
    (fun i hi => ⟨μ.val.eraseCorner (show μ.val.rowLen (i + 1) < μ.val.rowLen i from
        (Finset.mem_filter.mp hi).2),
      hcard i (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
  · exact fun i hi => mem_oneBoxRemovals.mpr
      (YoungDiagram.eraseCorner_le (Finset.mem_filter.mp hi).2)
  · intro i hi j hj hij
    by_contra hne
    have hi' := (Finset.mem_filter.mp hi).2
    have hrow := congrArg (fun ν : YoungDiagramOfSize n => ν.val.rowLen i) hij
    simp only [YoungDiagram.rowLen_eraseCorner, if_true, if_neg hne] at hrow
    omega
  · intro ν hν
    obtain ⟨i, h, hval⟩ := exists_eq_eraseCorner (mem_oneBoxRemovals.mp hν)
    exact ⟨i, Finset.mem_filter.mpr ⟨mem_range.mpr (hrowLt i h), h⟩, Subtype.ext hval.symm⟩
  · intro i hi
    exact (hcorner i (Finset.mem_filter.mp hi).2 (hcard i (Finset.mem_filter.mp hi).2)).symm

/-- The inductive step of the hook-length formula: the corner recursion for
standard tableaux against the weighted Vandermonde sum. -/
theorem card_mul_hookProduct_succ {n : ℕ} (μ : YoungDiagramOfSize (n + 1))
    (ih : ∀ ν : YoungDiagramOfSize n,
      Nat.card (StandardYoungTableau ν) * ν.val.hookProduct = n.factorial) :
    Nat.card (StandardYoungTableau μ) * μ.val.hookProduct = (n + 1).factorial := by
  have hm : μ.val.colLen 0 ≤ n + 1 := by
    rw [YoungDiagram.colLen_eq_card]
    exact le_of_le_of_eq (Finset.card_le_card (Finset.filter_subset _ _)) μ.property
  have hbInj : Set.InjOn (fun i => (μ.val.firstColumnHook (n + 1) i : ℚ)) (range (n + 1)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, mem_range] at hx hy
    have hnat : μ.val.firstColumnHook (n + 1) x = μ.val.firstColumnHook (n + 1) y := by
      simpa using hxy
    by_contra hne
    rcases Nat.lt_or_ge x y with h | h
    · exact absurd hnat (YoungDiagram.firstColumnHook_strictAnti h hy).ne'
    · exact absurd hnat (YoungDiagram.firstColumnHook_strictAnti (by omega) hx).ne
  have hvander : vanderDec (n + 1) (fun i => (μ.val.firstColumnHook (n + 1) i : ℚ)) ≠ 0 :=
    vanderDec_ne_zero hbInj
  have hterm : ∀ (i : ℕ) (h : μ.val.rowLen (i + 1) < μ.val.rowLen i)
      (hcard : (μ.val.eraseCorner h).card = n),
      (Nat.card (StandardYoungTableau (⟨μ.val.eraseCorner h, hcard⟩ : YoungDiagramOfSize n)) : ℚ) *
          ∏ j ∈ range (n + 1), ((μ.val.firstColumnHook (n + 1) j).factorial : ℚ) =
        (n.factorial : ℚ) * ((μ.val.firstColumnHook (n + 1) i : ℚ) *
          vanderDec (n + 1) (Function.update
            (fun j => (μ.val.firstColumnHook (n + 1) j : ℚ)) i
            ((μ.val.firstColumnHook (n + 1) i : ℚ) - 1))) := by
    intro i h hcard
    have hcell : (i, 0) ∈ μ.val := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hi : i < n + 1 := lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hcell) hm
    have hpos : 1 ≤ μ.val.firstColumnHook (n + 1) i := by
      simp only [YoungDiagram.firstColumnHook]
      omega
    have hmν : (μ.val.eraseCorner h).colLen 0 ≤ n + 1 := by
      rw [YoungDiagram.colLen_eq_card]
      exact le_trans (le_of_le_of_eq (Finset.card_le_card (Finset.filter_subset _ _)) hcard)
        (by omega)
    have hupdate : (fun j => (((μ.val.eraseCorner h).firstColumnHook (n + 1) j : ℕ) : ℚ)) =
        Function.update (fun j => (μ.val.firstColumnHook (n + 1) j : ℚ)) i
          ((μ.val.firstColumnHook (n + 1) i : ℚ) - 1) := by
      funext j
      rw [YoungDiagram.firstColumnHook_eraseCorner h]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self, Nat.cast_sub hpos, Nat.cast_one]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    have hsplit : ∏ j ∈ range (n + 1), ((μ.val.firstColumnHook (n + 1) j).factorial : ℚ) =
        (μ.val.firstColumnHook (n + 1) i : ℚ) *
          ∏ j ∈ range (n + 1),
            (((μ.val.eraseCorner h).firstColumnHook (n + 1) j).factorial : ℚ) := by
      rw [← Finset.mul_prod_erase _ _ (mem_range.mpr hi),
        ← Finset.mul_prod_erase _ _ (mem_range.mpr hi)]
      have herase : ∀ j ∈ (range (n + 1)).erase i,
          (((μ.val.eraseCorner h).firstColumnHook (n + 1) j).factorial : ℚ) =
            ((μ.val.firstColumnHook (n + 1) j).factorial : ℚ) := by
        intro j hj
        rw [YoungDiagram.firstColumnHook_eraseCorner h,
          Function.update_of_ne (Finset.mem_erase.mp hj).1]
      obtain ⟨t, ht⟩ : ∃ t, μ.val.firstColumnHook (n + 1) i = t + 1 :=
        ⟨μ.val.firstColumnHook (n + 1) i - 1, by omega⟩
      rw [Finset.prod_congr rfl herase, YoungDiagram.firstColumnHook_eraseCorner h,
        Function.update_self, ht]
      simp [Nat.factorial_succ]
      ring
    have hFCν := YoungDiagram.hookProduct_mul_vanderDec (μ := μ.val.eraseCorner h)
      (m := n + 1) hmν
    have hih : (Nat.card (StandardYoungTableau (⟨μ.val.eraseCorner h, hcard⟩ :
        YoungDiagramOfSize n)) : ℚ) * ((μ.val.eraseCorner h).hookProduct : ℚ) =
          (n.factorial : ℚ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℚ)) (ih ⟨μ.val.eraseCorner h, hcard⟩)
    rw [hsplit, ← hFCν, hupdate]
    linear_combination ((μ.val.firstColumnHook (n + 1) i : ℚ) *
      vanderDec (n + 1) (Function.update (fun j => (μ.val.firstColumnHook (n + 1) j : ℚ)) i
        ((μ.val.firstColumnHook (n + 1) i : ℚ) - 1))) * hih
  have hzero : ∀ i < n + 1, μ.val.rowLen (i + 1) = μ.val.rowLen i →
      (n.factorial : ℚ) * ((μ.val.firstColumnHook (n + 1) i : ℚ) *
        vanderDec (n + 1) (Function.update
          (fun j => (μ.val.firstColumnHook (n + 1) j : ℚ)) i
          ((μ.val.firstColumnHook (n + 1) i : ℚ) - 1))) = 0 := by
    intro i hi hrow
    rcases Nat.lt_or_ge (i + 1) (n + 1) with hlt | hge
    · have hstep : μ.val.firstColumnHook (n + 1) i =
          μ.val.firstColumnHook (n + 1) (i + 1) + 1 := by
        simp only [YoungDiagram.firstColumnHook, hrow]
        omega
      rw [vanderDec_eq_zero_of_eq (i := i) (j := i + 1) (by omega) hlt (by
        rw [Function.update_self, Function.update_of_ne (by omega), hstep]
        push_cast
        ring)]
      ring
    · have hlast : μ.val.rowLen i = 0 := by
        by_contra hne
        have hcell : (i + 1, 0) ∈ μ.val := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
        have := lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hcell) hm
        omega
      have hβ : μ.val.firstColumnHook (n + 1) i = 0 := by
        simp only [YoungDiagram.firstColumnHook, hlast]
        omega
      rw [hβ]
      simp
  have hsum : (Nat.card (StandardYoungTableau μ) : ℚ) *
      ∏ j ∈ range (n + 1), ((μ.val.firstColumnHook (n + 1) j).factorial : ℚ) =
      ((n + 1).factorial : ℚ) *
        vanderDec (n + 1) (fun i => (μ.val.firstColumnHook (n + 1) i : ℚ)) := by
    have hrec : (Nat.card (StandardYoungTableau μ) : ℚ) =
        ∑ ν ∈ oneBoxRemovals μ, (Nat.card (StandardYoungTableau ν) : ℚ) := by
      rw [← Nat.cast_sum, ← card_standardYoungTableau_succ μ]
    have htotal : ∑ i ∈ range (n + 1), (μ.val.firstColumnHook (n + 1) i : ℚ) =
        ((n + 1 : ℕ) : ℚ) + (((n + 1).choose 2 : ℕ) : ℚ) := by
      rw [← Nat.cast_sum, YoungDiagram.sum_firstColumnHook hm, μ.property, Nat.cast_add]
    rw [hrec, Finset.sum_mul,
      sum_oneBoxRemovals_eq_sum_range μ
        (fun ν => (Nat.card (StandardYoungTableau ν) : ℚ) *
          ∏ j ∈ range (n + 1), ((μ.val.firstColumnHook (n + 1) j).factorial : ℚ))
        (fun i => (n.factorial : ℚ) * ((μ.val.firstColumnHook (n + 1) i : ℚ) *
          vanderDec (n + 1) (Function.update
            (fun j => (μ.val.firstColumnHook (n + 1) j : ℚ)) i
            ((μ.val.firstColumnHook (n + 1) i : ℚ) - 1)))) hterm hzero hm,
      ← Finset.mul_sum, sum_mul_vanderDec_update hbInj, htotal, Nat.factorial_succ]
    push_cast
    ring
  have hFC := YoungDiagram.hookProduct_mul_vanderDec (μ := μ.val) (m := n + 1) hm
  have hgoal : ((Nat.card (StandardYoungTableau μ) * μ.val.hookProduct : ℕ) : ℚ) =
      (((n + 1).factorial : ℕ) : ℚ) := by
    refine mul_right_cancel₀ hvander ?_
    push_cast
    rw [mul_assoc, hFC, hsum]
  exact_mod_cast hgoal

/-- Multiplicative hook-length formula: `f^μ` times the hook product is `n!`.

The hook convention is Sagan, *The Symmetric Group*, 2nd ed., Definition 3.10.1
(DOI `10.1007/978-1-4757-6804-6_3`), cross-checked against Frame, Robinson, and
Thrall, *The Hook Graphs of the Symmetric Group*, Canadian Journal of
Mathematics 6 (1954), Section 1, equation (1.1) (DOI
`10.4153/CJM-1954-030-1`). The formula is Sagan, Theorem 3.10.2, and
Frame--Robinson--Thrall, Theorem 1. The multiplicative form avoids truncated
natural-number division. -/
theorem standardYoungTableau_card_mul_hookProduct {n : ℕ}
    (μ : YoungDiagramOfSize n) :
  Nat.card (StandardYoungTableau μ) * μ.val.hookProduct = n.factorial := by
  induction n with
  | zero =>
    have hcard : μ.val.cells.card = 0 := μ.property
    rw [card_standardYoungTableau_of_isEmpty μ, YoungDiagram.hookProduct,
      Finset.card_eq_zero.mp hcard]
    simp
  | succ n ih => exact card_mul_hookProduct_succ μ ih
