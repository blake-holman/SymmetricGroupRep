import SymmetricGroupRep.LittlewoodRichardson
import SymmetricGroupRep.SchurProduct

/-! # Littlewood-Richardson tableaux are Stembridge's good tableaux

The Littlewood-Richardson coefficient counts fillings of the skew shape `ξ / μ`
with content `ν` whose reverse reading word is a lattice word, while Stembridge's
proof of the product rule counts fillings of the straight shape `ν` with entries
below `a + b` that are good for `μ`.  A filling of either kind is determined by
how often each value occurs in each of its rows, and the two row-content matrices
are transposes of each other.  Transposing sends the lattice condition to column
strictness and column strictness to goodness, so the two index sets have the same
size.

See Grinberg-Reiner, *Hopf Algebras in Combinatorics*, Exercise 2.9.18(b) for the
unshifted form of the equivalence between goodness and column strictness.
-/

open Finset

/-! ## Rows filled from a content vector -/

/-- The entry at offset `t` of the weakly increasing row of `B` possible values
in which the value `i` occurs `m i` times. -/
def rowFill (B : ℕ) (m : ℕ → ℕ) (t : ℕ) : ℕ :=
  ((range B).filter fun i => ∑ j ∈ range (i + 1), m j ≤ t).card

/-- The values below `k` occupy the first `m 0 + ⋯ + m (k-1)` cells of the row. -/
theorem rowFill_lt_iff {B k : ℕ} (hk : k ≤ B) (m : ℕ → ℕ) (t : ℕ) :
    rowFill B m t < k ↔ t < ∑ j ∈ range k, m j := by
  simp only [rowFill]
  constructor
  · intro hlt
    by_contra hcon
    have hsub : range k ⊆ (range B).filter fun i => ∑ j ∈ range (i + 1), m j ≤ t := by
      intro i hi
      rw [mem_range] at hi
      exact mem_filter.mpr ⟨mem_range.mpr (lt_of_lt_of_le hi hk),
        le_trans (Finset.sum_le_sum_of_subset (range_subset_range.mpr hi)) (not_lt.mp hcon)⟩
    have hcard := card_le_card hsub
    rw [card_range] at hcard
    omega
  · intro hlt
    have hsub : ((range B).filter fun i => ∑ j ∈ range (i + 1), m j ≤ t) ⊆ range (k - 1) := by
      intro i hi
      rw [mem_filter] at hi
      rw [mem_range]
      by_contra hcon
      exact absurd (le_trans (Finset.sum_le_sum_of_subset
        (range_subset_range.mpr (by omega : k ≤ i + 1))) hi.2) (by omega)
    have hcard := card_le_card hsub
    rw [card_range] at hcard
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hlt
    · omega

theorem rowFill_mono (B : ℕ) (m : ℕ → ℕ) {t t' : ℕ} (h : t ≤ t') :
    rowFill B m t ≤ rowFill B m t' :=
  card_le_card fun _ hi => mem_filter.mpr
    ⟨(mem_filter.mp hi).1, le_trans (mem_filter.mp hi).2 h⟩

theorem rowFill_lt (B : ℕ) (m : ℕ → ℕ) {t : ℕ} (h : t < ∑ j ∈ range B, m j) :
    rowFill B m t < B := (rowFill_lt_iff le_rfl m t).mpr h

/-- Filling a row from a content vector reproduces that content. -/
theorem card_filter_rowFill {B i : ℕ} (hi : i < B) (m : ℕ → ℕ) (s : ℕ) :
    ((Ico s (s + ∑ j ∈ range B, m j)).filter fun c => rowFill B m (c - s) = i).card = m i := by
  have hle : ∑ j ∈ range (i + 1), m j ≤ ∑ j ∈ range B, m j :=
    Finset.sum_le_sum_of_subset (range_subset_range.mpr hi)
  have hset : ((Ico s (s + ∑ j ∈ range B, m j)).filter fun c => rowFill B m (c - s) = i)
      = Ico (s + ∑ j ∈ range i, m j) (s + ∑ j ∈ range (i + 1), m j) := by
    ext t
    have e1 := rowFill_lt_iff (le_of_lt hi) m (t - s)
    have e2 := rowFill_lt_iff (show i + 1 ≤ B from hi) m (t - s)
    simp only [mem_filter, mem_Ico]
    omega
  rw [hset, Nat.card_Ico, Finset.sum_range_succ]
  omega

/-- A weakly increasing row is the row filled by its own content. -/
theorem eq_rowFill {B s e : ℕ} {f : ℕ → ℕ}
    (hmono : ∀ c d, s ≤ c → c ≤ d → d < e → f c ≤ f d)
    (hbound : ∀ c, s ≤ c → c < e → f c < B)
    {c : ℕ} (hcs : s ≤ c) (hce : c < e) :
    rowFill B (fun i => ((Ico s e).filter fun c' => f c' = i).card) (c - s) = f c := by
  classical
  set m := fun i => ((Ico s e).filter fun c' => f c' = i).card with hm
  have hsum : ∀ k ≤ B, ∑ i ∈ range k, m i = ((Ico s e).filter fun c' => f c' < k).card := by
    intro k _
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := range k)
      fun x hx => mem_range.mpr (mem_filter.mp hx).2]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hm, Finset.filter_filter]
    exact congrArg Finset.card
      (Finset.filter_congr fun x _ =>
        ⟨fun h => ⟨by rw [h]; exact mem_range.mp hi, h⟩, fun h => h.2⟩)
  have hkey : ∀ k ≤ B, (rowFill B m (c - s) < k ↔ f c < k) := by
    intro k hkB
    rw [rowFill_lt_iff hkB, hsum k hkB]
    constructor
    · intro hlt
      by_contra hcon
      have hsub : ((Ico s e).filter fun c' => f c' < k) ⊆ Ico s c := by
        intro x hx
        rw [mem_filter, mem_Ico] at hx
        refine mem_Ico.mpr ⟨hx.1.1, ?_⟩
        by_contra hxc
        exact absurd (lt_of_lt_of_le hx.2 (not_lt.mp hcon))
          (not_lt.mpr (hmono c x hcs (not_lt.mp hxc) hx.1.2))
      have hcard := card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega
    · intro hfc
      have hsub : Ico s (c + 1) ⊆ (Ico s e).filter fun c' => f c' < k := by
        intro x hx
        rw [mem_Ico] at hx
        exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hx.1, by omega⟩,
          lt_of_le_of_lt (hmono x c hx.1 (by omega) hce) hfc⟩
      have hcard := card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega
  have hy : f c < B := hbound c hcs hce
  have hx : rowFill B m (c - s) < B := (hkey B le_rfl).mpr hy
  have h1 := (hkey (f c + 1) (by omega)).mpr (Nat.lt_succ_self _)
  have h2 := (hkey (rowFill B m (c - s) + 1) (by omega)).mp (Nat.lt_succ_self _)
  omega

/-! ## The skew shape -/

theorem YoungDiagram.mem_sdiff_cells {mu xi : YoungDiagram} {r c : ℕ} :
    (r, c) ∈ xi.cells \ mu.cells ↔ mu.rowLen r ≤ c ∧ c < xi.rowLen r := by
  simp only [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, not_lt]
  tauto

namespace LittlewoodRichardsonTableau

variable {a b : ℕ} {mu : YoungDiagramOfSize a} {nu : YoungDiagramOfSize b}
  {xi : YoungDiagramOfSize (a + b)} (U : LittlewoodRichardsonTableau mu nu xi)

/-- The entry of a Littlewood-Richardson tableau as a function of the coordinates
of the cell. -/
noncomputable def entryAt (r c : ℕ) : ℕ :=
  if h : (r, c) ∈ xi.val.cells \ mu.val.cells then (U.entry ⟨(r, c), h⟩ : ℕ) else b

theorem entryAt_eq {r c : ℕ} (h : (r, c) ∈ xi.val.cells \ mu.val.cells) :
    U.entryAt r c = (U.entry ⟨(r, c), h⟩ : ℕ) := dif_pos h

theorem entryAt_lt {r c : ℕ} (h : mu.val.rowLen r ≤ c ∧ c < xi.val.rowLen r) :
    U.entryAt r c < b := by
  rw [U.entryAt_eq (YoungDiagram.mem_sdiff_cells.mpr h)]
  exact (U.entry _).isLt

theorem entryAt_row_weak {r c d : ℕ} (hc : mu.val.rowLen r ≤ c)
    (hcd : c ≤ d) (hd : d < xi.val.rowLen r) : U.entryAt r c ≤ U.entryAt r d := by
  have hmc : (r, c) ∈ xi.val.cells \ mu.val.cells := YoungDiagram.mem_sdiff_cells.mpr ⟨hc, by omega⟩
  have hmd : (r, d) ∈ xi.val.cells \ mu.val.cells := YoungDiagram.mem_sdiff_cells.mpr ⟨by omega, hd⟩
  rw [U.entryAt_eq hmc, U.entryAt_eq hmd]
  rcases eq_or_lt_of_le hcd with rfl | hlt
  · exact le_rfl
  · exact U.row_weak (c := ⟨(r, c), hmc⟩) (d := ⟨(r, d), hmd⟩) rfl hlt

theorem entryAt_col_strict {r r' c : ℕ} (hc : mu.val.rowLen r ≤ c) (hcx : c < xi.val.rowLen r)
    (hc' : mu.val.rowLen r' ≤ c) (hcx' : c < xi.val.rowLen r') (hrr : r < r') :
    U.entryAt r c < U.entryAt r' c := by
  have hm : (r, c) ∈ xi.val.cells \ mu.val.cells := YoungDiagram.mem_sdiff_cells.mpr ⟨hc, hcx⟩
  have hm' : (r', c) ∈ xi.val.cells \ mu.val.cells := YoungDiagram.mem_sdiff_cells.mpr ⟨hc', hcx'⟩
  rw [U.entryAt_eq hm, U.entryAt_eq hm']
  exact U.col_strict (c := ⟨(r, c), hm⟩) (d := ⟨(r', c), hm'⟩) rfl hrr

end LittlewoodRichardsonTableau

/-! ## Fillings of a skew shape

The two conditions on a Littlewood-Richardson tableau that involve more than one
row are read off from its row contents, so they are stated here for an arbitrary
filling `f` of the cells of `xi` outside `mu`. -/

theorem Finset.card_filter_attach_coe {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun x : ↥s => p ↑x).card = (s.filter p).card := by
  rw [Finset.univ_eq_attach, Finset.filter_attach, Finset.card_map, Finset.card_attach]

namespace SkewFilling

variable (mu xi : YoungDiagram) (f : ℕ → ℕ → ℕ)

/-- How often the value `i` occurs in row `r` of a filling of `xi / mu`. -/
noncomputable def rowContent (r i : ℕ) : ℕ :=
  ((Ico (mu.rowLen r) (xi.rowLen r)).filter fun c => f r c = i).card

/-- How often the value `i` occurs at or before `d` in the reading order. -/
noncomputable def prefixCount (d : ℕ × ℕ) (i : ℕ) : ℕ :=
  ((xi.cells \ mu.cells).filter fun x =>
    LittlewoodRichardson.readingLE x d ∧ f x.1 x.2 = i).card

/-- The first `r` rows hold the first `r` row contents. -/
theorem sum_rowContent (r i : ℕ) :
    ∑ r' ∈ range r, rowContent mu xi f r' i
      = ((xi.cells \ mu.cells).filter fun x => x.1 < r ∧ f x.1 x.2 = i).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ => x.1) (t := range r)
    fun x hx => mem_range.mpr (mem_filter.mp hx).2.1]
  refine Finset.sum_congr rfl fun r' hr' => ?_
  have himage : (((xi.cells \ mu.cells).filter fun x => x.1 < r ∧ f x.1 x.2 = i).filter
      fun x => x.1 = r')
      = ((Ico (mu.rowLen r') (xi.rowLen r')).filter fun c => f r' c = i).image (Prod.mk r') := by
    ext ⟨y, c⟩
    simp only [mem_filter, mem_image, mem_Ico, YoungDiagram.mem_sdiff_cells, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, -, h4⟩, rfl⟩
      exact ⟨c, ⟨⟨h1, h2⟩, h4⟩, rfl, rfl⟩
    · rintro ⟨d, ⟨⟨h1, h2⟩, h3⟩, rfl, rfl⟩
      exact ⟨⟨⟨h1, h2⟩, mem_range.mp hr', h3⟩, rfl⟩
  rw [himage, Finset.card_image_of_injective _ fun x y hxy => (Prod.mk.injEq .. ▸ hxy).2]
  rfl

variable {mu xi f}

theorem prefixCount_le (d : ℕ × ℕ) (i : ℕ) :
    prefixCount mu xi f d i ≤ ∑ r' ∈ range (d.1 + 1), rowContent mu xi f r' i := by
  rw [sum_rowContent]
  refine card_le_card fun x hx => ?_
  rw [mem_filter] at hx ⊢
  rcases hx.2.1 with h | ⟨h, -⟩
  · exact ⟨hx.1, by omega, hx.2.2⟩
  · exact ⟨hx.1, by omega, hx.2.2⟩

theorem le_prefixCount (d : ℕ × ℕ) (i : ℕ) :
    ∑ r' ∈ range d.1, rowContent mu xi f r' i ≤ prefixCount mu xi f d i := by
  rw [sum_rowContent]
  refine card_le_card fun x hx => ?_
  rw [mem_filter] at hx ⊢
  exact ⟨hx.1, Or.inl hx.2.1, hx.2.2⟩

/-- Reading the row contents column by column: the lattice condition follows from
the inequalities between partial column sums. -/
theorem prefixCount_succ_le (hR : ∀ r i, ∑ r' ∈ range (r + 1), rowContent mu xi f r' (i + 1)
      ≤ ∑ r' ∈ range r, rowContent mu xi f r' i) (d : ℕ × ℕ) (i : ℕ) :
    prefixCount mu xi f d (i + 1) ≤ prefixCount mu xi f d i :=
  le_trans (le_trans (prefixCount_le d (i + 1)) (hR d.1 i)) (le_prefixCount d i)

/-- Cutting the reading word just before the leftmost `i + 1` of row `r` turns the
lattice condition at that cell into the inequality between partial column sums. -/
theorem sum_rowContent_succ_le_of_pos
    (hweak : ∀ r c c', mu.rowLen r ≤ c → c ≤ c' → c' < xi.rowLen r → f r c ≤ f r c')
    (hL : ∀ d ∈ xi.cells \ mu.cells, ∀ i,
      prefixCount mu xi f d (i + 1) ≤ prefixCount mu xi f d i)
    {r i : ℕ} (hpos : 0 < rowContent mu xi f r (i + 1)) :
    ∑ r' ∈ range (r + 1), rowContent mu xi f r' (i + 1)
      ≤ ∑ r' ∈ range r, rowContent mu xi f r' i := by
  classical
  set S := (Ico (mu.rowLen r) (xi.rowLen r)).filter fun c => f r c = i + 1 with hS
  have hne : S.Nonempty := Finset.card_pos.mp hpos
  set c0 := S.min' hne with hc0
  have hmem := Finset.mem_filter.mp (S.min'_mem hne)
  have hIco := mem_Ico.mp hmem.1
  have hd : (r, c0) ∈ xi.cells \ mu.cells := YoungDiagram.mem_sdiff_cells.mpr hIco
  have hleft : ∑ r' ∈ range (r + 1), rowContent mu xi f r' (i + 1)
      ≤ prefixCount mu xi f (r, c0) (i + 1) := by
    rw [sum_rowContent]
    refine card_le_card fun x hx => ?_
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_, hx.2.2⟩
    rcases Nat.lt_or_ge x.1 r with h | h
    · exact Or.inl h
    · have hxr : x.1 = r := by omega
      refine Or.inr ⟨hxr, S.min'_le x.2 (Finset.mem_filter.mpr ⟨mem_Ico.mpr ?_, ?_⟩)⟩
      · rw [← hxr]
        exact YoungDiagram.mem_sdiff_cells.mp hx.1
      · rw [← hxr]
        exact hx.2.2
  have hright : prefixCount mu xi f (r, c0) i ≤ ∑ r' ∈ range r, rowContent mu xi f r' i := by
    rw [sum_rowContent]
    refine card_le_card fun x hx => ?_
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_, hx.2.2⟩
    rcases hx.2.1 with h | ⟨hxr, hc⟩
    · exact h
    · exfalso
      have hxr' : x.1 = r := hxr
      have hval : f r x.2 = i := by rw [← hxr']; exact hx.2.2
      have hx2 := YoungDiagram.mem_sdiff_cells.mp hx.1
      rw [hxr'] at hx2
      have hmono := hweak r c0 x.2 hIco.1 hc hx2.2
      rw [hmem.2, hval] at hmono
      omega
  exact le_trans hleft (le_trans (hL _ hd i) hright)

/-- **The lattice condition is the inequality between partial column sums.** -/
theorem sum_rowContent_succ_le
    (hweak : ∀ r c c', mu.rowLen r ≤ c → c ≤ c' → c' < xi.rowLen r → f r c ≤ f r c')
    (hL : ∀ d ∈ xi.cells \ mu.cells, ∀ i,
      prefixCount mu xi f d (i + 1) ≤ prefixCount mu xi f d i) (r i : ℕ) :
    ∑ r' ∈ range (r + 1), rowContent mu xi f r' (i + 1)
      ≤ ∑ r' ∈ range r, rowContent mu xi f r' i := by
  induction r with
  | zero =>
    rcases Nat.eq_zero_or_pos (rowContent mu xi f 0 (i + 1)) with hz | hpos
    · simp [hz]
    · exact sum_rowContent_succ_le_of_pos hweak hL hpos
  | succ s ih =>
    rcases Nat.eq_zero_or_pos (rowContent mu xi f (s + 1) (i + 1)) with hz | hpos
    · rw [Finset.sum_range_succ, hz, Nat.add_zero]
      exact le_trans ih (Finset.sum_le_sum_of_subset (range_subset_range.mpr (Nat.le_succ s)))
    · exact sum_rowContent_succ_le_of_pos hweak hL hpos

/-! ### Column strictness -/

variable {B : ℕ}

theorem rowContent_eq_zero
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B) (r : ℕ) {i : ℕ}
    (hi : B ≤ i) : rowContent mu xi f r i = 0 := by
  rw [rowContent, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc hval
  exact absurd (hval ▸ hbound r c (mem_Ico.mp hc).1 (mem_Ico.mp hc).2) (by omega)

theorem sum_rowContent_eq
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B) (r : ℕ) {k : ℕ} (hk : B ≤ k) :
    ∑ i ∈ range k, rowContent mu xi f r i = ∑ i ∈ range B, rowContent mu xi f r i :=
  (Finset.sum_subset (range_subset_range.mpr hk) fun i _ hi =>
    rowContent_eq_zero hbound r (by simpa using hi)).symm

theorem sum_rowContent_le
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B) (r k : ℕ) :
    ∑ i ∈ range k, rowContent mu xi f r i ≤ ∑ i ∈ range B, rowContent mu xi f r i := by
  rcases le_or_gt k B with hk | hk
  · exact Finset.sum_le_sum_of_subset (range_subset_range.mpr hk)
  · exact le_of_eq (sum_rowContent_eq hbound r (le_of_lt hk))

/-- The values of row `r` fill the cells of that row. -/
theorem sum_rowContent_row
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B) (hle : mu ≤ xi) (r : ℕ) :
    mu.rowLen r + ∑ i ∈ range B, rowContent mu xi f r i = xi.rowLen r := by
  classical
  have hcard : ∑ i ∈ range B, rowContent mu xi f r i
      = (Ico (mu.rowLen r) (xi.rowLen r)).card :=
    (Finset.card_eq_sum_card_fiberwise (f := fun c => f r c) (t := range B)
      fun c hc => mem_range.mpr (hbound r c (mem_Ico.mp hc).1 (mem_Ico.mp hc).2)).symm
  have := YoungDiagram.rowLen_le_of_le hle r
  rw [hcard, Nat.card_Ico]
  omega

theorem eq_rowFill_rowContent
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B)
    (hweak : ∀ r c c', mu.rowLen r ≤ c → c ≤ c' → c' < xi.rowLen r → f r c ≤ f r c')
    {r c : ℕ} (h1 : mu.rowLen r ≤ c) (h2 : c < xi.rowLen r) :
    rowFill B (rowContent mu xi f r) (c - mu.rowLen r) = f r c :=
  eq_rowFill (fun _ _ hx hxy hy => hweak r _ _ hx hxy hy)
    (fun _ hx hy => hbound r _ hx hy) h1 h2

/-- Column strictness between consecutive rows follows from the shifted
inequalities between partial row sums. -/
theorem lt_succ_row
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B)
    (hweak : ∀ r c c', mu.rowLen r ≤ c → c ≤ c' → c' < xi.rowLen r → f r c ≤ f r c')
    (hR : ∀ r i, mu.rowLen (r + 1) + ∑ i' ∈ range (i + 1), rowContent mu xi f (r + 1) i'
        ≤ mu.rowLen r + ∑ i' ∈ range i, rowContent mu xi f r i')
    {r c : ℕ} (h1 : mu.rowLen r ≤ c) (h3 : mu.rowLen (r + 1) ≤ c)
    (h4 : c < xi.rowLen (r + 1)) : f r c < f (r + 1) c := by
  have h2 : c < xi.rowLen r := lt_of_lt_of_le h4 (xi.rowLen_anti r (r + 1) (Nat.le_succ r))
  have hk : f r c < B := hbound r c h1 h2
  have e1 := rowFill_lt_iff (le_of_lt hk) (rowContent mu xi f r) (c - mu.rowLen r)
  have e2 := rowFill_lt_iff (show f r c + 1 ≤ B from hk) (rowContent mu xi f (r + 1))
    (c - mu.rowLen (r + 1))
  rw [eq_rowFill_rowContent hbound hweak h1 h2] at e1
  rw [eq_rowFill_rowContent hbound hweak h3 h4] at e2
  have hstep := hR r (f r c)
  omega

/-- Column strictness between arbitrary rows follows from the consecutive case. -/
theorem lt_of_row_lt
    (hstep : ∀ r c, mu.rowLen r ≤ c → mu.rowLen (r + 1) ≤ c → c < xi.rowLen (r + 1) →
      f r c < f (r + 1) c)
    {r r' c : ℕ} (hr : r < r') (h1 : mu.rowLen r ≤ c) (h4 : c < xi.rowLen r') :
    f r c < f r' c := by
  induction r', hr using Nat.le_induction with
  | base => exact hstep r c h1 (le_trans (mu.rowLen_anti r (r + 1) (Nat.le_succ r)) h1) h4
  | succ n hn ih =>
    exact lt_trans (ih (lt_of_lt_of_le h4 (xi.rowLen_anti n (n + 1) (Nat.le_succ n))))
      (hstep n c (le_trans (mu.rowLen_anti r n (le_of_lt hn)) h1)
        (le_trans (mu.rowLen_anti r (n + 1) (by omega)) h1) h4)

/-! ### Fillings built from a row-content matrix -/

/-- The filling of `xi / mu` whose row `r` carries the value `i` exactly `m r i`
times, in weakly increasing order. -/
noncomputable def ofRowContent (mu xi : YoungDiagram) (B : ℕ) (m : ℕ → ℕ → ℕ) (r c : ℕ) : ℕ :=
  if mu.rowLen r ≤ c ∧ c < xi.rowLen r then rowFill B (m r) (c - mu.rowLen r) else 0

variable {m : ℕ → ℕ → ℕ}

theorem ofRowContent_apply {r c : ℕ} (h1 : mu.rowLen r ≤ c) (h2 : c < xi.rowLen r) :
    ofRowContent mu xi B m r c = rowFill B (m r) (c - mu.rowLen r) := if_pos ⟨h1, h2⟩

theorem ofRowContent_lt (hm : ∀ r, mu.rowLen r + ∑ i ∈ range B, m r i = xi.rowLen r)
    (r c : ℕ) (h1 : mu.rowLen r ≤ c) (h2 : c < xi.rowLen r) :
    ofRowContent mu xi B m r c < B := by
  rw [ofRowContent_apply h1 h2]
  exact rowFill_lt B (m r) (by have := hm r; omega)

theorem ofRowContent_weak (r c c' : ℕ) (h1 : mu.rowLen r ≤ c) (hcc : c ≤ c')
    (h2 : c' < xi.rowLen r) :
    ofRowContent mu xi B m r c ≤ ofRowContent mu xi B m r c' := by
  rw [ofRowContent_apply h1 (by omega), ofRowContent_apply (by omega) h2]
  exact rowFill_mono B (m r) (by omega)

theorem rowContent_ofRowContent (hm : ∀ r, mu.rowLen r + ∑ i ∈ range B, m r i = xi.rowLen r)
    (r : ℕ) {i : ℕ} (hi : i < B) :
    rowContent mu xi (ofRowContent mu xi B m) r i = m r i := by
  have hxi : xi.rowLen r = mu.rowLen r + ∑ j ∈ range B, m r j := (hm r).symm
  rw [rowContent, hxi, ← card_filter_rowFill hi (m r) (mu.rowLen r)]
  exact congrArg Finset.card (Finset.filter_congr fun c hc => by
    rw [ofRowContent_apply (mem_Ico.mp hc).1 (by rw [hxi]; exact (mem_Ico.mp hc).2)])

/-- Away from its own bound the row content of the built filling still agrees
with the matrix. -/
theorem rowContent_ofRowContent_eq (hzero : ∀ r i, B ≤ i → m r i = 0)
    (hm : ∀ r, mu.rowLen r + ∑ i ∈ range B, m r i = xi.rowLen r) (r i : ℕ) :
    rowContent mu xi (ofRowContent mu xi B m) r i = m r i := by
  rcases lt_or_ge i B with h | h
  · exact rowContent_ofRowContent hm r h
  · rw [rowContent_eq_zero (ofRowContent_lt hm) r h, hzero r i h]

/-- Conversely, column strictness at the cell just past the last `i` of row `r`
gives the shifted inequality between partial row sums. -/
theorem sum_le_of_lt_succ_row
    (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B)
    (hweak : ∀ r c c', mu.rowLen r ≤ c → c ≤ c' → c' < xi.rowLen r → f r c ≤ f r c')
    (hcol : ∀ r c, mu.rowLen r ≤ c → mu.rowLen (r + 1) ≤ c → c < xi.rowLen (r + 1) →
      f r c < f (r + 1) c)
    (hle : mu ≤ xi) (r i : ℕ) :
    mu.rowLen (r + 1) + ∑ i' ∈ range (i + 1), rowContent mu xi f (r + 1) i'
      ≤ mu.rowLen r + ∑ i' ∈ range i, rowContent mu xi f r i' := by
  have hrow0 := sum_rowContent_row hbound hle r
  have hrow1 := sum_rowContent_row hbound hle (r + 1)
  have hmu := mu.rowLen_anti r (r + 1) (Nat.le_succ r)
  have hxir := xi.rowLen_anti r (r + 1) (Nat.le_succ r)
  rcases lt_or_ge i B with hiB | hiB
  · by_contra hcon
    have hbnd := sum_rowContent_le hbound (r + 1) (i + 1)
    set c := mu.rowLen r + ∑ i' ∈ range i, rowContent mu xi f r i' with hc
    have h1 : mu.rowLen r ≤ c := by omega
    have h3 : mu.rowLen (r + 1) ≤ c := by omega
    have h4 : c < xi.rowLen (r + 1) := by omega
    have h2 : c < xi.rowLen r := by omega
    have hstrict := hcol r c h1 h3 h4
    have e1 := rowFill_lt_iff (le_of_lt hiB) (rowContent mu xi f r) (c - mu.rowLen r)
    have e2 := rowFill_lt_iff (show i + 1 ≤ B from hiB) (rowContent mu xi f (r + 1))
      (c - mu.rowLen (r + 1))
    rw [eq_rowFill_rowContent hbound hweak h1 h2] at e1
    rw [eq_rowFill_rowContent hbound hweak h3 h4] at e2
    omega
  · rw [sum_rowContent_eq hbound (r + 1) (by omega), sum_rowContent_eq hbound r hiB]
    omega

end SkewFilling

/-! ## Goodness read off from the rows

Stembridge's goodness condition cuts a tableau of straight shape by columns,
while the column strictness of a Littlewood-Richardson tableau cuts it by rows.
The two cuts see the same inequalities: a cut at a column is dominated by the cut
at the row holding the leftmost affected cell, and conversely. -/

namespace GoodTableau

variable {nu kap : YoungDiagram} {T : SemistandardYoungTableau nu}

/-- How often the value `v` occurs in the first `k` rows. -/
noncomputable def rowPrefix (T : SemistandardYoungTableau nu) (v k : ℕ) : ℕ :=
  (nu.cells.filter fun x => x.1 < k ∧ T x.1 x.2 = v).card

theorem rowPrefix_zero (v : ℕ) : rowPrefix T v 0 = 0 := by
  rw [rowPrefix, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun _ _ hx => absurd hx.1 (Nat.not_lt_zero _)

theorem rowPrefix_mono (v : ℕ) {k k' : ℕ} (h : k ≤ k') : rowPrefix T v k ≤ rowPrefix T v k' :=
  card_le_card fun _ hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,
    lt_of_lt_of_le (mem_filter.mp hx).2.1 h, (mem_filter.mp hx).2.2⟩

theorem rowPrefix_succ_of_forall_ne {v i : ℕ} (h : ∀ c, (i, c) ∈ nu → T i c ≠ v) :
    rowPrefix T v (i + 1) = rowPrefix T v i := by
  refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
  refine ⟨fun hy => ⟨?_, hy.2⟩, fun hy => ⟨by omega, hy.2⟩⟩
  rcases Nat.lt_or_ge x.1 i with h1 | h1
  · exact h1
  · exfalso
    have hxi : x.1 = i := by omega
    refine h x.2 ?_ ?_
    · rw [← hxi]
      exact hx
    · rw [← hxi]
      exact hy.2

/-- Every `r + 1` in the first `i + 1` rows lies at or right of the leftmost
`r + 1` of row `i`. -/
theorem rowPrefix_le_colWeight_of_min {i j r : ℕ} (hj : (i, j) ∈ nu) (hval : T i j = r + 1)
    (hmin : ∀ c, (i, c) ∈ nu → T i c = r + 1 → j ≤ c) :
    rowPrefix T (r + 1) (i + 1) ≤ T.colWeight j (r + 1) := by
  refine card_le_card fun x hx => ?_
  rw [mem_filter] at hx ⊢
  obtain ⟨hcell, hrow, hv⟩ := hx
  refine ⟨hcell, ?_, hv⟩
  rcases Nat.lt_or_ge x.1 i with hlt | hge
  · by_contra hcon
    have hxj : (x.1, j) ∈ nu := nu.up_left_mem (le_of_lt hlt) le_rfl hj
    have hcs : T x.1 j < T i j := T.col_strict hlt hj
    have hrw : T x.1 x.2 ≤ T x.1 j := T.row_weak_of_le (le_of_lt (not_le.mp hcon)) hxj
    omega
  · have hxi : x.1 = i := by omega
    refine hmin x.2 ?_ ?_
    · rw [← hxi]
      exact hcell
    · rw [← hxi]
      exact hv

/-- Every `r` at or right of the leftmost `r + 1` of row `i` lies above row `i`. -/
theorem colWeight_le_rowPrefix_of_min {i j r : ℕ} (hval : T i j = r + 1) :
    T.colWeight j r ≤ rowPrefix T r i := by
  refine card_le_card fun x hx => ?_
  rw [mem_filter] at hx ⊢
  obtain ⟨hcell, hcol, hv⟩ := hx
  refine ⟨hcell, ?_, hv⟩
  by_contra hcon
  have hge : i ≤ x.1 := not_lt.mp hcon
  have hxj : (i, x.2) ∈ nu := nu.up_left_mem hge le_rfl hcell
  have h1 : T i j ≤ T i x.2 := T.row_weak_of_le hcol hxj
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [heq] at h1 hval
    omega
  · have h2 : T i x.2 < T x.1 x.2 := T.col_strict hlt hcell
    omega

/-- Every `r + 1` at or right of column `j` lies at or above the row of the
`r + 1` in column `j`. -/
theorem colWeight_le_rowPrefix_of_col {x j r : ℕ} (hval : T x j = r + 1) :
    T.colWeight j (r + 1) ≤ rowPrefix T (r + 1) (x + 1) := by
  refine card_le_card fun y hy => ?_
  rw [mem_filter] at hy ⊢
  obtain ⟨hcell, hcol, hv⟩ := hy
  refine ⟨hcell, ?_, hv⟩
  by_contra hcon
  have hgt : x < y.1 := by omega
  have hyj : (y.1, j) ∈ nu := nu.up_left_mem le_rfl hcol hcell
  have h1 : T y.1 j ≤ T y.1 y.2 := T.row_weak_of_le hcol hcell
  have h2 : T x j < T y.1 j := T.col_strict hgt hyj
  omega

/-- If column `j` holds an `r + 1` but no `r`, every `r` above that `r + 1` lies
at or right of column `j`. -/
theorem rowPrefix_le_colWeight_of_col {x j r : ℕ} (hj : (x, j) ∈ nu) (hval : T x j = r + 1)
    (hno : ∀ y, (y, j) ∈ nu → T y j ≠ r) : rowPrefix T r x ≤ T.colWeight j r := by
  refine card_le_card fun y hy => ?_
  rw [mem_filter] at hy ⊢
  obtain ⟨hcell, hrow, hv⟩ := hy
  refine ⟨hcell, ?_, hv⟩
  have hyj : (y.1, j) ∈ nu := nu.up_left_mem (le_of_lt hrow) le_rfl hj
  have h1 : T y.1 j < T x j := T.col_strict hrow hj
  have h2 : T y.1 j ≠ r := hno y.1 hyj
  by_contra hcon
  have h3 : T y.1 y.2 ≤ T y.1 j := T.row_weak_of_le (le_of_lt (not_le.mp hcon)) hyj
  omega

/-- Cutting at the leftmost `r + 1` of row `i`. -/
theorem sum_le_of_exists {r i : ℕ}
    (hgood : ∀ j, kap.rowLen (r + 1) + T.colWeight j (r + 1) ≤ kap.rowLen r + T.colWeight j r)
    (hex : ∃ c, (i, c) ∈ nu ∧ T i c = r + 1) :
    kap.rowLen (r + 1) + rowPrefix T (r + 1) (i + 1) ≤ kap.rowLen r + rowPrefix T r i := by
  classical
  set S := (range (nu.rowLen i)).filter fun c => T i c = r + 1 with hS
  have hne : S.Nonempty := by
    obtain ⟨c, hc, hv⟩ := hex
    exact ⟨c, mem_filter.mpr ⟨mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp hc), hv⟩⟩
  have hjm := mem_filter.mp (S.min'_mem hne)
  have hjcell : (i, S.min' hne) ∈ nu :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (mem_range.mp hjm.1)
  have hmin : ∀ c, (i, c) ∈ nu → T i c = r + 1 → S.min' hne ≤ c := fun c hc hv =>
    S.min'_le c (mem_filter.mpr ⟨mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp hc), hv⟩)
  have h1 := rowPrefix_le_colWeight_of_min hjcell hjm.2 hmin
  have h2 := colWeight_le_rowPrefix_of_min hjm.2
  have h3 := hgood (S.min' hne)
  omega

/-- **Goodness gives the shifted inequalities between row prefixes.** -/
theorem sum_le_of_good {r : ℕ}
    (hgood : ∀ j, kap.rowLen (r + 1) + T.colWeight j (r + 1) ≤ kap.rowLen r + T.colWeight j r)
    (i : ℕ) :
    kap.rowLen (r + 1) + rowPrefix T (r + 1) (i + 1) ≤ kap.rowLen r + rowPrefix T r i := by
  classical
  induction i with
  | zero =>
    by_cases hex : ∃ c, (0, c) ∈ nu ∧ T 0 c = r + 1
    · exact sum_le_of_exists hgood hex
    · rw [rowPrefix_succ_of_forall_ne fun c hc hv => hex ⟨c, hc, hv⟩, rowPrefix_zero]
      have := kap.rowLen_anti r (r + 1) (Nat.le_succ r)
      omega
  | succ s ih =>
    by_cases hex : ∃ c, (s + 1, c) ∈ nu ∧ T (s + 1) c = r + 1
    · exact sum_le_of_exists hgood hex
    · rw [rowPrefix_succ_of_forall_ne fun c hc hv => hex ⟨c, hc, hv⟩]
      have := rowPrefix_mono (T := T) r (show s ≤ s + 1 by omega)
      omega

/-- **The shifted inequalities between row prefixes give goodness.** -/
theorem good_of_sum_le {r : ℕ}
    (hR : ∀ i, kap.rowLen (r + 1) + rowPrefix T (r + 1) (i + 1) ≤ kap.rowLen r + rowPrefix T r i)
    (j : ℕ) :
    kap.rowLen (r + 1) + T.colWeight j (r + 1) ≤ kap.rowLen r + T.colWeight j r := by
  classical
  suffices h : ∀ d j, nu.rowLen 0 ≤ j + d →
      kap.rowLen (r + 1) + T.colWeight j (r + 1) ≤ kap.rowLen r + T.colWeight j r from
    h (nu.rowLen 0) j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [T.colWeight_eq_zero (by omega), T.colWeight_eq_zero (by omega)]
    have h0 := hR 0
    rw [rowPrefix_zero] at h0
    omega
  | succ n ih =>
    intro j hj
    have hstep1 := T.colWeight_succ j r
    have hstep2 := T.colWeight_succ j (r + 1)
    have hc1 := T.colCell_le_one j r
    have hc2 := T.colCell_le_one j (r + 1)
    rcases Nat.lt_or_ge (T.colCell j r) (T.colCell j (r + 1)) with hlt | hge
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < T.colCell j (r + 1) by omega)
      rw [mem_filter] at hx
      have hxj : (x.1, j) ∈ nu := by
        rw [← hx.2.1]
        exact hx.1
      have hval : T x.1 j = r + 1 := by
        rw [← hx.2.1]
        exact hx.2.2
      have hzero := Finset.filter_eq_empty_iff.mp
        (Finset.card_eq_zero.mp (show T.colCell j r = 0 by omega))
      have hno : ∀ y, (y, j) ∈ nu → T y j ≠ r := fun y hy hv => hzero hy ⟨rfl, hv⟩
      have h1 := colWeight_le_rowPrefix_of_col hval
      have h2 := rowPrefix_le_colWeight_of_col hxj hval hno
      have h3 := hR x.1
      omega
    · have hih := ih (j + 1) (by omega)
      omega

end GoodTableau

/-! ## Reading the two descriptions off the same matrix -/

theorem YoungDiagram.rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  by_contra h
  exact YoungDiagram.notMem_bot (i, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

namespace GoodTableau

variable {nu : YoungDiagram} (T : SemistandardYoungTableau nu)

theorem sum_rowContent_eq_rowPrefix (v k : ℕ) :
    ∑ i ∈ range k, SkewFilling.rowContent ⊥ nu T i v = rowPrefix T v k := by
  rw [SkewFilling.sum_rowContent, rowPrefix, YoungDiagram.cells_bot, Finset.sdiff_empty]

theorem rowPrefix_eq_weight (v : ℕ) {k : ℕ} (hk : nu.colLen 0 ≤ k) :
    rowPrefix T v k = T.weight v :=
  congrArg Finset.card (Finset.filter_congr fun x hx =>
    ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le (lt_of_lt_of_le
      (YoungDiagram.mem_iff_lt_colLen.mp hx) (nu.colLen_anti 0 x.2 (Nat.zero_le _))) hk, h⟩⟩)

end GoodTableau

/-- Goodness compares the column weights of consecutive values. -/
theorem Stembridge.isGood_iff {N : ℕ} {nu kap : YoungDiagram} (T : BoundedSemistandardTableau N nu) :
    Stembridge.IsGood kap.rowLen T ↔ ∀ r, r + 1 < N → ∀ j,
      kap.rowLen (r + 1) + T.tableau.colWeight j (r + 1)
        ≤ kap.rowLen r + T.tableau.colWeight j r := by
  simp only [Stembridge.IsGood, Stembridge.Fails, Stembridge.prof, not_exists, not_and, not_le]
  constructor
  · intro h r hr j
    have := h j r hr
    omega
  · intro h j i hi
    have := h i hi j
    omega

namespace LittlewoodRichardsonTableau

variable {a b : ℕ} {mu : YoungDiagramOfSize a} {nu : YoungDiagramOfSize b}
  {xi : YoungDiagramOfSize (a + b)} (U : LittlewoodRichardsonTableau mu nu xi)

theorem entryAt_coe (c : ↥(xi.val.cells \ mu.val.cells)) :
    U.entryAt (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 = (U.entry c : ℕ) := U.entryAt_eq c.2

/-- Counting the cells carrying a value, by rows. -/
theorem card_filter_eq_sum (f : ℕ → ℕ → ℕ) (i : ℕ) :
    (Finset.univ.filter fun c : ↥(xi.val.cells \ mu.val.cells) =>
        f (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 = i).card
      = ∑ r ∈ range (a + b), SkewFilling.rowContent mu.val xi.val f r i := by
  classical
  have h1 : ((xi.val.cells \ mu.val.cells).filter fun x => x.1 < a + b ∧ f x.1 x.2 = i)
      = ((xi.val.cells \ mu.val.cells).filter fun x => f x.1 x.2 = i) := by
    refine Finset.filter_congr fun x hx => ?_
    have hlt : x.1 < a + b := by
      simpa [xi.property] using xi.val.cell_fst_lt_card (Finset.mem_sdiff.mp hx).1
    tauto
  rw [SkewFilling.sum_rowContent, h1,
    Finset.card_filter_attach_coe (xi.val.cells \ mu.val.cells) fun x => f x.1 x.2 = i]

/-- The content condition counts each value down the columns of the transposed
row-content matrix. -/
theorem sum_rowContent_col {i : ℕ} (hi : i < b) :
    ∑ r ∈ range (a + b), SkewFilling.rowContent mu.val xi.val U.entryAt r i
      = nu.val.rowLen i := by
  rw [← card_filter_eq_sum U.entryAt i, ← U.content ⟨i, hi⟩]
  exact congrArg Finset.card (Finset.filter_congr fun c _ => by
    rw [U.entryAt_coe c]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩)

end LittlewoodRichardsonTableau

/-! ## The two tableaux built from a row-content matrix -/

namespace LittlewoodRichardsonTableau

variable {a b : ℕ} {mu : YoungDiagramOfSize a} {nu : YoungDiagramOfSize b}
  {xi : YoungDiagramOfSize (a + b)} {M : ℕ → ℕ → ℕ}

/-- The Littlewood-Richardson tableau whose rows carry prescribed contents. -/
noncomputable def ofMatrix
    (hshape : mu.val ≤ xi.val)
    (hzero : ∀ r i, b ≤ i → M r i = 0)
    (hrow : ∀ r, mu.val.rowLen r + ∑ i ∈ range b, M r i = xi.val.rowLen r)
    (hcol : ∀ i, i < b → ∑ r ∈ range (a + b), M r i = nu.val.rowLen i)
    (hR : ∀ r i, ∑ r' ∈ range (r + 1), M r' (i + 1) ≤ ∑ r' ∈ range r, M r' i)
    (hRmu : ∀ r i, mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), M (r + 1) i'
        ≤ mu.val.rowLen r + ∑ i' ∈ range i, M r i') :
    LittlewoodRichardsonTableau mu nu xi where
  shape := hshape
  entry := fun c => ⟨SkewFilling.ofRowContent mu.val xi.val b M (c : ℕ × ℕ).1 (c : ℕ × ℕ).2,
    SkewFilling.ofRowContent_lt hrow _ _ (YoungDiagram.mem_sdiff_cells.mp c.2).1 (YoungDiagram.mem_sdiff_cells.mp c.2).2⟩
  row_weak := fun {c d} hr hc => Fin.le_def.mpr (by
    have h1 := YoungDiagram.mem_sdiff_cells.mp c.2
    have h2 := YoungDiagram.mem_sdiff_cells.mp d.2
    show SkewFilling.ofRowContent mu.val xi.val b M _ _ ≤ _
    rw [hr]
    exact SkewFilling.ofRowContent_weak _ _ _ (by rw [← hr]; exact h1.1) (le_of_lt hc) h2.2)
  col_strict := fun {c d} hr hc => Fin.lt_def.mpr (by
    have h1 := YoungDiagram.mem_sdiff_cells.mp c.2
    have h2 := YoungDiagram.mem_sdiff_cells.mp d.2
    show SkewFilling.ofRowContent mu.val xi.val b M _ _ < _
    rw [hr]
    refine SkewFilling.lt_of_row_lt (fun r' c' hc1 hc2 hc3 =>
      SkewFilling.lt_succ_row (SkewFilling.ofRowContent_lt hrow)
        (fun r'' => SkewFilling.ofRowContent_weak r'') ?_ hc1 hc2 hc3)
      hc (by rw [← hr]; exact h1.1) h2.2
    intro r' i'
    simp only [Finset.sum_congr rfl fun j (_ : j ∈ range (i' + 1)) =>
        SkewFilling.rowContent_ofRowContent_eq hzero hrow (r' + 1) j,
      Finset.sum_congr rfl fun j (_ : j ∈ range i') =>
        SkewFilling.rowContent_ofRowContent_eq hzero hrow r' j]
    exact hRmu r' i')
  content := fun i => by
    simp only [Fin.ext_iff]
    rw [card_filter_eq_sum (mu := mu) (xi := xi) (SkewFilling.ofRowContent mu.val xi.val b M) i.1,
      Finset.sum_congr rfl fun r (_ : r ∈ range (a + b)) =>
        SkewFilling.rowContent_ofRowContent_eq hzero hrow r i.1]
    exact hcol i.1 i.isLt
  lattice := fun d i => by
    rw [Finset.card_filter_attach_coe (xi.val.cells \ mu.val.cells)
        (fun x => LittlewoodRichardson.readingLE x (d : ℕ × ℕ) ∧
          SkewFilling.ofRowContent mu.val xi.val b M x.1 x.2 = i.1 + 1),
      Finset.card_filter_attach_coe (xi.val.cells \ mu.val.cells)
        (fun x => LittlewoodRichardson.readingLE x (d : ℕ × ℕ) ∧
          SkewFilling.ofRowContent mu.val xi.val b M x.1 x.2 = i.1)]
    refine SkewFilling.prefixCount_succ_le (fun r i' => ?_) _ _
    rw [Finset.sum_congr rfl fun j (_ : j ∈ range (r + 1)) =>
        SkewFilling.rowContent_ofRowContent_eq hzero hrow j (i' + 1),
      Finset.sum_congr rfl fun j (_ : j ∈ range r) =>
        SkewFilling.rowContent_ofRowContent_eq hzero hrow j i']
    exact hR r i'

theorem val_entry_ofMatrix
    (hshape : mu.val ≤ xi.val)
    (hzero : ∀ r i, b ≤ i → M r i = 0)
    (hrow : ∀ r, mu.val.rowLen r + ∑ i ∈ range b, M r i = xi.val.rowLen r)
    (hcol : ∀ i, i < b → ∑ r ∈ range (a + b), M r i = nu.val.rowLen i)
    (hR : ∀ r i, ∑ r' ∈ range (r + 1), M r' (i + 1) ≤ ∑ r' ∈ range r, M r' i)
    (hRmu : ∀ r i, mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), M (r + 1) i'
        ≤ mu.val.rowLen r + ∑ i' ∈ range i, M r i')
    (c : ↥(xi.val.cells \ mu.val.cells)) :
    (((ofMatrix hshape hzero hrow hcol hR hRmu).entry c : Fin b) : ℕ)
      = SkewFilling.ofRowContent mu.val xi.val b M (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 := rfl

end LittlewoodRichardsonTableau

namespace GoodTableau

variable {a b : ℕ} {nu : YoungDiagramOfSize b} {M : ℕ → ℕ → ℕ}

theorem bot_rowLen_add_sum (hcol : ∀ i, ∑ r ∈ range (a + b), M r i = nu.val.rowLen i) (i : ℕ) :
    (⊥ : YoungDiagram).rowLen i + ∑ r ∈ range (a + b), M r i = nu.val.rowLen i := by
  rw [YoungDiagram.rowLen_bot, Nat.zero_add]
  exact hcol i

/-- The tableau of shape `nu` whose row `i` lists, weakly increasing, the rows of
`xi` in which the value `i` is placed. -/
noncomputable def ofMatrix
    (hzero : ∀ r i, a + b ≤ r → M r i = 0)
    (hcol : ∀ i, ∑ r ∈ range (a + b), M r i = nu.val.rowLen i)
    (hR : ∀ r i, ∑ r' ∈ range (r + 1), M r' (i + 1) ≤ ∑ r' ∈ range r, M r' i) :
    BoundedSemistandardTableau (a + b) nu.val where
  tableau :=
    { entry := SkewFilling.ofRowContent ⊥ nu.val (a + b) fun i r => M r i
      row_weak' := fun {i j1 j2} hj hcell =>
        SkewFilling.ofRowContent_weak i j1 j2 (by rw [YoungDiagram.rowLen_bot]; exact Nat.zero_le _)
          (le_of_lt hj) (YoungDiagram.mem_iff_lt_rowLen.mp hcell)
      col_strict' := fun {i1 i2 j} hi hcell => by
        refine SkewFilling.lt_of_row_lt (fun i' j' h1 h2 h3 =>
          SkewFilling.lt_succ_row (SkewFilling.ofRowContent_lt (bot_rowLen_add_sum hcol))
            (fun i'' => SkewFilling.ofRowContent_weak i'') (fun i'' v => ?_) h1 h2 h3) hi
          (by rw [YoungDiagram.rowLen_bot]; exact Nat.zero_le _)
          (YoungDiagram.mem_iff_lt_rowLen.mp hcell)
        rw [YoungDiagram.rowLen_bot, YoungDiagram.rowLen_bot,
          Finset.sum_congr rfl fun w (_ : w ∈ range (v + 1)) =>
            SkewFilling.rowContent_ofRowContent_eq (fun i''' r hr => hzero r i''' hr)
              (bot_rowLen_add_sum hcol) (i'' + 1) w,
          Finset.sum_congr rfl fun w (_ : w ∈ range v) =>
            SkewFilling.rowContent_ofRowContent_eq (fun i''' r hr => hzero r i''' hr)
              (bot_rowLen_add_sum hcol) i'' w]
        have := hR v i''
        omega
      zeros' := fun {i j} hcell =>
        if_neg fun h => hcell (YoungDiagram.mem_iff_lt_rowLen.mpr h.2) }
  entry_lt := fun cell hcell =>
    SkewFilling.ofRowContent_lt (bot_rowLen_add_sum hcol) cell.1 cell.2
      (by rw [YoungDiagram.rowLen_bot]; exact Nat.zero_le _)
      (YoungDiagram.mem_iff_lt_rowLen.mp hcell)

variable {mu : YoungDiagramOfSize a} {xi : YoungDiagramOfSize (a + b)}
  {hzero : ∀ r i, a + b ≤ r → M r i = 0}
  {hcol : ∀ i, ∑ r ∈ range (a + b), M r i = nu.val.rowLen i}
  {hR : ∀ r i, ∑ r' ∈ range (r + 1), M r' (i + 1) ≤ ∑ r' ∈ range r, M r' i}

theorem sum_rowPrefix_ofMatrix (v k : ℕ) :
    rowPrefix (ofMatrix hzero hcol hR).tableau v k = ∑ i ∈ range k, M v i := by
  rw [← sum_rowContent_eq_rowPrefix]
  exact Finset.sum_congr rfl fun i _ =>
    SkewFilling.rowContent_ofRowContent_eq (fun i' r hr => hzero r i' hr)
      (bot_rowLen_add_sum hcol) i v

/-- The built tableau is good for `mu` exactly when the shifted partial row sums
decrease. -/
theorem isGood_ofMatrix
    (hRmu : ∀ r i, mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), M (r + 1) i'
        ≤ mu.val.rowLen r + ∑ i' ∈ range i, M r i') :
    Stembridge.IsGood mu.val.rowLen (ofMatrix hzero hcol hR) := by
  rw [Stembridge.isGood_iff]
  refine fun r _ j => good_of_sum_le (fun i => ?_) j
  rw [sum_rowPrefix_ofMatrix, sum_rowPrefix_ofMatrix]
  exact hRmu r i

/-- The built tableau lengthens the rows of `mu` to `xi`. -/
theorem addWeight_ofMatrix
    (hRmu : ∀ r i, mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), M (r + 1) i'
        ≤ mu.val.rowLen r + ∑ i' ∈ range i, M r i')
    (hrow : ∀ r, mu.val.rowLen r + ∑ i ∈ range b, M r i = xi.val.rowLen r) :
    Stembridge.addWeight mu.val (ofMatrix hzero hcol hR) = xi.val := by
  refine YoungDiagram.ext_of_rowLen fun r => ?_
  rcases lt_or_ge r (a + b) with h | h
  · rw [Stembridge.rowLen_addWeight (isGood_ofMatrix hRmu) ⟨r, h⟩,
      ← rowPrefix_eq_weight (ofMatrix hzero hcol hR).tableau r
        (YoungDiagramOfSize.colLen_zero_le nu), sum_rowPrefix_ofMatrix]
    exact hrow r
  · rw [YoungDiagram.rowLen_eq_zero
      (Stembridge.colLen_addWeight (isGood_ofMatrix hRmu)) h,
      YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le xi) h]

theorem tableau_ofMatrix (i c : ℕ) :
    (ofMatrix hzero hcol hR).tableau i c
      = SkewFilling.ofRowContent ⊥ nu.val (a + b) (fun i r => M r i) i c := rfl

end GoodTableau

/-! ## The row-content matrix of each kind of tableau -/

namespace SkewFilling

variable {mu xi : YoungDiagram} {f : ℕ → ℕ → ℕ} {B : ℕ}

theorem rowContent_eq_zero_of_short {r : ℕ} (h : xi.rowLen r ≤ mu.rowLen r) (i : ℕ) :
    rowContent mu xi f r i = 0 := by
  rw [rowContent, Finset.Ico_eq_empty (by omega), Finset.filter_empty, Finset.card_empty]

theorem prefixCount_eq_zero (hbound : ∀ r c, mu.rowLen r ≤ c → c < xi.rowLen r → f r c < B)
    (d : ℕ × ℕ) {i : ℕ} (hi : B ≤ i) : prefixCount mu xi f d i = 0 := by
  rw [prefixCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hval
  have hmem := YoungDiagram.mem_sdiff_cells.mp hx
  exact absurd (hval.2 ▸ hbound x.1 x.2 hmem.1 hmem.2) (by omega)

end SkewFilling

namespace LittlewoodRichardsonTableau

variable {a b : ℕ} {mu : YoungDiagramOfSize a} {nu : YoungDiagramOfSize b}
  {xi : YoungDiagramOfSize (a + b)} (U : LittlewoodRichardsonTableau mu nu xi)

/-- How often `U` places the value `i` in row `r`. -/
noncomputable def contentMatrix (r i : ℕ) : ℕ :=
  SkewFilling.rowContent mu.val xi.val U.entryAt r i

theorem contentMatrix_eq_zero_col (r : ℕ) {i : ℕ} (hi : b ≤ i) : U.contentMatrix r i = 0 :=
  SkewFilling.rowContent_eq_zero (mu := mu.val) (xi := xi.val) (f := U.entryAt) (B := b)
    (fun _ _ h1 h2 => U.entryAt_lt ⟨h1, h2⟩) r hi

theorem contentMatrix_eq_zero_row {r : ℕ} (hr : a + b ≤ r) (i : ℕ) : U.contentMatrix r i = 0 :=
  SkewFilling.rowContent_eq_zero_of_short
    (by rw [YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le xi) hr]; omega) i

theorem sum_contentMatrix_row (r : ℕ) :
    mu.val.rowLen r + ∑ i ∈ range b, U.contentMatrix r i = xi.val.rowLen r :=
  SkewFilling.sum_rowContent_row (mu := mu.val) (xi := xi.val) (f := U.entryAt) (B := b)
    (fun _ _ h1 h2 => U.entryAt_lt ⟨h1, h2⟩) U.shape r

theorem sum_contentMatrix_col (i : ℕ) :
    ∑ r ∈ range (a + b), U.contentMatrix r i = nu.val.rowLen i := by
  rcases lt_or_ge i b with hi | hi
  · exact U.sum_rowContent_col hi
  · rw [Finset.sum_congr rfl fun r (_ : r ∈ range (a + b)) => U.contentMatrix_eq_zero_col r hi,
      Finset.sum_const, smul_eq_mul, mul_zero,
      YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le nu) hi]

theorem prefixCount_entryAt (d : ℕ × ℕ) (k : ℕ) :
    (Finset.univ.filter fun c : ↥(xi.val.cells \ mu.val.cells) =>
        LittlewoodRichardson.readingLE (c : ℕ × ℕ) d ∧ ((U.entry c : Fin b) : ℕ) = k).card
      = SkewFilling.prefixCount mu.val xi.val U.entryAt d k := by
  have hc : (Finset.univ.filter fun c : ↥(xi.val.cells \ mu.val.cells) =>
        LittlewoodRichardson.readingLE (c : ℕ × ℕ) d ∧ ((U.entry c : Fin b) : ℕ) = k)
      = (Finset.univ.filter fun c : ↥(xi.val.cells \ mu.val.cells) =>
        LittlewoodRichardson.readingLE ((c : ℕ × ℕ)) d ∧
          U.entryAt (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 = k) :=
    Finset.filter_congr fun c _ => by rw [U.entryAt_coe c]
  rw [hc, Finset.card_filter_attach_coe (xi.val.cells \ mu.val.cells)
    fun x => LittlewoodRichardson.readingLE x d ∧ U.entryAt x.1 x.2 = k]
  rfl

theorem prefixCount_le_of_lattice (d : ↥(xi.val.cells \ mu.val.cells)) (i : Fin (b - 1)) :
    SkewFilling.prefixCount mu.val xi.val U.entryAt (d : ℕ × ℕ) (i.1 + 1)
      ≤ SkewFilling.prefixCount mu.val xi.val U.entryAt (d : ℕ × ℕ) i.1 := by
  rw [← U.prefixCount_entryAt (d : ℕ × ℕ) (i.1 + 1), ← U.prefixCount_entryAt (d : ℕ × ℕ) i.1]
  exact U.lattice d i

theorem sum_contentMatrix_lattice (r i : ℕ) :
    ∑ r' ∈ range (r + 1), U.contentMatrix r' (i + 1) ≤ ∑ r' ∈ range r, U.contentMatrix r' i := by
  refine SkewFilling.sum_rowContent_succ_le (mu := mu.val) (xi := xi.val) (f := U.entryAt)
    (fun _ _ _ h1 h2 h3 => U.entryAt_row_weak h1 h2 h3) (fun d hd i' => ?_) r i
  rcases lt_or_ge (i' + 1) b with hi | hi
  · exact U.prefixCount_le_of_lattice ⟨d, hd⟩ ⟨i', by omega⟩
  · rw [SkewFilling.prefixCount_eq_zero (fun _ _ ha hb => U.entryAt_lt ⟨ha, hb⟩) d hi]
    exact Nat.zero_le _

theorem sum_contentMatrix_column (r i : ℕ) :
    mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), U.contentMatrix (r + 1) i'
      ≤ mu.val.rowLen r + ∑ i' ∈ range i, U.contentMatrix r i' :=
  SkewFilling.sum_le_of_lt_succ_row (mu := mu.val) (xi := xi.val) (f := U.entryAt) (B := b)
    (fun _ _ h1 h2 => U.entryAt_lt ⟨h1, h2⟩)
    (fun _ _ _ h1 h2 h3 => U.entryAt_row_weak h1 h2 h3)
    (fun r' _ h1 h2 h3 => U.entryAt_col_strict h1
      (lt_of_lt_of_le h3 (xi.val.rowLen_anti r' (r' + 1) (Nat.le_succ r'))) h2 h3
      (Nat.lt_succ_self r')) U.shape r i

end LittlewoodRichardsonTableau

namespace GoodTableau

variable {a b : ℕ} {mu : YoungDiagramOfSize a} {nu : YoungDiagramOfSize b}
  {xi : YoungDiagramOfSize (a + b)} (T : BoundedSemistandardTableau (a + b) nu.val)

/-- How often `T` places the value `r` in row `i`. -/
noncomputable def contentMatrix (r i : ℕ) : ℕ :=
  SkewFilling.rowContent ⊥ nu.val T.tableau i r

theorem entry_bound (i c : ℕ) (_ : (⊥ : YoungDiagram).rowLen i ≤ c) (hc : c < nu.val.rowLen i) :
    T.tableau i c < a + b :=
  T.entry_lt (i, c) (YoungDiagram.mem_iff_lt_rowLen.mpr hc)

theorem contentMatrix_eq_zero_row {r : ℕ} (hr : a + b ≤ r) (i : ℕ) : contentMatrix T r i = 0 :=
  SkewFilling.rowContent_eq_zero (mu := ⊥) (xi := nu.val) (f := T.tableau) (B := a + b)
    (entry_bound T) i hr

theorem contentMatrix_eq_zero_col (r : ℕ) {i : ℕ} (hi : b ≤ i) : contentMatrix T r i = 0 :=
  SkewFilling.rowContent_eq_zero_of_short (mu := ⊥) (xi := nu.val) (f := T.tableau)
    (by rw [YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le nu) hi]; omega) r

theorem sum_contentMatrix_col (i : ℕ) :
    ∑ r ∈ range (a + b), contentMatrix T r i = nu.val.rowLen i := by
  have h := SkewFilling.sum_rowContent_row (mu := ⊥) (xi := nu.val) (f := T.tableau)
    (B := a + b) (entry_bound T) bot_le i
  rw [YoungDiagram.rowLen_bot, Nat.zero_add] at h
  exact h

theorem sum_contentMatrix_lattice (r i : ℕ) :
    ∑ r' ∈ range (r + 1), contentMatrix T r' (i + 1)
      ≤ ∑ r' ∈ range r, contentMatrix T r' i := by
  have h := SkewFilling.sum_le_of_lt_succ_row (mu := ⊥) (xi := nu.val) (f := T.tableau)
    (B := a + b) (entry_bound T)
    (fun i' c c' _ hcc h3 => T.tableau.row_weak_of_le hcc
      (YoungDiagram.mem_iff_lt_rowLen.mpr h3))
    (fun i' c _ _ h3 => T.tableau.col_strict (Nat.lt_succ_self i')
      (YoungDiagram.mem_iff_lt_rowLen.mpr h3)) bot_le i r
  rw [YoungDiagram.rowLen_bot, YoungDiagram.rowLen_bot, Nat.zero_add, Nat.zero_add] at h
  exact h

theorem sum_contentMatrix_eq_rowPrefix (v k : ℕ) :
    ∑ i ∈ range k, contentMatrix T v i = rowPrefix T.tableau v k :=
  sum_rowContent_eq_rowPrefix T.tableau v k

variable {T} (hgood : Stembridge.IsGood mu.val.rowLen T)
  (hxi : Stembridge.addWeight mu.val T = xi.val)

include hgood hxi in
theorem sum_contentMatrix_row (r : ℕ) :
    mu.val.rowLen r + ∑ i ∈ range b, contentMatrix T r i = xi.val.rowLen r := by
  rcases lt_or_ge r (a + b) with h | h
  · rw [sum_contentMatrix_eq_rowPrefix,
      rowPrefix_eq_weight T.tableau r (YoungDiagramOfSize.colLen_zero_le nu), ← hxi]
    exact (Stembridge.rowLen_addWeight hgood ⟨r, h⟩).symm
  · rw [YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le mu) (by omega),
      YoungDiagram.rowLen_eq_zero (YoungDiagramOfSize.colLen_zero_le xi) h,
      Finset.sum_congr rfl fun i (_ : i ∈ range b) => contentMatrix_eq_zero_row T h i]
    simp

include hgood in
theorem sum_contentMatrix_column (r i : ℕ) :
    mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), contentMatrix T (r + 1) i'
      ≤ mu.val.rowLen r + ∑ i' ∈ range i, contentMatrix T r i' := by
  rw [sum_contentMatrix_eq_rowPrefix, sum_contentMatrix_eq_rowPrefix]
  rcases lt_or_ge (r + 1) (a + b) with h | h
  · exact sum_le_of_good (fun j => (Stembridge.isGood_iff T).mp hgood r h j) i
  · rw [← sum_contentMatrix_eq_rowPrefix,
      Finset.sum_congr rfl fun i' _ => contentMatrix_eq_zero_row T h i', Finset.sum_const]
    have := mu.val.rowLen_anti r (r + 1) (Nat.le_succ r)
    simp only [smul_eq_mul, mul_zero]
    omega

end GoodTableau

/-! ## The two index sets agree -/

theorem YoungDiagram.le_of_rowLen_le {mu xi : YoungDiagram}
    (h : ∀ r, mu.rowLen r ≤ xi.rowLen r) : mu ≤ xi := by
  intro c hc
  exact YoungDiagram.mem_iff_lt_rowLen.mpr
    (lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hc) (h c.1))

namespace LittlewoodRichardsonTableau

variable {a b : ℕ} {mu : YoungDiagramOfSize a} {nu : YoungDiagramOfSize b}
  {xi : YoungDiagramOfSize (a + b)} {M : ℕ → ℕ → ℕ}

theorem contentMatrix_ofMatrix
    (hshape : mu.val ≤ xi.val)
    (hzero : ∀ r i, b ≤ i → M r i = 0)
    (hrow : ∀ r, mu.val.rowLen r + ∑ i ∈ range b, M r i = xi.val.rowLen r)
    (hcol : ∀ i, i < b → ∑ r ∈ range (a + b), M r i = nu.val.rowLen i)
    (hR : ∀ r i, ∑ r' ∈ range (r + 1), M r' (i + 1) ≤ ∑ r' ∈ range r, M r' i)
    (hRmu : ∀ r i, mu.val.rowLen (r + 1) + ∑ i' ∈ range (i + 1), M (r + 1) i'
        ≤ mu.val.rowLen r + ∑ i' ∈ range i, M r i') :
    (ofMatrix hshape hzero hrow hcol hR hRmu).contentMatrix = M := by
  funext r i
  rw [contentMatrix, ← SkewFilling.rowContent_ofRowContent_eq hzero hrow r i]
  refine congrArg Finset.card (Finset.filter_congr fun c hc => ?_)
  rw [entryAt_eq _ (YoungDiagram.mem_sdiff_cells.mpr ⟨(mem_Ico.mp hc).1, (mem_Ico.mp hc).2⟩)]
  rfl

theorem _root_.GoodTableau.contentMatrix_ofMatrix
    (hzero : ∀ r i, a + b ≤ r → M r i = 0)
    (hcol : ∀ i, ∑ r ∈ range (a + b), M r i = nu.val.rowLen i)
    (hR : ∀ r i, ∑ r' ∈ range (r + 1), M r' (i + 1) ≤ ∑ r' ∈ range r, M r' i) :
    GoodTableau.contentMatrix (GoodTableau.ofMatrix hzero hcol hR) = M :=
  funext fun r => funext fun i =>
    SkewFilling.rowContent_ofRowContent_eq (fun i' r' hr' => hzero r' i' hr')
      (GoodTableau.bot_rowLen_add_sum hcol) i r

variable (mu nu xi)

/-- **Littlewood-Richardson tableaux are Stembridge's good tableaux.**  Both are
determined by the same row-content matrix, read along rows in one case and along
columns in the other. -/
noncomputable def stembridgeEquiv :
    LittlewoodRichardsonTableau mu nu xi ≃
      {T : BoundedSemistandardTableau (a + b) nu.val //
        Stembridge.IsGood mu.val.rowLen T ∧ Stembridge.addWeight mu.val T = xi.val} where
  toFun U :=
    ⟨GoodTableau.ofMatrix (fun r i hr => U.contentMatrix_eq_zero_row hr i)
        U.sum_contentMatrix_col U.sum_contentMatrix_lattice,
      GoodTableau.isGood_ofMatrix U.sum_contentMatrix_column,
      GoodTableau.addWeight_ofMatrix U.sum_contentMatrix_column U.sum_contentMatrix_row⟩
  invFun T := ofMatrix
    (YoungDiagram.le_of_rowLen_le fun r => by
      have := GoodTableau.sum_contentMatrix_row (xi := xi) T.2.1 T.2.2 r
      omega)
    (fun r i hi => GoodTableau.contentMatrix_eq_zero_col T.val r hi)
    (GoodTableau.sum_contentMatrix_row (xi := xi) T.2.1 T.2.2)
    (fun i _ => GoodTableau.sum_contentMatrix_col T.val i)
    (GoodTableau.sum_contentMatrix_lattice T.val)
    (GoodTableau.sum_contentMatrix_column T.2.1)
  left_inv U := by
    refine LittlewoodRichardsonTableau.ext (funext fun c => Fin.ext ?_)
    have hcell := YoungDiagram.mem_sdiff_cells.mp c.2
    rw [val_entry_ofMatrix, GoodTableau.contentMatrix_ofMatrix,
      SkewFilling.ofRowContent_apply hcell.1 hcell.2, ← U.entryAt_coe c]
    exact SkewFilling.eq_rowFill_rowContent (mu := mu.val) (xi := xi.val) (f := U.entryAt)
      (B := b) (fun _ _ h1 h2 => U.entryAt_lt ⟨h1, h2⟩)
      (fun _ _ _ h1 h2 h3 => U.entryAt_row_weak h1 h2 h3) hcell.1 hcell.2
  right_inv T := by
    refine Subtype.ext (BoundedSemistandardTableau.ext fun i c => ?_)
    rw [GoodTableau.tableau_ofMatrix, contentMatrix_ofMatrix]
    rcases lt_or_ge c (nu.val.rowLen i) with hc | hc
    · rw [SkewFilling.ofRowContent_apply (by rw [YoungDiagram.rowLen_bot]; exact Nat.zero_le _) hc]
      exact SkewFilling.eq_rowFill_rowContent (mu := ⊥) (xi := nu.val) (f := T.val.tableau)
        (B := a + b) (GoodTableau.entry_bound T.val)
        (fun _ _ _ _ hcc h3 => T.val.tableau.row_weak_of_le hcc
          (YoungDiagram.mem_iff_lt_rowLen.mpr h3))
        (by rw [YoungDiagram.rowLen_bot]; exact Nat.zero_le _) hc
    · rw [SkewFilling.ofRowContent, if_neg (by omega),
        T.val.tableau.zeros
          (fun hmem => absurd (YoungDiagram.mem_iff_lt_rowLen.mp hmem) (by omega))]

end LittlewoodRichardsonTableau

/-- **The Littlewood-Richardson coefficient is Stembridge's count.** -/
theorem littlewoodRichardsonCoefficient_eq_stembridgeCount {a b : ℕ}
    (mu : YoungDiagramOfSize a) (nu : YoungDiagramOfSize b) (xi : YoungDiagramOfSize (a + b)) :
    littlewoodRichardsonCoefficient mu nu xi = Stembridge.stembridgeCount mu nu xi :=
  Nat.card_congr (LittlewoodRichardsonTableau.stembridgeEquiv mu nu xi)

/-- **The Littlewood-Richardson rule for Schur polynomials.**  `s_mu · s_nu` is
the sum of the Schur polynomials of the shapes `xi`, each taken as often as there
are Littlewood-Richardson tableaux of shape `xi / mu` and content `nu`. -/
theorem schurPoly_mul_schurPoly_eq_littlewoodRichardson {a b : ℕ}
    (mu : YoungDiagramOfSize a) (nu : YoungDiagramOfSize b) :
    schurPoly (a + b) mu.val * schurPoly (a + b) nu.val =
      ∑ xi : YoungDiagramOfSize (a + b),
        MvPolynomial.C (littlewoodRichardsonCoefficient mu nu xi : ℤ) *
          schurPoly (a + b) xi.val := by
  rw [Stembridge.schurPoly_mul_schurPoly_eq_sum]
  exact Finset.sum_congr rfl fun xi _ => by
    rw [littlewoodRichardsonCoefficient_eq_stembridgeCount]
