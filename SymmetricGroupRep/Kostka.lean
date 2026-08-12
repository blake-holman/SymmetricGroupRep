import SymmetricGroupRep.SemistandardHom
import SymmetricGroupRep.YoungPermutation
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Combinatorics.Young.SemistandardTableau

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # Kostka numbers and Young's rule

Mathlib supplies semistandard Young tableaux with natural-number entries.  We
add a finite content condition and use these tableaux to index Kostka numbers.
-/

/-- A semistandard tableau of a fixed shape and weight.

Mathlib's tableau entries are zero-based: entry `i` here corresponds to entry
`i + 1` in the usual positive-integer convention. -/
structure WeightedSemistandardTableau {n : ℕ}
    (shape weight : YoungDiagramOfSize n) where
  tableau : SemistandardYoungTableau shape.val
  entry_lt : ∀ cell ∈ shape.val.cells, tableau cell.1 cell.2 < n
  content : ∀ entry : Fin n,
    (shape.val.cells.filter fun cell => tableau cell.1 cell.2 = entry).card =
      weight.val.rowLen entry

namespace WeightedSemistandardTableau

/-- The bounded entries of a weighted semistandard tableau. -/
def entries {n : ℕ} {shape weight : YoungDiagramOfSize n}
    (T : WeightedSemistandardTableau shape weight) :
    (cell : ↥shape.val.cells) → Fin n :=
  fun cell => ⟨T.tableau cell.1.1 cell.1.2, T.entry_lt cell.1 cell.2⟩

private theorem entries_injective {n : ℕ} {shape weight : YoungDiagramOfSize n} :
    Function.Injective
      (entries : WeightedSemistandardTableau shape weight →
        ((cell : ↥shape.val.cells) → Fin n)) := by
  intro T U hequal
  cases T with
  | mk T hT wT =>
    cases U with
    | mk U hU wU =>
      congr 1
      apply SemistandardYoungTableau.ext
      intro row column
      by_cases hcell : (row, column) ∈ shape.val.cells
      · have hentry := congrFun hequal ⟨(row, column), hcell⟩
        exact congrArg Fin.val hentry
      · rw [T.zeros (by simpa using hcell), U.zeros (by simpa using hcell)]

noncomputable instance {n : ℕ} (shape weight : YoungDiagramOfSize n) :
    Finite (WeightedSemistandardTableau shape weight) :=
  Finite.of_injective entries entries_injective

end WeightedSemistandardTableau

/-- The Kostka number `K_(shape,weight)`. -/
noncomputable def kostkaNumber {n : ℕ}
    (shape weight : YoungDiagramOfSize n) : ℕ :=
  Nat.card (WeightedSemistandardTableau shape weight)

/-- A shape of size `n` has no row past row `n`. -/
private theorem rowLen_eq_zero_of_le {n : ℕ} (mu : YoungDiagramOfSize n) {row : ℕ}
    (hrow : n ≤ row) : mu.val.rowLen row = 0 := by
  by_contra hne
  have hlt : row < n := Tabloid.cell_fst_lt (mu := mu)
    ⟨(row, 0), YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)⟩
  omega

namespace YoungTableau

variable {n : ℕ} {lam mu : YoungDiagramOfSize n}

/-- A tableau matches its labels with the cells of its shape, so a condition on cells and the
condition it becomes on labels hold equally often. -/
private theorem card_filter_cells (t : YoungTableau lam)
    (p : ℕ → ℕ → Prop) [∀ row column, Decidable (p row column)]
    (q : Fin n → Prop) [DecidablePred q] (hpq : ∀ i : Fin n, p (t.row i) (t.column i) ↔ q i) :
    (lam.val.cells.filter fun cell => p cell.1 cell.2).card =
      (Finset.univ.filter q).card := by
  refine (Finset.card_nbij (fun i => (t.row i, t.column i)) (fun i hi => ?_)
    (fun i _ j _ hij => t.row_column_injective hij) fun c hc => ?_).symm
  · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.mpr ⟨t.mem_cells i, (hpq i).mpr hi⟩
  · simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc
    refine ⟨t ⟨c, hc.1⟩, ?_, Prod.ext (t.row_apply _) (t.column_apply _)⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact (hpq _).mp (by rw [t.row_apply, t.column_apply]; exact hc.2)

/-- The tabloid a semistandard tableau of shape `lam` and weight `mu` determines, read through
`t`: the label in a cell is sent to the row named by the entry there. -/
private def readTabloid (t : YoungTableau lam) (T : WeightedSemistandardTableau lam mu) :
    Tabloid mu where
  rowOf i := ⟨T.tableau (t.row i) (t.column i), T.entry_lt _ (t.mem_cells i)⟩
  row_nonempty i := by
    rw [← T.content ⟨T.tableau (t.row i) (t.column i), T.entry_lt _ (t.mem_cells i)⟩,
      Finset.card_pos]
    exact ⟨(t.row i, t.column i), Finset.mem_filter.mpr ⟨t.mem_cells i, rfl⟩⟩
  content row := by
    rcases lt_or_ge row n with hrow | hrow
    · exact (card_filter_cells t (fun r c => T.tableau r c = row)
        (fun i => T.tableau (t.row i) (t.column i) = row) fun _ => Iff.rfl).symm.trans
        (T.content ⟨row, hrow⟩)
    · rw [rowLen_eq_zero_of_le mu hrow, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun i _ => Nat.ne_of_lt (lt_of_lt_of_le (T.entry_lt _ (t.mem_cells i)) hrow)

private theorem semistandard_readTabloid (t : YoungTableau lam)
    (T : WeightedSemistandardTableau lam mu) : Semistandard t (readTabloid t T) :=
  semistandard_of_entry_eq t fun _ => rfl

/-- **Sagan's Proposition 2.9.2.**  Reading a tabloid of weight `mu` through a tableau `t` of
shape `lam` matches the semistandard tabloids with the semistandard tableaux of shape `lam` and
weight `mu`. -/
def semistandardTabloidEquiv (t : YoungTableau lam) :
    {S : Tabloid mu // Semistandard t S} ≃ WeightedSemistandardTableau lam mu where
  toFun S :=
    { tableau := readTableau t S.2
      entry_lt := fun cell hcell => by
        show readEntry t S.val cell.1 cell.2 < n
        rw [readEntry_of_mem t S.val hcell]
        exact (S.val.rowOf _).isLt
      content := fun value => by
        show (lam.val.cells.filter fun cell =>
          readEntry t S.val cell.1 cell.2 = (value : ℕ)).card = mu.val.rowLen (value : ℕ)
        exact (card_filter_cells t (fun r c => readEntry t S.val r c = (value : ℕ))
          (fun i => (S.val.rowOf i : ℕ) = (value : ℕ))
          fun i => by simp only [readEntry_row_column]; exact Iff.rfl).trans
          (S.val.content (value : ℕ)) }
  invFun T := ⟨readTabloid t T, semistandard_readTabloid t T⟩
  left_inv S := Subtype.ext (Tabloid.ext (funext fun i => Fin.ext (readEntry_row_column t S.val i)))
  right_inv T := by
    obtain ⟨T, hT, wT⟩ := T
    dsimp only
    congr 1
    exact SemistandardYoungTableau.ext (readEntry_eq t fun _ => rfl)

/-- The multiplicity of `S^lam` in `M^mu` is the Kostka number `K_(lam,mu)`.

This is Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.10.1: the semistandard homomorphisms are
a basis of `Hom(S^lam, M^mu)`, and reading them through a tableau of shape `lam` matches them with
the semistandard tableaux of shape `lam` and weight `mu`. -/
theorem finrank_hom_eq_kostkaNumber (lam mu : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtModule lam ⟶ youngPermutationModule mu) = kostkaNumber lam mu := by
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  exact (t.finrank_hom_eq_card_semistandard (Y := Tabloid mu)).trans
    (Nat.card_congr (semistandardTabloidEquiv t))

end YoungTableau

/-- Young's rule: the Young permutation module of weight `weight` contains
`S^shape` with multiplicity `K_(shape,weight)`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.11.2,
https://doi.org/10.1007/978-1-4757-6804-6_2.  The conventions are cross-checked
against Tomczak, *Representation Theory of Symmetric Groups* (2022 lecture
notes), Corollary 3.19,
https://math.berkeley.edu/~ltomczak/notes/Mich2022/RepSn_Notes.pdf: rows are
weakly increasing, columns are strictly increasing, and the first Kostka index
is the shape.  Tomczak uses positive entries, while
`WeightedSemistandardTableau` shifts them down by one. -/
theorem youngsRule {n : ℕ} (weight : YoungDiagramOfSize n) :
  Nonempty (youngPermutationModule weight ≅
    ⨁ fun shape : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (kostkaNumber shape weight) => spechtModule shape) := by
  obtain ⟨e⟩ := FDRep.exists_iso_biproduct_multiplicity spechtModule spechtModule_irreducible
    (fun shape shape' h => (spechtModule_iso_iff_eq shape shape').mp h)
    (fun T hT => @exists_iso_spechtModule n T hT) (youngPermutationModule weight)
  exact ⟨e ≪≫ biproduct.mapIso fun shape =>
    biproduct.reindex (finCongr (YoungTableau.finrank_hom_eq_kostkaNumber shape weight))
      fun _ => spechtModule shape⟩

/-- The balanced two-row weight associated to a `k`-subset of an `n`-element
set.  Complementary subset sizes give the same weight. -/
def twoRowWeight (n k : ℕ) (hk : k ≤ n) : YoungDiagramOfSize n :=
  twoRowPartition n (min k (n - k)) (by omega)

/-- The two-row shapes occurring in the `k`-subset representation. -/
def twoRowShape (n k : ℕ) (hk : k ≤ n)
    (i : Fin (min k (n - k) + 1)) : YoungDiagramOfSize n :=
  twoRowPartition n i (by
    have hi : i.val ≤ min k (n - k) := by omega
    omega)

namespace WeightedSemistandardTableau

variable {n r : ℕ} {h : 2 * r ≤ n} {shape : YoungDiagramOfSize n}

/-- With a two-row weight, every entry is `0` or `1`. -/
theorem entry_le_one (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {row column : ℕ} (hcell : (row, column) ∈ shape.val.cells) :
    T.tableau row column ≤ 1 := by
  by_contra hcontra
  have hgt : 1 < T.tableau row column := Nat.not_le.mp hcontra
  have hlt : T.tableau row column < n := T.entry_lt (row, column) hcell
  have hc := T.content ⟨T.tableau row column, hlt⟩
  rw [twoRowPartition_rowLen] at hc
  simp only [if_neg (by omega : T.tableau row column ≠ 0),
    if_neg (by omega : T.tableau row column ≠ 1)] at hc
  have hmem : (row, column) ∈ shape.val.cells.filter
      (fun cell => T.tableau cell.1 cell.2 = ((⟨T.tableau row column, hlt⟩ : Fin n) : ℕ)) :=
    Finset.mem_filter.mpr ⟨hcell, rfl⟩
  rw [Finset.card_eq_zero] at hc
  rw [hc] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- With a two-row weight the shape has at most two rows. -/
theorem rowLen_eq_zero_of_two_le
    (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {row : ℕ} (hrow : 2 ≤ row) : shape.val.rowLen row = 0 := by
  by_contra hne
  obtain ⟨column, hcolumn⟩ : ∃ column, (row, column) ∈ shape.val.cells :=
    ⟨0, YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)⟩
  have hsecond : (1, column) ∈ shape.val.cells :=
    shape.val.up_left_mem (by omega) le_rfl hcolumn
  have hlt01 : T.tableau 0 column < T.tableau 1 column :=
    T.tableau.col_strict (by omega) hsecond
  have hlt1r : T.tableau 1 column < T.tableau row column :=
    T.tableau.col_strict (by omega) hcolumn
  have := T.entry_le_one hcolumn
  omega

/-- A cell carrying a zero entry lies in the first row. -/
theorem row_eq_zero_of_entry_eq_zero
    (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {row column : ℕ} (hcell : (row, column) ∈ shape.val.cells)
    (hzero : T.tableau row column = 0) : row = 0 := by
  by_contra hne
  have := T.tableau.col_strict (Nat.pos_of_ne_zero hne) hcell
  omega

/-- A cell in the second row carries a one, and the cell above it carries a zero. -/
theorem entry_row_one
    (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {column : ℕ} (hcell : (1, column) ∈ shape.val.cells) :
    T.tableau 0 column = 0 ∧ T.tableau 1 column = 1 := by
  have hlt := T.tableau.col_strict (by omega : (0 : ℕ) < 1) hcell
  have hle := T.entry_le_one hcell
  omega

/-- With at most two rows, the two row lengths add up to the size. -/
theorem rowLen_zero_add_rowLen_one
    (T : WeightedSemistandardTableau shape (twoRowPartition n r h)) :
    shape.val.rowLen 0 + shape.val.rowLen 1 = n := by
  have hsplit : shape.val.cells.filter (fun c => c.1 ≠ 0) = shape.val.row 1 := by
    ext ⟨row, column⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]
    constructor
    · rintro ⟨hcell, hne⟩
      refine ⟨hcell, ?_⟩
      by_contra hrow
      have hzero := T.rowLen_eq_zero_of_two_le (row := row) (by omega)
      have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hcell
      omega
    · rintro ⟨hcell, rfl⟩
      exact ⟨hcell, by omega⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := shape.val.cells) (p := fun c => c.1 = 0)
  have hn : shape.val.cells.card = n := shape.property
  rw [hn] at hcard
  rw [YoungDiagram.rowLen_eq_card, YoungDiagram.rowLen_eq_card, ← hsplit]
  simpa [YoungDiagram.row] using hcard

/-- The cells carrying a zero entry. -/
def zeroCells (T : WeightedSemistandardTableau shape (twoRowPartition n r h)) :
    Finset (ℕ × ℕ) :=
  shape.val.cells.filter fun cell => T.tableau cell.1 cell.2 = 0

theorem mem_zeroCells (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {cell : ℕ × ℕ} :
    cell ∈ T.zeroCells ↔ cell ∈ shape.val.cells ∧ T.tableau cell.1 cell.2 = 0 :=
  Finset.mem_filter

theorem card_zeroCells (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    (hn : 0 < n) : T.zeroCells.card = n - r := by
  have hzeros := T.content ⟨0, hn⟩
  rw [twoRowPartition_rowLen] at hzeros
  simpa [zeroCells] using hzeros

/-- Zero entries occupy an initial segment of the first row. -/
theorem entry_eq_zero_iff (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {column : ℕ} (hcell : (0, column) ∈ shape.val.cells) :
    T.tableau 0 column = 0 ↔ column < n - r := by
  have hn : 0 < n := by
    have hsize : shape.val.cells.card = n := shape.property
    have hpos : 0 < shape.val.cells.card := Finset.card_pos.mpr ⟨(0, column), hcell⟩
    omega
  have hcard := T.card_zeroCells hn
  constructor
  · intro hzero
    have hsub : ({0} ×ˢ Finset.range (column + 1) : Finset (ℕ × ℕ)) ⊆ T.zeroCells := by
      rintro ⟨a, b⟩ hb
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hb
      obtain ⟨rfl, hb⟩ := hb
      refine T.mem_zeroCells.mpr ⟨shape.val.up_left_mem le_rfl (by omega) hcell, ?_⟩
      show T.tableau 0 b = 0
      have hle : T.tableau 0 b ≤ T.tableau 0 column :=
        T.tableau.row_weak_of_le (by omega : b ≤ column) hcell
      omega
    have := Finset.card_le_card hsub
    simp only [Finset.card_product, Finset.card_singleton, Finset.card_range,
      one_mul, hcard] at this
    omega
  · intro hlt
    by_contra hne
    have hone : T.tableau 0 column = 1 := by
      have := T.entry_le_one hcell
      omega
    have hsub : T.zeroCells ⊆ ({0} ×ˢ Finset.range column : Finset (ℕ × ℕ)) := by
      rintro ⟨a, b⟩ hb
      obtain ⟨hcellb, hzerob⟩ := T.mem_zeroCells.mp hb
      have ha : a = 0 := T.row_eq_zero_of_entry_eq_zero hcellb hzerob
      subst ha
      have hcellb' : (0, b) ∈ shape.val.cells := hcellb
      have hzerob' : T.tableau 0 b = 0 := hzerob
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, true_and]
      by_contra hge
      have hle : T.tableau 0 column ≤ T.tableau 0 b :=
        T.tableau.row_weak_of_le (by omega : column ≤ b) hcellb'
      omega
    have := Finset.card_le_card hsub
    simp only [Finset.card_product, Finset.card_singleton, Finset.card_range,
      one_mul, hcard] at this
    omega

/-- Every entry is determined by its cell. -/
theorem entry_eq (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    {row column : ℕ} (hcell : (row, column) ∈ shape.val.cells) :
    T.tableau row column = if row = 0 ∧ column < n - r then 0 else 1 := by
  rcases Nat.eq_zero_or_pos row with rfl | hrow
  · by_cases hlt : column < n - r
    · simpa [hlt] using (T.entry_eq_zero_iff hcell).mpr hlt
    · have hne : T.tableau 0 column ≠ 0 := fun hzero =>
        hlt ((T.entry_eq_zero_iff hcell).mp hzero)
      have := T.entry_le_one hcell
      simp only [hlt, and_false, if_false]
      omega
  · have hone : row = 1 := by
      by_contra hne
      have hzero := T.rowLen_eq_zero_of_two_le (row := row) (by omega)
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell
      omega
    subst hone
    simpa using (T.entry_row_one hcell).2

/-- The second row of the shape is no longer than the second row of the weight. -/
theorem rowLen_one_le (T : WeightedSemistandardTableau shape (twoRowPartition n r h)) :
    shape.val.rowLen 1 ≤ r := by
  have hsum := T.rowLen_zero_add_rowLen_one
  rcases Nat.eq_zero_or_pos n with hzero | hn
  · omega
  have hcard := T.card_zeroCells hn
  have hsub : T.zeroCells ⊆ shape.val.row 0 := by
    intro cell hc
    obtain ⟨hcell, hzero⟩ := T.mem_zeroCells.mp hc
    exact YoungDiagram.mem_row_iff.mpr
      ⟨hcell, T.row_eq_zero_of_entry_eq_zero hcell hzero⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, ← YoungDiagram.rowLen_eq_card] at hle
  omega

/-- The shape is the two-row partition determined by the length of its second row. -/
theorem shape_eq (T : WeightedSemistandardTableau shape (twoRowPartition n r h))
    (hle : 2 * shape.val.rowLen 1 ≤ n) :
    shape = twoRowPartition n (shape.val.rowLen 1) hle := by
  refine YoungDiagramOfSize.eq_twoRowPartition hle shape ?_ rfl
    fun row hrow => T.rowLen_eq_zero_of_two_le hrow
  have := T.rowLen_zero_add_rowLen_one
  omega

/-- Two weighted semistandard tableaux of two-row weight and the same shape agree. -/
theorem subsingleton (shape : YoungDiagramOfSize n) (r : ℕ) (h : 2 * r ≤ n) :
    Subsingleton (WeightedSemistandardTableau shape (twoRowPartition n r h)) := by
  refine ⟨fun T U => ?_⟩
  cases T with
  | mk Tt Tlt Tc =>
    cases U with
    | mk Ut Ult Uc =>
      congr 1
      apply SemistandardYoungTableau.ext
      intro row column
      by_cases hcell : (row, column) ∈ shape.val.cells
      · have hT := WeightedSemistandardTableau.entry_eq ⟨Tt, Tlt, Tc⟩ hcell
        have hU := WeightedSemistandardTableau.entry_eq ⟨Ut, Ult, Uc⟩ hcell
        exact hT.trans hU.symm
      · rw [Tt.zeros (by simpa using hcell), Ut.zeros (by simpa using hcell)]

end WeightedSemistandardTableau

/-- The entry function of the unique tableau of two-row shape and two-row weight. -/
private def twoRowEntry (n r : ℕ) (μ : YoungDiagram) (row column : ℕ) : ℕ :=
  if (row, column) ∈ μ.cells then (if row = 0 ∧ column < n - r then 0 else 1) else 0

private theorem twoRowEntry_le_one (n r : ℕ) (μ : YoungDiagram) (row column : ℕ) :
    twoRowEntry n r μ row column ≤ 1 := by
  simp only [twoRowEntry]
  split <;> [split; skip] <;> omega

/-- The unique semistandard tableau of shape `(n - i, i)` and weight `(n - r, r)`. -/
private def twoRowSemistandardTableau (n r i : ℕ) (hr : 2 * r ≤ n) (hi : i ≤ r)
    (hi2 : 2 * i ≤ n) : SemistandardYoungTableau (twoRowPartition n i hi2).val where
  entry := twoRowEntry n r (twoRowPartition n i hi2).val
  row_weak' := by
    intro row column1 column2 hcolumn hcell
    have hcell1 : (row, column1) ∈ (twoRowPartition n i hi2).val :=
      (twoRowPartition n i hi2).val.up_left_mem le_rfl (by omega) hcell
    simp only [twoRowEntry, YoungDiagram.mem_cells, if_pos hcell, if_pos hcell1]
    split <;> split <;> omega
  col_strict' := by
    intro row1 row2 column hrow hcell
    have hcell1 : (row1, column) ∈ (twoRowPartition n i hi2).val :=
      (twoRowPartition n i hi2).val.up_left_mem (by omega) le_rfl hcell
    have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    rw [twoRowPartition_rowLen] at hlt
    have hrow2 : row2 = 1 := by
      by_contra hne
      rw [if_neg (by omega : row2 ≠ 0), if_neg hne] at hlt
      omega
    have hrow1 : row1 = 0 := by omega
    subst hrow2
    subst hrow1
    have hcolumn : column < i := by simpa using hlt
    have hkey : column < n - r := by omega
    simp only [twoRowEntry, YoungDiagram.mem_cells, if_pos hcell, if_pos hcell1]
    simp [hkey]
  zeros' := by
    intro row column hcell
    simp only [twoRowEntry, YoungDiagram.mem_cells, if_neg hcell]

@[simp]
private theorem twoRowSemistandardTableau_apply (n r i : ℕ) (hr : 2 * r ≤ n) (hi : i ≤ r)
    (hi2 : 2 * i ≤ n) (row column : ℕ) :
    twoRowSemistandardTableau n r i hr hi hi2 row column =
      twoRowEntry n r (twoRowPartition n i hi2).val row column :=
  rfl

/-- The zero entries of the two-row tableau fill the first `n - r` cells of its first row. -/
private theorem twoRowSemistandardTableau_zeroCells (n r i : ℕ) (hr : 2 * r ≤ n) (hi : i ≤ r)
    (hi2 : 2 * i ≤ n) :
    ((twoRowPartition n i hi2).val.cells.filter fun cell =>
        twoRowSemistandardTableau n r i hr hi hi2 cell.1 cell.2 = 0) =
      ({0} ×ˢ Finset.range (n - r) : Finset (ℕ × ℕ)) := by
  ext ⟨row, column⟩
  simp only [Finset.mem_filter, twoRowSemistandardTableau_apply, twoRowEntry,
    Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
  constructor
  · rintro ⟨hcell, hzero⟩
    rw [if_pos hcell] at hzero
    by_cases hsplit : row = 0 ∧ column < n - r
    · exact hsplit
    · rw [if_neg hsplit] at hzero
      omega
  · rintro ⟨rfl, hcolumn⟩
    have hcell : ((0 : ℕ), column) ∈ (twoRowPartition n i hi2).val.cells := by
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, twoRowPartition_rowLen]
      simpa using by omega
    exact ⟨hcell, by rw [if_pos hcell, if_pos ⟨rfl, hcolumn⟩]⟩

/-- The unique weighted semistandard tableau of shape `(n - i, i)` and weight `(n - r, r)`. -/
private def twoRowWeightedTableau (n r i : ℕ) (hr : 2 * r ≤ n) (hi : i ≤ r) (hi2 : 2 * i ≤ n) :
    WeightedSemistandardTableau (twoRowPartition n i hi2) (twoRowPartition n r hr) where
  tableau := twoRowSemistandardTableau n r i hr hi hi2
  entry_lt := by
    rintro ⟨row, column⟩ hcell
    have hmem : (row, column) ∈ (twoRowPartition n i hi2).val.cells := hcell
    rw [twoRowPartition_cells] at hmem
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_range] at hmem
    simp only [twoRowSemistandardTableau_apply, twoRowEntry, if_pos hcell]
    rcases hmem with ⟨hrow, hcolumn⟩ | ⟨hrow, hcolumn⟩
    · by_cases hlt : column < n - r
      · rw [if_pos ⟨hrow, hlt⟩]
        omega
      · rw [if_neg fun hc => hlt hc.2]
        omega
    · rw [if_neg fun hc => by omega]
      omega
  content := by
    intro e
    rw [twoRowPartition_rowLen]
    have hsize : (twoRowPartition n i hi2).val.cells.card = n :=
      (twoRowPartition n i hi2).property
    by_cases he0 : (e : ℕ) = 0
    · rw [he0, if_pos rfl, ← he0]
      have hzero := twoRowSemistandardTableau_zeroCells n r i hr hi hi2
      rw [he0]
      rw [show ((twoRowPartition n i hi2).val.cells.filter fun cell =>
          twoRowSemistandardTableau n r i hr hi hi2 cell.1 cell.2 = 0) = _ from hzero]
      simp
    have hzeroCard : ((twoRowPartition n i hi2).val.cells.filter fun cell =>
        twoRowSemistandardTableau n r i hr hi hi2 cell.1 cell.2 = 0).card = n - r := by
      rw [twoRowSemistandardTableau_zeroCells]
      simp
    by_cases he1 : (e : ℕ) = 1
    · rw [he1, if_neg (by omega), if_pos rfl, ← he1]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (twoRowPartition n i hi2).val.cells)
        (p := fun cell => twoRowSemistandardTableau n r i hr hi hi2 cell.1 cell.2 = 0)
      rw [hzeroCard, hsize] at hsplit
      have hneg : ((twoRowPartition n i hi2).val.cells.filter fun cell =>
          ¬ (twoRowSemistandardTableau n r i hr hi hi2 cell.1 cell.2 = 0)) =
          ((twoRowPartition n i hi2).val.cells.filter fun cell =>
            twoRowSemistandardTableau n r i hr hi hi2 cell.1 cell.2 = (e : ℕ)) := by
        apply Finset.filter_congr
        intro cell _
        have := twoRowEntry_le_one n r (twoRowPartition n i hi2).val cell.1 cell.2
        simp only [twoRowSemistandardTableau_apply, he1]
        omega
      rw [hneg] at hsplit
      omega
    · rw [if_neg he0, if_neg he1]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro cell _
      have := twoRowEntry_le_one n r (twoRowPartition n i hi2).val cell.1 cell.2
      simp only [twoRowSemistandardTableau_apply]
      omega

private theorem nonempty_of_kostkaNumber_pos {n : ℕ} {shape weight : YoungDiagramOfSize n}
    (hpos : 0 < kostkaNumber shape weight) :
    Nonempty (WeightedSemistandardTableau shape weight) :=
  (Nat.card_pos_iff.mp hpos).1

private theorem kostkaNumber_pos_of_fin {n : ℕ} {shape weight : YoungDiagramOfSize n}
    (j : Fin (kostkaNumber shape weight)) : 0 < kostkaNumber shape weight :=
  Nat.pos_of_ne_zero fun hzero => Fin.elim0 (hzero ▸ j)

/-- A two-row shape occurs exactly once in a two-row weight. -/
theorem kostkaNumber_twoRow_eq_one (n r i : ℕ) (hr : 2 * r ≤ n) (hi : i ≤ r) (hi2 : 2 * i ≤ n) :
    kostkaNumber (twoRowPartition n i hi2) (twoRowPartition n r hr) = 1 := by
  haveI : Nonempty
      (WeightedSemistandardTableau (twoRowPartition n i hi2) (twoRowPartition n r hr)) :=
    ⟨twoRowWeightedTableau n r i hr hi hi2⟩
  haveI := WeightedSemistandardTableau.subsingleton (twoRowPartition n i hi2) r hr
  exact Nat.card_unique

/-- A shape occurring in a two-row weight occurs exactly once. -/
theorem kostkaNumber_twoRow_eq_one_of_pos (n r : ℕ) (hr : 2 * r ≤ n)
    (shape : YoungDiagramOfSize n)
    (hpos : 0 < kostkaNumber shape (twoRowPartition n r hr)) :
    kostkaNumber shape (twoRowPartition n r hr) = 1 := by
  haveI : Nonempty (WeightedSemistandardTableau shape (twoRowPartition n r hr)) :=
    nonempty_of_kostkaNumber_pos hpos
  haveI := WeightedSemistandardTableau.subsingleton shape r hr
  exact Nat.card_unique

/-- Every shape occurring in a two-row weight is the two-row shape given by its
second row. -/
theorem eq_twoRowPartition_of_kostkaNumber_pos (n r : ℕ) (hr : 2 * r ≤ n)
    (shape : YoungDiagramOfSize n)
    (hpos : 0 < kostkaNumber shape (twoRowPartition n r hr)) :
    shape.val.rowLen 1 ≤ r ∧ ∀ hle : 2 * shape.val.rowLen 1 ≤ n,
      shape = twoRowPartition n (shape.val.rowLen 1) hle := by
  obtain ⟨T⟩ := nonempty_of_kostkaNumber_pos hpos
  exact ⟨T.rowLen_one_le, fun hle => T.shape_eq hle⟩

/-- Two shapes occurring in a two-row weight agree once their second rows do. -/
theorem shape_eq_of_rowLen_one_eq (n r : ℕ) (hr : 2 * r ≤ n)
    {shape1 shape2 : YoungDiagramOfSize n}
    (hpos1 : 0 < kostkaNumber shape1 (twoRowPartition n r hr))
    (hpos2 : 0 < kostkaNumber shape2 (twoRowPartition n r hr))
    (heq : shape1.val.rowLen 1 = shape2.val.rowLen 1) : shape1 = shape2 := by
  obtain ⟨T1⟩ := nonempty_of_kostkaNumber_pos hpos1
  obtain ⟨T2⟩ := nonempty_of_kostkaNumber_pos hpos2
  apply Subtype.ext
  apply YoungDiagram.ext_of_rowLen
  intro row
  match row with
  | 0 =>
      have h1 := T1.rowLen_zero_add_rowLen_one
      have h2 := T2.rowLen_zero_add_rowLen_one
      omega
  | 1 => exact heq
  | (row + 2) =>
      rw [T1.rowLen_eq_zero_of_two_le (by omega), T2.rowLen_eq_zero_of_two_le (by omega)]

/-- The second-row length of the shape carried by a two-row Kostka copy. -/
private noncomputable def twoRowKostkaIndexMap (n k : ℕ) (hk : k ≤ n)
    (copy : Σ shape : YoungDiagramOfSize n,
      Fin (kostkaNumber shape (twoRowWeight n k hk))) :
    Fin (min k (n - k) + 1) :=
  ⟨copy.1.val.rowLen 1, by
    have hpos : 0 < kostkaNumber copy.1 (twoRowPartition n (min k (n - k)) (by omega)) :=
      kostkaNumber_pos_of_fin copy.2
    have hle := (eq_twoRowPartition_of_kostkaNumber_pos n (min k (n - k)) (by omega)
      copy.1 hpos).1
    omega⟩

private theorem twoRowKostkaIndexMap_bijective (n k : ℕ) (hk : k ≤ n) :
    Function.Bijective (twoRowKostkaIndexMap n k hk) := by
  have hr : 2 * min k (n - k) ≤ n := by omega
  constructor
  · rintro ⟨shape1, j1⟩ ⟨shape2, j2⟩ heq
    have hpos1 : 0 < kostkaNumber shape1 (twoRowPartition n (min k (n - k)) hr) :=
      kostkaNumber_pos_of_fin j1
    have hpos2 : 0 < kostkaNumber shape2 (twoRowPartition n (min k (n - k)) hr) :=
      kostkaNumber_pos_of_fin j2
    have hrow : shape1.val.rowLen 1 = shape2.val.rowLen 1 := congrArg Fin.val heq
    have hshape : shape1 = shape2 :=
      shape_eq_of_rowLen_one_eq n (min k (n - k)) hr hpos1 hpos2 hrow
    subst hshape
    have hone : kostkaNumber shape1 (twoRowWeight n k hk) = 1 :=
      kostkaNumber_twoRow_eq_one_of_pos n (min k (n - k)) hr shape1 hpos1
    have hj1 := j1.isLt
    have hj2 := j2.isLt
    exact congrArg _ (Fin.ext (by omega))
  · intro index
    have hi : (index : ℕ) ≤ min k (n - k) := Nat.lt_succ_iff.mp index.isLt
    have hi2 : 2 * (index : ℕ) ≤ n := le_trans (Nat.mul_le_mul_left 2 hi) hr
    have hone : kostkaNumber (twoRowPartition n (index : ℕ) hi2)
        (twoRowWeight n k hk) = 1 :=
      kostkaNumber_twoRow_eq_one n (min k (n - k)) (index : ℕ) hr hi hi2
    refine ⟨⟨twoRowPartition n (index : ℕ) hi2, ⟨0, by omega⟩⟩, ?_⟩
    apply Fin.ext
    show (twoRowPartition n (index : ℕ) hi2).val.rowLen 1 = (index : ℕ)
    rw [twoRowPartition_rowLen]
    simp

/-- For a two-row weight, the nonzero Kostka copies are indexed once by the
possible second-row lengths.

This is the two-letter specialization of Sagan, *The Symmetric Group*, 2nd ed.,
Definition 2.11.1 and Theorem 2.11.2,
https://doi.org/10.1007/978-1-4757-6804-6_2.  In a semistandard tableau of weight
`(n-r,r)`, strict columns force at most two rows; the bottom row is all `1`, and
the remaining top row is uniquely weakly increasing.  The same conventions are
independently stated in Tomczak, *Representation Theory of Symmetric Groups*
(2022 lecture notes), Corollary 3.19,
https://math.berkeley.edu/~ltomczak/notes/Mich2022/RepSn_Notes.pdf. -/
noncomputable def twoRowKostkaIndexEquiv (n k : ℕ) (hk : k ≤ n) :
  (Σ shape : YoungDiagramOfSize n,
    Fin (kostkaNumber shape (twoRowWeight n k hk))) ≃
      Fin (min k (n - k) + 1) :=
  Equiv.ofBijective _ (twoRowKostkaIndexMap_bijective n k hk)

/-- The Kostka copy selected by `twoRowKostkaIndexEquiv` has the corresponding
two-row shape.  This records the shape component of the sourced two-row Kostka
calculation above. -/
theorem twoRowKostkaIndexEquiv_shape (n k : ℕ) (hk : k ≤ n)
    (copy : Σ shape : YoungDiagramOfSize n,
      Fin (kostkaNumber shape (twoRowWeight n k hk))) :
    copy.1 = twoRowShape n k hk (twoRowKostkaIndexEquiv n k hk copy) := by
  have hr : 2 * min k (n - k) ≤ n := by omega
  have hpos : 0 < kostkaNumber copy.1 (twoRowPartition n (min k (n - k)) hr) :=
    kostkaNumber_pos_of_fin copy.2
  exact (eq_twoRowPartition_of_kostkaNumber_pos n (min k (n - k)) hr copy.1 hpos).2 _

/-- Young's rule for a two-row weight, regrouped into its multiplicity-free
form. -/
theorem youngPermutationModule_twoRow_decomposition (n k : ℕ) (hk : k ≤ n) :
    Nonempty (youngPermutationModule (twoRowWeight n k hk) ≅
      ⨁ fun i : Fin (min k (n - k) + 1) => spechtModule (twoRowShape n k hk i)) := by
  let youngIso := Classical.choice (youngsRule (twoRowWeight n k hk))
  let copies := Σ shape : YoungDiagramOfSize n,
    Fin (kostkaNumber shape (twoRowWeight n k hk))
  let indexEquiv : copies ≃ Fin (min k (n - k) + 1) :=
    twoRowKostkaIndexEquiv n k hk
  let flatten :
      (⨁ fun shape : YoungDiagramOfSize n =>
        ⨁ fun _ : Fin (kostkaNumber shape (twoRowWeight n k hk)) => spechtModule shape) ≅
      ⨁ fun copy : copies => spechtModule copy.1 :=
    biproductBiproductIso
      (fun shape => Fin (kostkaNumber shape (twoRowWeight n k hk)))
      (fun shape _ => spechtModule shape)
  let changeShape :
      (⨁ fun copy : copies => spechtModule copy.1) ≅
      ⨁ fun copy : copies => spechtModule (twoRowShape n k hk (indexEquiv copy)) :=
    biproduct.mapIso fun copy =>
      eqToIso (congrArg spechtModule (twoRowKostkaIndexEquiv_shape n k hk copy))
  exact ⟨youngIso ≪≫ flatten ≪≫ changeShape ≪≫
    biproduct.reindex indexEquiv
      (fun i => spechtModule (twoRowShape n k hk i))⟩
