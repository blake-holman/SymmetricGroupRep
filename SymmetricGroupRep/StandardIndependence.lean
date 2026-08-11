import SymmetricGroupRep.Classification
import SymmetricGroupRep.StandardTableaux
import Mathlib.Order.PiLex

/-! # Standard polytabloids are linearly independent

Order the tabloids of shape `μ` colexicographically by the row of each label,
comparing at the largest label where two tabloids differ. If `t` is standard and
`σ` is a nontrivial element of its column group, then at the largest label moved
by `σ` the tabloid `σ • {t}` has a strictly smaller row than `{t}`, because
standardness makes labels increase down each column. So `{t}` is the
colexicographic maximum of the tabloids occurring in the polytabloid `e_t`, and
it occurs with coefficient one. Picking the standard tableau whose tabloid is
largest in a vanishing linear combination therefore forces its coefficient to be
zero, which is Sagan, *The Symmetric Group*, 2nd ed., Lemma 2.5.4.

The consequence recorded here is the inequality half of the standard basis
theorem: the Specht module has at least as many dimensions as `μ` has standard
tableaux.
-/

namespace StandardYoungTableau

open YoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize n}

/-- Labels in a common column increase with the row. -/
theorem lt_of_column_eq_of_row_lt (T : StandardYoungTableau μ) {i j : Fin n}
    (hcol : column T.entry i = column T.entry j) (hrow : row T.entry i < row T.entry j) : i < j := by
  simpa using T.col_strict (c := T.entry.symm i) (d := T.entry.symm j) hcol hrow

/-- Labels in a common row increase with the column. -/
theorem lt_of_row_eq_of_column_lt (T : StandardYoungTableau μ) {i j : Fin n}
    (hrow : row T.entry i = row T.entry j) (hcol : column T.entry i < column T.entry j) : i < j := by
  simpa using T.row_strict (c := T.entry.symm i) (d := T.entry.symm j) hrow hcol

/-- Rows in a common column increase with the label. -/
theorem row_lt_row_of_column_eq (T : StandardYoungTableau μ) {i j : Fin n}
    (hcol : column T.entry i = column T.entry j) (hij : i < j) :
    row T.entry i < row T.entry j := by
  rcases lt_trichotomy (row T.entry i) (row T.entry j) with h | h | h
  · exact h
  · exact absurd (row_column_injective T.entry (Prod.ext h hcol)) hij.ne
  · exact absurd (T.lt_of_column_eq_of_row_lt hcol.symm h) (by omega)

/-- Columns in a common row increase with the label. -/
theorem column_lt_column_of_row_eq (T : StandardYoungTableau μ) {i j : Fin n}
    (hrow : row T.entry i = row T.entry j) (hij : i < j) :
    column T.entry i < column T.entry j := by
  rcases lt_trichotomy (column T.entry i) (column T.entry j) with h | h | h
  · exact h
  · exact absurd (row_column_injective T.entry (Prod.ext hrow h)) hij.ne
  · exact absurd (T.lt_of_row_eq_of_column_lt hrow.symm h) (by omega)

/-- A standard tableau is determined by its tabloid: the column of a label counts the smaller
labels in its row. -/
theorem column_eq_card_filter (T : StandardYoungTableau μ) (i : Fin n) :
    column T.entry i =
      (Finset.univ.filter fun j => j < i ∧ row T.entry j = row T.entry i).card := by
  have hcards := card_filter_column_lt_and_row_eq T.entry (row T.entry i) (column T.entry i)
  rw [min_eq_right (column_lt_rowLen T.entry i).le] at hcards
  rw [← hcards]
  refine congrArg Finset.card (Finset.filter_congr fun j _ => ?_)
  constructor
  · rintro ⟨hcol, hrow⟩
    exact ⟨T.lt_of_row_eq_of_column_lt hrow hcol, hrow⟩
  · rintro ⟨hlt, hrow⟩
    exact ⟨T.column_lt_column_of_row_eq hrow hlt, hrow⟩

/-- Standard tableaux with the same tabloid are equal. -/
theorem eq_of_tabloid_eq {T U : StandardYoungTableau μ}
    (h : tabloid T.entry = tabloid U.entry) : T = U := by
  have hrow : ∀ i, row T.entry i = row U.entry i := fun i =>
    congrArg Fin.val (congrFun (congrArg Tabloid.rowOf h) i)
  refine StandardYoungTableau.ext (Equiv.symm_bijective.injective (Equiv.ext fun i => ?_))
  refine Subtype.ext (Prod.ext (hrow i) ?_)
  rw [show (T.entry.symm i).1.2 = column T.entry i from rfl,
    show (U.entry.symm i).1.2 = column U.entry i from rfl,
    T.column_eq_card_filter i, U.column_eq_card_filter i]
  exact congrArg Finset.card (Finset.filter_congr fun j _ => by rw [hrow j, hrow i])

end StandardYoungTableau

open YoungTableau

/-- A nontrivial column permutation lowers the row of the largest label it moves, so it strictly
decreases the tabloid in the colexicographic order on rows. -/
theorem toColex_smul_tabloid_lt {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) {sigma : SymmetricGroup n}
    (hmem : sigma ∈ columnGroup T.entry) (hne : sigma ≠ 1) :
    toColex (sigma • tabloid T.entry).rowOf < toColex (tabloid T.entry).rowOf := by
  have hnonempty : (Finset.univ.filter fun i : Fin n => sigma⁻¹ i ≠ i).Nonempty := by
    by_contra hc
    refine hne (inv_eq_one.mp (Equiv.ext fun i => ?_))
    by_contra hi
    exact hc ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image _ (fun i : Fin n => i) hnonempty
  have hk : sigma⁻¹ k ≠ k := (Finset.mem_filter.mp hkmem).2
  have hklt : sigma⁻¹ k < k := by
    refine lt_of_le_of_ne (hkmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hfix => ?_⟩)) hk
    exact hk (by simpa using congrArg (sigma ·) hfix)
  have hfixed : ∀ j, k < j → sigma⁻¹ j = j := by
    intro j hj
    by_contra hcon
    exact absurd (hkmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)) (by omega)
  refine ⟨k, fun j hj => ?_, ?_⟩
  · show (sigma • tabloid T.entry).rowOf j = (tabloid T.entry).rowOf j
    rw [Tabloid.smul_rowOf, hfixed j hj]
  · show (sigma • tabloid T.entry).rowOf k < (tabloid T.entry).rowOf k
    rw [Tabloid.smul_rowOf]
    exact T.row_lt_row_of_column_eq ((columnGroup T.entry).inv_mem hmem k) hklt

/-- Every tabloid occurring in a polytabloid is a column permutation of the tabloid itself. -/
theorem exists_mem_columnGroup_of_apply_ne_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    (t : YoungTableau μ) {S : Tabloid μ} (h : polytabloid t S ≠ 0) :
    ∃ sigma ∈ columnGroup t, sigma • tabloid t = S := by
  by_contra hc
  refine h ?_
  rw [polytabloid, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun sigma _ => ?_
  have hne : (sigma : SymmetricGroup n) • tabloid t ≠ S := fun heq => hc ⟨sigma, sigma.2, heq⟩
  simp [hne]

/-- The standard polytabloids of a fixed shape are linearly independent. -/
theorem linearIndependent_polytabloid {n : ℕ} (μ : YoungDiagramOfSize n) :
    LinearIndependent ℂ fun T : StandardYoungTableau μ => polytabloid T.entry := by
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  obtain ⟨T', hT's, hT'ne⟩ : ∃ T ∈ s, g T ≠ 0 := by
    by_contra hc
    exact hcon fun T hT => by
      by_contra hg
      exact hc ⟨T, hT, hg⟩
  obtain ⟨T₀, hT₀, hmax⟩ := Finset.exists_max_image (s.filter fun T => g T ≠ 0)
    (fun T => toColex (tabloid T.entry).rowOf) ⟨T', Finset.mem_filter.mpr ⟨hT's, hT'ne⟩⟩
  have hT₀s : T₀ ∈ s := (Finset.mem_filter.mp hT₀).1
  have hT₀ne : g T₀ ≠ 0 := (Finset.mem_filter.mp hT₀).2
  have hvanish : ∀ T ∈ s, T ≠ T₀ →
      (g T • polytabloid T.entry) (tabloid T₀.entry) = 0 := by
    intro T hTs hTne
    by_cases hg : g T = 0
    · simp [hg]
    have hzero : polytabloid T.entry (tabloid T₀.entry) = 0 := by
      by_contra hnz
      obtain ⟨sigma, hsigma, hsmul⟩ := exists_mem_columnGroup_of_apply_ne_zero T.entry hnz
      rcases eq_or_ne sigma 1 with rfl | hsne
      · rw [one_smul] at hsmul
        exact hTne (StandardYoungTableau.eq_of_tabloid_eq hsmul)
      · refine absurd (hmax T (Finset.mem_filter.mpr ⟨hTs, hg⟩)) (not_le.mpr ?_)
        rw [← hsmul]
        exact toColex_smul_tabloid_lt T hsigma hsne
    simp [hzero]
  have heval := congrArg (fun x : Tabloid μ →₀ ℂ => x (tabloid T₀.entry)) hsum
  simp only [Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at heval
  rw [Finset.sum_eq_single_of_mem T₀ hT₀s hvanish] at heval
  simp only [Finsupp.smul_apply, polytabloid_apply_tabloid, smul_eq_mul, mul_one] at heval
  exact hT₀ne heval

/-- The standard polytabloids, viewed inside the Specht module. -/
noncomputable def spechtStandardFamily {n : ℕ} (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ) : (spechtModule μ : Type) :=
  ⟨polytabloid T.entry, Submodule.subset_span ⟨T.entry, rfl⟩⟩

theorem linearIndependent_spechtStandardFamily {n : ℕ} (μ : YoungDiagramOfSize n) :
    LinearIndependent ℂ (spechtStandardFamily μ) :=
  LinearIndependent.of_comp (spechtSubrepresentation μ).toSubmodule.subtype
    (linearIndependent_polytabloid μ)

/-- The Specht module has at least as many dimensions as its shape has standard tableaux. -/
theorem card_standardYoungTableau_le_finrank {n : ℕ} (μ : YoungDiagramOfSize n) :
    Nat.card (StandardYoungTableau μ) ≤ Module.finrank ℂ (spechtModule μ) := by
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (linearIndependent_spechtStandardFamily μ).fintype_card_le_finrank
