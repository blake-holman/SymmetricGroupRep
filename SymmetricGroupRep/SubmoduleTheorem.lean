import SymmetricGroupRep.Polytabloid
import Mathlib.Data.Complex.BigOperators
import Mathlib.RepresentationTheory.Irreducible

/-! # James's submodule theorem, and irreducibility of the Specht module

This is Sagan, *The Symmetric Group*, 2nd ed., Section 2.4, over `ℂ`. The Young permutation module
carries a form for which the tabloids are orthonormal, and every subrepresentation of it is
comparable with the Specht module in a strong sense: either it contains the Specht module, or it is
orthogonal to it (Theorem 2.4.4). Over `ℂ` the form is taken Hermitian, so it is positive definite
and the two alternatives meet only in zero; the Specht module is therefore a minimal
subrepresentation, hence irreducible (Theorem 2.4.6).

The engine is the behaviour of the column antisymmetriser `κ_t` on a single tabloid `U`
(Corollary 2.4.3): either two labels share a row of `U` and a column of `t`, and then their
transposition is an odd element of the column group fixing `U`, so `κ_t U` is its own negative and
vanishes; or no two do, and then `U` is a column permutation of the tabloid of `t`, which `κ_t`
absorbs through its sign, leaving a multiple of the polytabloid `e_t`. The second case rests on a
counting lemma: the labels in the first `k` columns of `t` number `∑ i, min (μ.rowLen i) k`, while
row `i` of `U` can hold at most `min (μ.rowLen i) k` of them, so those bounds are all equalities.
-/

namespace YoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize n}

theorem mem_cells (t : YoungTableau μ) (i : Fin n) : (t.row i, t.column i) ∈ μ.val := by
  simp [row, column]

theorem column_lt_rowLen (t : YoungTableau μ) (i : Fin n) :
    t.column i < μ.val.rowLen (t.row i) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (t.mem_cells i)

theorem row_lt (t : YoungTableau μ) (i : Fin n) : t.row i < n :=
  Tabloid.cell_fst_lt (t.symm i)

theorem row_column_injective (t : YoungTableau μ) :
    Function.Injective fun i => (t.row i, t.column i) := by
  intro i j h
  rw [Prod.mk.injEq] at h
  exact t.symm.injective (Subtype.ext (Prod.ext h.1 h.2))

@[simp]
theorem row_apply (t : YoungTableau μ) (c : ↥μ.val.cells) : t.row (t c) = c.1.1 := by
  rw [row, Equiv.symm_apply_apply]

@[simp]
theorem column_apply (t : YoungTableau μ) (c : ↥μ.val.cells) : t.column (t c) = c.1.2 := by
  rw [column, Equiv.symm_apply_apply]

/-- Row `i` of a tableau meets its first `k` columns in `min (μ.rowLen i) k` labels. -/
theorem card_filter_column_lt_and_row_eq (t : YoungTableau μ) (i k : ℕ) :
    (Finset.univ.filter fun y => t.column y < k ∧ t.row y = i).card = min (μ.val.rowLen i) k := by
  classical
  have hinj : Set.InjOn t.column
      ↑(Finset.univ.filter fun y => t.column y < k ∧ t.row y = i) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    exact t.row_column_injective (Prod.ext (ha.2.trans hb.2.symm) hab)
  have himage : (Finset.univ.filter fun y => t.column y < k ∧ t.row y = i).image t.column =
      Finset.range (min (μ.val.rowLen i) k) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      lt_min_iff]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy2 ▸ t.column_lt_rowLen y, hy1⟩
    · rintro ⟨hj1, hj2⟩
      have hcell : ((i, j) : ℕ × ℕ) ∈ μ.val.cells := YoungDiagram.mem_iff_lt_rowLen.mpr hj1
      exact ⟨t ⟨(i, j), hcell⟩, ⟨by simpa using hj2, by simp⟩, by simp⟩
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_range]

/-- Row `i` of a tabloid meets the first `k` columns of a tableau in at most
`min (μ.rowLen i) k` labels, when a label is determined by its tabloid row together with its
tableau column. -/
private theorem card_filter_column_lt_and_rowOf_eq_le (t : YoungTableau μ) (U : Tabloid μ)
    (hinj : Function.Injective fun y => ((U.rowOf y : ℕ), t.column y)) (i k : ℕ) :
    (Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i).card ≤
      min (μ.val.rowLen i) k := by
  classical
  refine le_min ?_ ?_
  · rw [← U.content i]
    refine Finset.card_le_card fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  · have hinjOn : Set.InjOn t.column
        ↑(Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
      exact hinj (Prod.ext (ha.2.trans hb.2.symm) hab)
    calc (Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i).card
        = ((Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i).image
            t.column).card := (Finset.card_image_of_injOn hinjOn).symm
      _ ≤ (Finset.range k).card := by
          refine Finset.card_le_card fun j hj => ?_
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hj
          exact Finset.mem_range.mpr hy
      _ = k := Finset.card_range k

/-- Summed over the rows, the labels lying in the first `k` columns of a tableau number
`∑ i, min (μ.rowLen i) k`, however they are distributed among the rows of a tabloid. -/
private theorem sum_card_filter_column_lt (t : YoungTableau μ) (U : Tabloid μ) (k : ℕ) :
    ∑ i ∈ Finset.range n,
        (Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i).card =
      ∑ i ∈ Finset.range n, min (μ.val.rowLen i) k := by
  classical
  have hfiber : ∀ f : Fin n → ℕ, (∀ y, f y ∈ Finset.range n) →
      (Finset.univ.filter fun y => t.column y < k).card =
        ∑ i ∈ Finset.range n,
          (Finset.univ.filter fun y => t.column y < k ∧ f y = i).card := by
    intro f hf
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range n) fun y _ => hf y]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
  rw [← hfiber (fun y => (U.rowOf y : ℕ)) fun y => Finset.mem_range.mpr (U.rowOf y).2,
    hfiber t.row fun y => Finset.mem_range.mpr (t.row_lt y)]
  exact Finset.sum_congr rfl fun i _ => card_filter_column_lt_and_row_eq t i k

/-- **The counting lemma.** If a label is determined by its row in the tabloid `U` together with
its column in the tableau `t`, then those two indices are again the coordinates of a cell.

The labels in the first `k` columns of `t` number `∑ i, min (μ.rowLen i) k`, while row `i` of `U`
contributes at most `min (μ.rowLen i) k` of them; upper bounds that add up to the total are
equalities, and the case `k = μ.rowLen i` is the statement.

Adapted from `TauCetiProject/TauCeti` (Apache-2.0),
`RepresentationTheory/Symmetric/Vanishing.lean` and `Combinatorics/Young/Tableau.lean`. -/
theorem column_lt_rowLen_of_injective (t : YoungTableau μ) (U : Tabloid μ)
    (hinj : Function.Injective fun y => ((U.rowOf y : ℕ), t.column y)) (x : Fin n) :
    t.column x < μ.val.rowLen (U.rowOf x) := by
  classical
  set i : ℕ := (U.rowOf x : ℕ) with hi
  set k : ℕ := μ.val.rowLen i with hk
  have hrow := (Finset.sum_eq_sum_iff_of_le
      (fun j _ => card_filter_column_lt_and_rowOf_eq_le t U hinj j k)).mp
    (sum_card_filter_column_lt t U k) i (Finset.mem_range.mpr (U.rowOf x).2)
  rw [← hk, min_self] at hrow
  have hsub : (Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i) ⊆
      Finset.univ.filter fun y => (U.rowOf y : ℕ) = i := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  have hcard : (Finset.univ.filter fun y => (U.rowOf y : ℕ) = i).card ≤
      (Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i).card := by
    rw [hrow, U.content i]
  have hmem : x ∈ Finset.univ.filter fun y => t.column y < k ∧ (U.rowOf y : ℕ) = i := by
    rw [Finset.eq_of_subset_of_card_le hsub hcard]
    simp [hi]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem.1

/-- Any two tableaux of the same shape differ by a relabelling. -/
theorem exists_smul_eq (t s : YoungTableau μ) : ∃ sigma : SymmetricGroup n, sigma • t = s :=
  ⟨t.symm.trans s, Equiv.ext fun c => congrArg s (t.symm_apply_apply c)⟩

/-- When a label is determined by its row in `U` together with its column in `t`, the tabloid `U`
is a column-permutation of the tabloid of `t`. -/
theorem exists_mem_columnGroup_smul_tabloid_eq (t : YoungTableau μ) (U : Tabloid μ)
    (hinj : Function.Injective fun i => ((U.rowOf i : ℕ), t.column i)) :
    ∃ pi ∈ t.columnGroup, pi • t.tabloid = U := by
  have hcell : ∀ i : Fin n, ((U.rowOf i : ℕ), t.column i) ∈ μ.val.cells := fun i =>
    YoungDiagram.mem_iff_lt_rowLen.mpr (t.column_lt_rowLen_of_injective U hinj i)
  set g : Fin n → Fin n := fun i => t ⟨((U.rowOf i : ℕ), t.column i), hcell i⟩ with hg
  have hrow : ∀ i, t.row (g i) = (U.rowOf i : ℕ) := fun i => by rw [hg]; simp
  have hcolumn : ∀ i, t.column (g i) = t.column i := fun i => by rw [hg]; simp
  have hinjective : Function.Injective g := fun a b hab =>
    hinj (Prod.ext ((hrow a).symm.trans (by rw [hab, hrow]))
      ((hcolumn a).symm.trans (by rw [hab, hcolumn])))
  set tau : SymmetricGroup n :=
    Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinjective) with htau
  have happly : ∀ i, tau i = g i := fun i => rfl
  refine ⟨tau⁻¹, t.columnGroup.inv_mem fun i => by rw [happly, hcolumn], ?_⟩
  apply Tabloid.ext
  funext i
  apply Fin.ext
  rw [Tabloid.smul_rowOf, inv_inv, t.tabloid_rowOf, happly, hrow]

/-- When two labels share a row of `U` and a column of `t`, their transposition is an odd element
of the column group of `t` fixing `U`.

The tabloid `U` is allowed a shape of its own, since the argument reads only its rows; the
distinctness proof needs that generality. -/
theorem exists_mem_columnGroup_sign_eq_neg_one {ν : YoungDiagramOfSize n}
    (t : YoungTableau μ) (U : Tabloid ν)
    (hinj : ¬ Function.Injective fun i => ((U.rowOf i : ℕ), t.column i)) :
    ∃ sigma ∈ t.columnGroup, Equiv.Perm.sign sigma = -1 ∧ sigma • U = U := by
  rw [Function.not_injective_iff] at hinj
  obtain ⟨a, b, hab, hne⟩ := hinj
  rw [Prod.mk.injEq] at hab
  have hrow : U.rowOf a = U.rowOf b := Fin.ext hab.1
  refine ⟨Equiv.swap a b, fun i => ?_, Equiv.Perm.sign_swap hne, ?_⟩
  · rcases eq_or_ne i a with rfl | hia
    · rw [Equiv.swap_apply_left, hab.2]
    · rcases eq_or_ne i b with rfl | hib
      · rw [Equiv.swap_apply_right, hab.2]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  · apply Tabloid.ext
    funext i
    rw [Tabloid.smul_rowOf, Equiv.swap_inv]
    rcases eq_or_ne i a with rfl | hia
    · rw [Equiv.swap_apply_left, hrow]
    · rcases eq_or_ne i b with rfl | hib
      · rw [Equiv.swap_apply_right, hrow]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

/-- The column antisymmetriser of a tableau, acting on the Young permutation module.

See Sagan, *The Symmetric Group*, 2nd ed., Section 2.4: the polytabloid `e_t` is the value of the
column antisymmetriser on the tabloid of `t`. -/
noncomputable def columnAntisymmetriser (t : YoungTableau μ) :
    (Tabloid μ →₀ ℂ) →ₗ[ℂ] (Tabloid μ →₀ ℂ) :=
  ∑ sigma : t.columnGroup, ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
    Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) (sigma : SymmetricGroup n)

theorem columnAntisymmetriser_apply (t : YoungTableau μ) (v : Tabloid μ →₀ ℂ) :
    columnAntisymmetriser t v = ∑ sigma : t.columnGroup,
      ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
        Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)
          (sigma : SymmetricGroup n) v := by
  rw [columnAntisymmetriser, LinearMap.sum_apply]
  rfl

@[simp]
theorem columnAntisymmetriser_tabloid (t : YoungTableau μ) :
    columnAntisymmetriser t (Finsupp.single t.tabloid 1) = polytabloid t := by
  rw [columnAntisymmetriser_apply, polytabloid]
  exact Finset.sum_congr rfl fun sigma _ => by rw [Representation.ofMulAction_single]

/-- The column antisymmetriser absorbs a column permutation through its sign. -/
theorem columnAntisymmetriser_ofMulAction (t : YoungTableau μ) {g : SymmetricGroup n}
    (hg : g ∈ t.columnGroup) (v : Tabloid μ →₀ ℂ) :
    columnAntisymmetriser t
        (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g v) =
      ((Equiv.Perm.sign g : ℤ) : ℂ) • columnAntisymmetriser t v := by
  rw [columnAntisymmetriser_apply, columnAntisymmetriser_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : t.columnGroup)) _ _ fun sigma => ?_
  have hcoe : ((Equiv.mulRight (⟨g, hg⟩ : t.columnGroup) sigma : t.columnGroup) :
      SymmetricGroup n) = (sigma : SymmetricGroup n) * g := rfl
  rw [hcoe, map_mul (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)),
    Module.End.mul_apply, smul_smul, map_mul Equiv.Perm.sign, Units.val_mul, Int.cast_mul,
    ← mul_assoc]
  congr 1
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hone | hone <;> rw [hone] <;> push_cast <;>
    ring

/-- **Sagan's Corollary 2.4.3.** The column antisymmetriser sends a tabloid into the line spanned
by the polytabloid.

Adapted from `TauCetiProject/TauCeti` (Apache-2.0),
`RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean`. -/
theorem columnAntisymmetriser_single_mem_span (t : YoungTableau μ) (U : Tabloid μ) :
    columnAntisymmetriser t (Finsupp.single U 1) ∈ Submodule.span ℂ {polytabloid t} := by
  by_cases hinj : Function.Injective fun i => ((U.rowOf i : ℕ), t.column i)
  · obtain ⟨pi, hpi, rfl⟩ := t.exists_mem_columnGroup_smul_tabloid_eq U hinj
    rw [← Representation.ofMulAction_single, columnAntisymmetriser_ofMulAction t hpi,
      columnAntisymmetriser_tabloid]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · obtain ⟨sigma, hsigma, hsign, hfix⟩ := t.exists_mem_columnGroup_sign_eq_neg_one U hinj
    have hself : columnAntisymmetriser t (Finsupp.single U 1) =
        -columnAntisymmetriser t (Finsupp.single U 1) := by
      conv_lhs => rw [← hfix, ← Representation.ofMulAction_single,
        columnAntisymmetriser_ofMulAction t hsigma, hsign]
      simp
    have hzero : columnAntisymmetriser t (Finsupp.single U 1) = 0 := by
      have htwo : (2 : ℂ) • columnAntisymmetriser t (Finsupp.single U 1) = 0 := by
        rw [two_smul, ← eq_neg_iff_add_eq_zero]
        exact hself
      exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
    rw [hzero]
    exact Submodule.zero_mem _

/-- The column antisymmetriser collapses the whole Young permutation module onto the line spanned
by the polytabloid. -/
theorem columnAntisymmetriser_mem_span (t : YoungTableau μ) (v : Tabloid μ →₀ ℂ) :
    columnAntisymmetriser t v ∈ Submodule.span ℂ {polytabloid t} := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single U c =>
      rw [← Finsupp.smul_single_one, map_smul]
      exact Submodule.smul_mem _ _ (columnAntisymmetriser_single_mem_span t U)

end YoungTableau

section TabloidForm

variable {n : ℕ} {μ : YoungDiagramOfSize n}

noncomputable local instance : Fintype (Tabloid μ) := Fintype.ofFinite _

/-- The tabloid form on the Young permutation module: the Hermitian form for which the tabloids
are orthonormal.

See Sagan, *The Symmetric Group*, 2nd ed., Section 2.4, where it is taken over `ℚ`; over `ℂ` the
second argument is conjugated, which is what keeps the form positive definite. -/
noncomputable def tabloidForm (x y : Tabloid μ →₀ ℂ) : ℂ :=
  ∑ T : Tabloid μ, x T * (starRingEnd ℂ) (y T)

@[simp]
theorem tabloidForm_zero_left (y : Tabloid μ →₀ ℂ) : tabloidForm 0 y = 0 := by
  simp [tabloidForm]

@[simp]
theorem tabloidForm_zero_right (x : Tabloid μ →₀ ℂ) : tabloidForm x 0 = 0 := by
  simp [tabloidForm]

theorem tabloidForm_add_right (x y z : Tabloid μ →₀ ℂ) :
    tabloidForm x (y + z) = tabloidForm x y + tabloidForm x z := by
  simp [tabloidForm, mul_add, Finset.sum_add_distrib]

theorem tabloidForm_single_left (T : Tabloid μ) (y : Tabloid μ →₀ ℂ) :
    tabloidForm (Finsupp.single T 1) y = (starRingEnd ℂ) (y T) := by
  rw [tabloidForm, Finset.sum_eq_single T]
  · simp
  · intro U _ hne
    rw [Finsupp.single_eq_of_ne hne, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ T) hmem

theorem tabloidForm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Tabloid μ →₀ ℂ)
    (y : Tabloid μ →₀ ℂ) :
    tabloidForm (∑ i ∈ s, f i) y = ∑ i ∈ s, tabloidForm (f i) y := by
  simp only [tabloidForm, Finsupp.finset_sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem tabloidForm_sum_right {ι : Type*} (x : Tabloid μ →₀ ℂ) (s : Finset ι)
    (f : ι → Tabloid μ →₀ ℂ) :
    tabloidForm x (∑ i ∈ s, f i) = ∑ i ∈ s, tabloidForm x (f i) := by
  simp only [tabloidForm, Finsupp.finset_sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem tabloidForm_smul_left (c : ℂ) (x y : Tabloid μ →₀ ℂ) :
    tabloidForm (c • x) y = c * tabloidForm x y := by
  simp [tabloidForm, Finset.mul_sum, mul_assoc]

theorem tabloidForm_smul_right (c : ℂ) (x y : Tabloid μ →₀ ℂ) :
    tabloidForm x (c • y) = (starRingEnd ℂ) c * tabloidForm x y := by
  simp [tabloidForm, Finset.mul_sum, mul_left_comm]

/-- The symmetric group acts on the Young permutation module by isometries of the tabloid form. -/
theorem tabloidForm_ofMulAction (g : SymmetricGroup n) (x y : Tabloid μ →₀ ℂ) :
    tabloidForm (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g x)
        (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g y) = tabloidForm x y := by
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun T => ?_).symm
  rw [Representation.ofMulAction_apply, Representation.ofMulAction_apply]
  simp

/-- A permutation moves across the tabloid form by inverting. -/
theorem tabloidForm_ofMulAction_left (g : SymmetricGroup n) (x y : Tabloid μ →₀ ℂ) :
    tabloidForm (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g x) y =
      tabloidForm x (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g⁻¹ y) := by
  rw [← tabloidForm_ofMulAction g x
    (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) g⁻¹ y)]
  congr 1
  refine Finsupp.ext fun T => ?_
  rw [Representation.ofMulAction_apply, Representation.ofMulAction_apply]
  simp

/-- The form is positive definite, so only the zero vector is self-orthogonal. -/
theorem eq_zero_of_tabloidForm_self_eq_zero {x : Tabloid μ →₀ ℂ} (h : tabloidForm x x = 0) :
    x = 0 := by
  have hcast : ((∑ T : Tabloid μ, Complex.normSq (x T) : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_sum, ← h, tabloidForm]
    exact Finset.sum_congr rfl fun T _ => (Complex.mul_conj (x T)).symm
  have hsum : ∑ T : Tabloid μ, Complex.normSq (x T) = 0 := by exact_mod_cast hcast
  refine Finsupp.ext fun T => Complex.normSq_eq_zero.mp ?_
  exact (Finset.sum_eq_zero_iff_of_nonneg fun U _ => Complex.normSq_nonneg (x U)).mp hsum T
    (Finset.mem_univ T)

/-- **The column antisymmetriser is self-adjoint for the tabloid form.** Permutations act by
isometries, so moving one across the form inverts it, and inversion is a sign-preserving
involution of the column group. -/
theorem tabloidForm_columnAntisymmetriser (t : YoungTableau μ) (v w : Tabloid μ →₀ ℂ) :
    tabloidForm (YoungTableau.columnAntisymmetriser t v) w =
      tabloidForm v (YoungTableau.columnAntisymmetriser t w) := by
  rw [YoungTableau.columnAntisymmetriser_apply, YoungTableau.columnAntisymmetriser_apply,
    tabloidForm_sum_left, tabloidForm_sum_right]
  refine Fintype.sum_equiv (Equiv.inv t.columnGroup) _ _ fun sigma => ?_
  rw [tabloidForm_smul_left, tabloidForm_smul_right,
    tabloidForm_ofMulAction_left (sigma : SymmetricGroup n)]
  simp

end TabloidForm

/-- **James's submodule theorem.** A subrepresentation `U` of the Young permutation module either
contains the Specht module or is orthogonal to it for the tabloid form.

The dichotomy is whether some column antisymmetriser fails to annihilate some vector of `U`. If it
does fail, the value is a nonzero multiple of a polytabloid and lies in `U`, so `U` contains the
whole orbit of that polytabloid, which spans the Specht module. If every column antisymmetriser
annihilates every vector of `U`, then self-adjointness moves it off each polytabloid
`e_t = κ_t {t}` and onto the vector of `U`, where it vanishes.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.4. Adapted from
`TauCetiProject/TauCeti` (Apache-2.0),
`RepresentationTheory/Symmetric/Specht/SubmoduleTheorem.lean`. -/
theorem spechtSubrepresentation_le_or_forall_tabloidForm_eq_zero {n : ℕ}
    (μ : YoungDiagramOfSize n)
    (U : Subrepresentation (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ))) :
    (spechtSubrepresentation μ).toSubmodule ≤ U.toSubmodule ∨
      ∀ v ∈ U.toSubmodule, ∀ w ∈ (spechtSubrepresentation μ).toSubmodule,
        tabloidForm v w = 0 := by
  by_cases hex : ∃ (t : YoungTableau μ) (v : Tabloid μ →₀ ℂ), v ∈ U.toSubmodule ∧
      YoungTableau.columnAntisymmetriser t v ≠ 0
  · obtain ⟨t, v, hv, hne⟩ := hex
    obtain ⟨c, hc⟩ :=
      Submodule.mem_span_singleton.mp (YoungTableau.columnAntisymmetriser_mem_span t v)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hc, zero_smul])
    have hmem : YoungTableau.columnAntisymmetriser t v ∈ U.toSubmodule := by
      rw [YoungTableau.columnAntisymmetriser_apply]
      exact Submodule.sum_mem _ fun sigma _ =>
        Submodule.smul_mem _ _ (U.apply_mem_toSubmodule _ hv)
    have hpolytabloid : YoungTableau.polytabloid t ∈ U.toSubmodule := by
      have hsmul := U.toSubmodule.smul_mem c⁻¹ hmem
      rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hsmul
    refine Or.inl (Submodule.span_le.mpr ?_)
    rintro _ ⟨s, rfl⟩
    obtain ⟨sigma, rfl⟩ := YoungTableau.exists_smul_eq t s
    rw [← YoungTableau.smul_polytabloid]
    exact U.apply_mem_toSubmodule _ hpolytabloid
  · push Not at hex
    refine Or.inr fun v hv w hw => ?_
    have hspan : w ∈ Submodule.span ℂ (Set.range (YoungTableau.polytabloid (μ := μ))) := hw
    clear hw
    induction hspan using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨t, rfl⟩ := hx
        rw [← YoungTableau.columnAntisymmetriser_tabloid, ← tabloidForm_columnAntisymmetriser,
          hex t v hv, tabloidForm_zero_left]
    | zero => exact tabloidForm_zero_right v
    | add x y _ _ hx hy => rw [tabloidForm_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [tabloidForm_smul_right, hx, mul_zero]

/-- **The Specht module is irreducible.** A nonzero subrepresentation of it would, by the submodule
theorem, be orthogonal to the Specht module while lying inside it, and the tabloid form is positive
definite.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
instance isIrreducible_spechtSubrepresentation {n : ℕ} (μ : YoungDiagramOfSize n) :
    Representation.IsIrreducible (spechtSubrepresentation μ).toRepresentation := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  have hpolytabloid : YoungTableau.polytabloid t ∈ (spechtSubrepresentation μ).toSubmodule :=
    Submodule.subset_span ⟨t, rfl⟩
  haveI : Nontrivial (Subrepresentation (spechtSubrepresentation μ).toRepresentation) := by
    refine ⟨⊥, ⊤, fun hbot => ?_⟩
    have htop : (⊥ : Submodule ℂ ↥(spechtSubrepresentation μ).toSubmodule) = ⊤ :=
      congrArg Subrepresentation.toSubmodule hbot
    have hmem : (⟨YoungTableau.polytabloid t, hpolytabloid⟩ :
        ↥(spechtSubrepresentation μ).toSubmodule) ∈
          (⊥ : Submodule ℂ ↥(spechtSubrepresentation μ).toSubmodule) := by
      rw [htop]
      exact Submodule.mem_top
    rw [Submodule.mem_bot] at hmem
    exact YoungTableau.polytabloid_ne_zero t (by simpa [Subtype.ext_iff] using hmem)
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)) :=
    { toSubmodule :=
        W.toSubmodule.map (spechtSubrepresentation μ).toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨(spechtSubrepresentation μ).toRepresentation g w, W.apply_mem_toSubmodule g hw,
          rfl⟩ }
  rcases spechtSubrepresentation_le_or_forall_tabloidForm_eq_zero μ U with hle | horthogonal
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    rintro x -
    obtain ⟨w, hw, hwx⟩ := hle x.2
    exact Subtype.ext hwx ▸ hw
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    show W.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro x hx
    have hzero : (x : Tabloid μ →₀ ℂ) = 0 :=
      eq_zero_of_tabloidForm_self_eq_zero (horthogonal _ ⟨x, hx, rfl⟩ _ x.2)
    rw [Submodule.mem_bot]
    exact Subtype.ext hzero
