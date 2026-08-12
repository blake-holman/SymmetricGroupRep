import SymmetricGroupRep.YoungGraph
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Standard Young tableaux and the Young graph

A standard tableau of shape `μ` is a bijective labelling of the cells of `μ`
increasing along rows and down columns. Deleting the largest label leaves a
standard tableau of a shape obtained from `μ` by removing one box, and every
such pair arises exactly once, so the number of standard tableaux satisfies the
recursion of the Young graph.

Combining that recursion with the one-box counts of `YoungGraph.lean` gives the
sum over all shapes of the squared tableau counts: it is `n !`. This is the
combinatorial half of the identity that also counts the regular representation
of `S_n`.
-/

/-- A standard tableau of shape `μ`, with labels `0, ..., n - 1` increasing
from left to right and from top to bottom. -/
@[ext]
structure StandardYoungTableau {n : ℕ} (μ : YoungDiagramOfSize n) where
  /-- The bijective labeling of the cells of `μ`. -/
  entry : ↥μ.val.cells ≃ Fin n
  /-- Labels increase strictly along rows. -/
  row_strict : ∀ {c d}, c.1.1 = d.1.1 → c.1.2 < d.1.2 → entry c < entry d
  /-- Labels increase strictly down columns. -/
  col_strict : ∀ {c d}, c.1.2 = d.1.2 → c.1.1 < d.1.1 → entry c < entry d

/-- There are finitely many standard tableaux of a fixed shape. -/
noncomputable instance {n : ℕ} (μ : YoungDiagramOfSize n) :
    Finite (StandardYoungTableau μ) :=
  Finite.of_injective StandardYoungTableau.entry fun T U h => by
    cases T
    cases U
    cases h
    rfl

namespace StandardYoungTableau

/-- The cell carrying the largest entry. -/
def largestCell {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : ↥μ.val.cells :=
  T.entry.symm (Fin.last n)

@[simp]
theorem entry_largestCell {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : T.entry T.largestCell = Fin.last n :=
  T.entry.apply_symm_apply _

/-- Tableau entries are weakly increasing in the product order on cells. -/
theorem entry_le_of_le {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) {c d : ↥μ.val.cells} (h : c.1 ≤ d.1) :
    T.entry c ≤ T.entry d := by
  let e : ↥μ.val.cells :=
    ⟨(c.1.1, d.1.2), μ.val.up_left_mem h.1 le_rfl d.2⟩
  have hce : T.entry c ≤ T.entry e := by
    rcases lt_or_eq_of_le h.2 with hcol | hcol
    · exact (T.row_strict (c := c) (d := e) rfl hcol).le
    · have : c = e := Subtype.ext (Prod.ext rfl hcol)
      simp [this]
  have hed : T.entry e ≤ T.entry d := by
    rcases lt_or_eq_of_le h.1 with hrow | hrow
    · exact (T.col_strict (c := e) (d := d) rfl hrow).le
    · have : e = d := Subtype.ext (Prod.ext hrow rfl)
      simp [this]
  exact hce.trans hed

/-- Remove the cell carrying the largest entry. -/
def eraseLargestDiagram {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : YoungDiagram where
  cells := μ.val.cells.erase T.largestCell.1
  isLowerSet := by
    intro a b hab hb
    change a ∈ μ.val.cells.erase T.largestCell.1 at hb
    change b ∈ μ.val.cells.erase T.largestCell.1
    rw [Finset.mem_erase] at hb ⊢
    refine ⟨?_, μ.val.isLowerSet hab hb.2⟩
    intro hbeq
    subst b
    let d : ↥μ.val.cells := ⟨a, hb.2⟩
    have hle := T.entry_le_of_le (c := T.largestCell) (d := d) hab
    have he : T.entry d = Fin.last n :=
      le_antisymm (Fin.le_last _) (by simpa using hle)
    have hd : d = T.largestCell := T.entry.injective (by simpa using he)
    exact hb.1 (congrArg Subtype.val hd)

/-- The shape left after removing the largest entry. -/
def eraseLargestShape {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : YoungDiagramOfSize n :=
  ⟨T.eraseLargestDiagram, by
    change (μ.val.cells.erase T.largestCell.1).card = n
    rw [Finset.card_erase_of_mem T.largestCell.2]
    change μ.val.card - 1 = n
    rw [μ.property]
    simp⟩

/-- Cells of the erased diagram are the original cells other than the largest one. -/
def remainingCellEquiv {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) :
    ↥(T.eraseLargestShape.val.cells) ≃ {c : ↥μ.val.cells // c ≠ T.largestCell} where
  toFun c :=
    ⟨⟨c.1, (Finset.mem_erase.mp c.2).2⟩, fun h =>
      (Finset.mem_erase.mp c.2).1 (congrArg Subtype.val h)⟩
  invFun c :=
    ⟨c.1.1, Finset.mem_erase.mpr ⟨fun h => c.2 (Subtype.ext h), c.1.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- Removing the largest cell also removes the largest label. -/
def restrictedEntryEquiv {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : ↥(T.eraseLargestShape.val.cells) ≃ Fin n :=
  (T.remainingCellEquiv.trans <|
    T.entry.subtypeEquiv fun c => by
      constructor
      · intro hc he
        apply hc
        apply T.entry.injective
        rw [he, T.entry_largestCell]
      · intro he hc
        apply he
        rw [hc, T.entry_largestCell]).trans
    (finSuccAboveEquiv (Fin.last n)).symm

@[simp]
theorem restrictedEntryEquiv_val {n : ℕ}
    {μ : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau μ)
    (c : ↥(T.eraseLargestShape.val.cells)) :
    (T.restrictedEntryEquiv c).1 =
      (T.entry (T.remainingCellEquiv c).1).1 := by
  rw [restrictedEntryEquiv, Equiv.trans_apply, Equiv.trans_apply,
    finSuccAboveEquiv_symm_apply_last]
  rfl

/-- The standard tableau obtained by deleting its largest entry. -/
def restrictLargest {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : StandardYoungTableau T.eraseLargestShape where
  entry := T.restrictedEntryEquiv
  row_strict := by
    intro c d hrow hcol
    change (T.restrictedEntryEquiv c).1 < (T.restrictedEntryEquiv d).1
    rw [T.restrictedEntryEquiv_val, T.restrictedEntryEquiv_val]
    exact T.row_strict (c := (T.remainingCellEquiv c).1)
      (d := (T.remainingCellEquiv d).1) hrow hcol
  col_strict := by
    intro c d hcol hrow
    change (T.restrictedEntryEquiv c).1 < (T.restrictedEntryEquiv d).1
    rw [T.restrictedEntryEquiv_val, T.restrictedEntryEquiv_val]
    exact T.col_strict (c := (T.remainingCellEquiv c).1)
      (d := (T.remainingCellEquiv d).1) hcol hrow

/-- The one-box removal selected by a tableau's largest entry. -/
def largestRemoval {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) : OneBoxRemoval μ :=
  ⟨T.eraseLargestShape,
    YoungDiagram.cells_subset_iff.mp (Finset.erase_subset _ _)⟩

/-- A tableau and its largest entry determine the corresponding branching summand. -/
def restrictLargestIndex {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) :
    Σ ν : OneBoxRemoval μ, StandardYoungTableau ν.val :=
  ⟨T.largestRemoval, T.restrictLargest⟩

end StandardYoungTableau

namespace OneBoxRemoval

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}

/-- The single cell of `μ` that a one-box removal deletes. -/
noncomputable def cell (ν : OneBoxRemoval μ) : ℕ × ℕ :=
  (Finset.card_eq_one.mp ν.2.card_sdiff).choose

theorem sdiff_eq_cell (ν : OneBoxRemoval μ) :
    μ.val.cells \ ν.val.val.cells = {cell ν} :=
  (Finset.card_eq_one.mp ν.2.card_sdiff).choose_spec

theorem cells_subset (ν : OneBoxRemoval μ) : ν.val.val.cells ⊆ μ.val.cells :=
  YoungDiagram.cells_subset_iff.mpr ν.2

theorem eq_cell_of_notMem (ν : OneBoxRemoval μ) {d : ℕ × ℕ} (hd : d ∈ μ.val.cells)
    (h : d ∉ ν.val.val.cells) : d = cell ν :=
  Finset.mem_singleton.mp (sdiff_eq_cell ν ▸ Finset.mem_sdiff.mpr ⟨hd, h⟩)

theorem cell_mem (ν : OneBoxRemoval μ) : cell ν ∈ μ.val.cells :=
  (Finset.mem_sdiff.mp (sdiff_eq_cell ν ▸ Finset.mem_singleton_self (cell ν))).1

theorem cell_notMem (ν : OneBoxRemoval μ) : cell ν ∉ ν.val.val.cells :=
  (Finset.mem_sdiff.mp (sdiff_eq_cell ν ▸ Finset.mem_singleton_self (cell ν))).2

theorem cells_eq_erase (ν : OneBoxRemoval μ) :
    ν.val.val.cells = μ.val.cells.erase (cell ν) := by
  refine Finset.eq_of_subset_of_card_le
    (Finset.subset_erase.mpr ⟨cells_subset ν, cell_notMem ν⟩) ?_
  have h₁ : ν.val.val.cells.card = n := ν.val.property
  have h₂ : μ.val.cells.card = n + 1 := μ.property
  rw [Finset.card_erase_of_mem (cell_mem ν)]
  omega

/-- Splitting the cells of `μ` into the cells of `ν` and the deleted cell. -/
noncomputable def cellEquivOption (ν : OneBoxRemoval μ) :
    ↥μ.val.cells ≃ Option ↥ν.val.val.cells where
  toFun d := if h : d.1 ∈ ν.val.val.cells then some ⟨d.1, h⟩ else none
  invFun e := e.elim ⟨cell ν, cell_mem ν⟩ fun c => ⟨c.1, cells_subset ν c.2⟩
  left_inv d := by
    by_cases h : d.1 ∈ ν.val.val.cells
    · simp [h]
    · simp only [h, dif_neg, Option.elim, not_false_eq_true]
      exact Subtype.ext (eq_cell_of_notMem ν d.2 h).symm
  right_inv e := by
    cases e with
    | none => simp [cell_notMem ν]
    | some c => simp [c.2]

/-- Extend a standard tableau of a one-box removal by writing the largest label in the deleted
cell. -/
noncomputable def extend (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val) :
    StandardYoungTableau μ where
  entry := ((cellEquivOption ν).trans (Equiv.optionCongr S.entry)).trans finSuccEquivLast.symm
  row_strict := by
    intro c d hrow hcol
    show finSuccEquivLast.symm _ < finSuccEquivLast.symm _
    by_cases hd : d.1 ∈ ν.val.val.cells
    · have hc : c.1 ∈ ν.val.val.cells :=
        ν.val.val.up_left_mem (le_of_eq hrow) hcol.le hd
      simp only [cellEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
        hc, hd, dif_pos, Option.map_some, finSuccEquivLast_symm_some, Fin.castSucc_lt_castSucc_iff]
      exact S.row_strict (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hrow hcol
    · by_cases hc : c.1 ∈ ν.val.val.cells
      · simp only [cellEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
          hc, hd, dif_pos, dif_neg, not_false_eq_true, Option.map_some, Option.map_none,
          finSuccEquivLast_symm_some, finSuccEquivLast_symm_none]
        exact Fin.castSucc_lt_last _
      · exact absurd ((eq_cell_of_notMem ν c.2 hc).trans (eq_cell_of_notMem ν d.2 hd).symm)
          fun h => absurd (congrArg Prod.snd h) (by omega)
  col_strict := by
    intro c d hcol hrow
    show finSuccEquivLast.symm _ < finSuccEquivLast.symm _
    by_cases hd : d.1 ∈ ν.val.val.cells
    · have hc : c.1 ∈ ν.val.val.cells :=
        ν.val.val.up_left_mem hrow.le (le_of_eq hcol) hd
      simp only [cellEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
        hc, hd, dif_pos, Option.map_some, finSuccEquivLast_symm_some, Fin.castSucc_lt_castSucc_iff]
      exact S.col_strict (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcol hrow
    · by_cases hc : c.1 ∈ ν.val.val.cells
      · simp only [cellEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
          hc, hd, dif_pos, dif_neg, not_false_eq_true, Option.map_some, Option.map_none,
          finSuccEquivLast_symm_some, finSuccEquivLast_symm_none]
        exact Fin.castSucc_lt_last _
      · exact absurd ((eq_cell_of_notMem ν c.2 hc).trans (eq_cell_of_notMem ν d.2 hd).symm)
          fun h => absurd (congrArg Prod.fst h) (by omega)

theorem entry_extend_of_mem (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val)
    (d : ↥μ.val.cells) (h : d.1 ∈ ν.val.val.cells) :
    (extend ν S).entry d = (S.entry ⟨d.1, h⟩).castSucc := by
  have hd : (cellEquivOption ν) d = some ⟨d.1, h⟩ := dif_pos h
  show finSuccEquivLast.symm ((Equiv.optionCongr S.entry) ((cellEquivOption ν) d)) = _
  rw [hd]
  simp

theorem entry_extend_cell (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val)
    (d : ↥μ.val.cells) (h : d.1 ∉ ν.val.val.cells) : (extend ν S).entry d = Fin.last n := by
  have hd : (cellEquivOption ν) d = none := dif_neg h
  show finSuccEquivLast.symm ((Equiv.optionCongr S.entry) ((cellEquivOption ν) d)) = _
  rw [hd]
  simp

end OneBoxRemoval

/-- The cell deleted by the removal a tableau selects is the cell of its largest label. -/
theorem StandardYoungTableau.cell_largestRemoval {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) :
    OneBoxRemoval.cell T.largestRemoval = T.largestCell.1 := by
  have hcells : T.largestRemoval.val.val.cells = μ.val.cells.erase T.largestCell.1 := rfl
  have hsdiff := OneBoxRemoval.sdiff_eq_cell T.largestRemoval
  rw [hcells] at hsdiff
  have herase : μ.val.cells \ μ.val.cells.erase T.largestCell.1 = {T.largestCell.1} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hx'⟩
      by_contra hne
      exact hx' ⟨hne, hx⟩
    · rintro rfl
      exact ⟨T.largestCell.2, fun h => h.1 rfl⟩
  exact (Finset.singleton_injective (herase.symm.trans hsdiff)).symm

/-- Deleting the largest label and writing it back restores the tableau. -/
theorem OneBoxRemoval.extend_restrictLargest {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) :
    OneBoxRemoval.extend T.largestRemoval T.restrictLargest = T := by
  have hcells : T.largestRemoval.val.val.cells = μ.val.cells.erase T.largestCell.1 := rfl
  refine StandardYoungTableau.ext (Equiv.ext fun d => ?_)
  by_cases hd : d.1 ∈ T.largestRemoval.val.val.cells
  · rw [OneBoxRemoval.entry_extend_of_mem _ _ d hd]
    refine Fin.ext ?_
    rw [Fin.val_castSucc]
    exact T.restrictedEntryEquiv_val ⟨d.1, hd⟩
  · rw [OneBoxRemoval.entry_extend_cell _ _ d hd]
    have hlargest : d = T.largestCell := by
      refine Subtype.ext ?_
      rw [hcells, Finset.mem_erase] at hd
      exact not_not.mp fun h => hd ⟨h, d.2⟩
    rw [hlargest, T.entry_largestCell]

/-- Removing the largest label of a standard tableau of shape `μ`, and extending back, are
mutually inverse: standard tableaux of shape `μ` are indexed by a one-box removal of `μ`
together with a standard tableau of that shape. -/
noncomputable def standardYoungTableauEquivRemovals {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    (Σ ν : OneBoxRemoval μ, StandardYoungTableau ν.val) ≃ StandardYoungTableau μ := by
  refine Equiv.ofBijective (fun p => OneBoxRemoval.extend p.1 p.2) ⟨?_, ?_⟩
  · rintro ⟨ν, S⟩ ⟨ν', S'⟩ heq
    have heq' : OneBoxRemoval.extend ν S = OneBoxRemoval.extend ν' S' := heq
    have hlast : ∀ (ξ : OneBoxRemoval μ) (R : StandardYoungTableau ξ.val),
        (OneBoxRemoval.extend ξ R).entry.symm (Fin.last n) =
          ⟨OneBoxRemoval.cell ξ, OneBoxRemoval.cell_mem ξ⟩ := fun ξ R =>
      (Equiv.symm_apply_eq _).mpr
        (OneBoxRemoval.entry_extend_cell ξ R _ (OneBoxRemoval.cell_notMem ξ)).symm
    have hcell : OneBoxRemoval.cell ν = OneBoxRemoval.cell ν' := by
      have := (hlast ν S).symm.trans (heq' ▸ hlast ν' S')
      exact congrArg Subtype.val this
    have hν : ν = ν' :=
      Subtype.ext (Subtype.ext (YoungDiagram.ext (by
        rw [OneBoxRemoval.cells_eq_erase, OneBoxRemoval.cells_eq_erase, hcell])))
    subst hν
    refine congrArg (Sigma.mk ν) (StandardYoungTableau.ext (Equiv.ext fun d => ?_))
    have h₁ := OneBoxRemoval.entry_extend_of_mem ν S ⟨d.1, OneBoxRemoval.cells_subset ν d.2⟩ d.2
    have h₂ := OneBoxRemoval.entry_extend_of_mem ν S' ⟨d.1, OneBoxRemoval.cells_subset ν d.2⟩ d.2
    rw [heq', h₂] at h₁
    exact Fin.castSucc_injective n h₁.symm
  · exact fun T => ⟨⟨T.largestRemoval, T.restrictLargest⟩, OneBoxRemoval.extend_restrictLargest T⟩

/-- The diagrams obtained from `ν` by adding one box. -/
noncomputable def oneBoxAdditions {n : ℕ} (ν : YoungDiagramOfSize n) :
    Finset (YoungDiagramOfSize (n + 1)) :=
  Finset.univ.filter fun lam => ν.val ≤ lam.val

/-- The diagrams obtained from `μ` by removing one box. -/
noncomputable def oneBoxRemovals {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    Finset (YoungDiagramOfSize n) :=
  Finset.univ.filter fun ν => ν.val ≤ μ.val

@[simp]
theorem mem_oneBoxAdditions {n : ℕ} {ν : YoungDiagramOfSize n}
    {lam : YoungDiagramOfSize (n + 1)} : lam ∈ oneBoxAdditions ν ↔ ν.val ≤ lam.val := by
  simp [oneBoxAdditions]

@[simp]
theorem mem_oneBoxRemovals {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    {ν : YoungDiagramOfSize n} : ν ∈ oneBoxRemovals μ ↔ ν.val ≤ μ.val := by
  simp [oneBoxRemovals]

theorem card_oneBoxAdditions {n : ℕ} (ν : YoungDiagramOfSize n) :
    (oneBoxAdditions ν).card = Nat.card (OneBoxAddition ν) := by
  letI : Fintype (OneBoxAddition ν) := Fintype.ofFinite _
  rw [Finset.card_eq_sum_ones, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  exact Finset.sum_subtype (p := fun lam : YoungDiagramOfSize (n + 1) => IsOneBoxAddition ν lam) _
    (fun _ => by simp [IsOneBoxAddition, IsOneBoxRemoval]) fun _ => 1

theorem card_oneBoxRemovals {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    (oneBoxRemovals μ).card = Nat.card (OneBoxRemoval μ) := by
  letI : Fintype (OneBoxRemoval μ) := Fintype.ofFinite _
  rw [Finset.card_eq_sum_ones, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  exact Finset.sum_subtype (p := fun ν : YoungDiagramOfSize n => IsOneBoxRemoval ν μ) _
    (fun _ => by simp [IsOneBoxRemoval]) fun _ => 1

/-- The number of standard tableaux of shape `μ` is the sum of the numbers of standard tableaux
of the shapes obtained from `μ` by removing one box. -/
theorem card_standardYoungTableau_succ {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    Nat.card (StandardYoungTableau μ) =
      ∑ ν ∈ oneBoxRemovals μ, Nat.card (StandardYoungTableau ν) := by
  letI : Fintype (OneBoxRemoval μ) := Fintype.ofFinite _
  rw [← Nat.card_congr (standardYoungTableauEquivRemovals μ), Nat.card_sigma]
  exact (Finset.sum_subtype (p := fun ν : YoungDiagramOfSize n => IsOneBoxRemoval ν μ) _
    (fun _ => by simp [IsOneBoxRemoval]) fun ν => Nat.card (StandardYoungTableau ν)).symm

/-- Adding a box and then removing one visits every diagram that removing a box and then adding
one visits, and additionally revisits `ν` itself once. This is the commutation relation of the
Young graph. -/
theorem sum_addition_removal_add_card_removals {n : ℕ} (ν : YoungDiagramOfSize (n + 1))
    (g : YoungDiagramOfSize (n + 1) → ℕ) :
    (∑ lam ∈ oneBoxAdditions ν, ∑ ν' ∈ oneBoxRemovals lam, g ν') +
        (oneBoxRemovals ν).card * g ν =
      (∑ xi ∈ oneBoxRemovals ν, ∑ ν' ∈ oneBoxAdditions xi, g ν') +
        (oneBoxAdditions ν).card * g ν := by
  have hleft : ∀ ν' : YoungDiagramOfSize (n + 1),
      ∑ lam ∈ oneBoxAdditions ν, (if ν'.val ≤ lam.val then g ν' else 0) =
        (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
          ν.val ≤ lam.val ∧ ν'.val ≤ lam.val).card * g ν' := by
    intro ν'
    rw [← Finset.sum_filter, Finset.sum_const, oneBoxAdditions, Finset.filter_filter]
    simp
  have hright : ∀ ν' : YoungDiagramOfSize (n + 1),
      ∑ xi ∈ oneBoxRemovals ν, (if xi.val ≤ ν'.val then g ν' else 0) =
        (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
          xi.val ≤ ν.val ∧ xi.val ≤ ν'.val).card * g ν' := by
    intro ν'
    rw [← Finset.sum_filter, Finset.sum_const, oneBoxRemovals, Finset.filter_filter]
    simp
  have expandLeft : ∑ lam ∈ oneBoxAdditions ν, ∑ ν' ∈ oneBoxRemovals lam, g ν' =
      ∑ ν' : YoungDiagramOfSize (n + 1),
        (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
          ν.val ≤ lam.val ∧ ν'.val ≤ lam.val).card * g ν' := by
    simp only [← hleft, oneBoxRemovals, Finset.sum_filter]
    exact Finset.sum_comm
  have expandRight : ∑ xi ∈ oneBoxRemovals ν, ∑ ν' ∈ oneBoxAdditions xi, g ν' =
      ∑ ν' : YoungDiagramOfSize (n + 1),
        (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
          xi.val ≤ ν.val ∧ xi.val ≤ ν'.val).card * g ν' := by
    simp only [← hright, oneBoxAdditions, Finset.sum_filter]
    exact Finset.sum_comm
  rw [expandLeft, expandRight,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ ν),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ ν)]
  have hdiag₁ : (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
      ν.val ≤ lam.val ∧ ν.val ≤ lam.val) = oneBoxAdditions ν := by
    simp [oneBoxAdditions]
  have hdiag₂ : (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
      xi.val ≤ ν.val ∧ xi.val ≤ ν.val) = oneBoxRemovals ν := by
    simp [oneBoxRemovals]
  have hoff : ∑ ν' ∈ Finset.univ.erase ν,
        (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
          ν.val ≤ lam.val ∧ ν'.val ≤ lam.val).card * g ν' =
      ∑ ν' ∈ Finset.univ.erase ν,
        (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
          xi.val ≤ ν.val ∧ xi.val ≤ ν'.val).card * g ν' :=
    Finset.sum_congr rfl fun ν' hν' => by
      rw [card_filter_common_addition_eq_card_filter_common_removal ν ν'
        (Ne.symm (Finset.mem_erase.mp hν').1)]
  rw [hdiag₁, hdiag₂, hoff]
  omega

/-- Summing over one-box removals of every shape of size `n + 1` is summing over one-box
additions to every shape of size `n`. -/
theorem sum_oneBoxRemovals_comm {n : ℕ}
    (h : YoungDiagramOfSize (n + 1) → YoungDiagramOfSize n → ℕ) :
    ∑ μ : YoungDiagramOfSize (n + 1), ∑ ν ∈ oneBoxRemovals μ, h μ ν =
      ∑ ν : YoungDiagramOfSize n, ∑ μ ∈ oneBoxAdditions ν, h μ ν := by
  simp only [oneBoxRemovals, oneBoxAdditions, Finset.sum_filter]
  exact Finset.sum_comm

/-- The only shape of size zero is the empty one. -/
theorem YoungDiagramOfSize.eq_bot (ν : YoungDiagramOfSize 0) : ν.val = ⊥ :=
  YoungDiagram.ext (by rw [Finset.card_eq_zero.mp ν.property]; rfl)

/-- There is only the empty shape of size zero. -/
theorem card_youngDiagramOfSize_zero : Nat.card (YoungDiagramOfSize 0) = 1 :=
  Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun μ ν => Subtype.ext ((YoungDiagramOfSize.eq_bot μ).trans
      (YoungDiagramOfSize.eq_bot ν).symm)⟩, ⟨⟨⊥, by simp⟩⟩⟩

/-- The empty shape has exactly one standard tableau. -/
theorem card_standardYoungTableau_of_isEmpty (μ : YoungDiagramOfSize 0) :
    Nat.card (StandardYoungTableau μ) = 1 := by
  have hcells : μ.val.cells = ∅ := Finset.card_eq_zero.mp μ.property
  haveI : IsEmpty ↥μ.val.cells := ⟨fun c => Finset.notMem_empty c.1 (hcells ▸ c.2)⟩
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun T U => ?_⟩, ⟨?_⟩⟩
  · exact StandardYoungTableau.ext (Equiv.ext fun c => isEmptyElim c)
  · exact ⟨Equiv.equivOfIsEmpty _ _, fun {c} => isEmptyElim c, fun {c} => isEmptyElim c⟩

/-- A shape with a single cell has exactly one standard tableau. -/
theorem card_standardYoungTableau_of_card_one (lam : YoungDiagramOfSize 1) :
    Nat.card (StandardYoungTableau lam) = 1 := by
  have huniv : oneBoxRemovals lam = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun ν => by
      rw [mem_oneBoxRemovals, YoungDiagramOfSize.eq_bot ν]
      exact bot_le
  rw [card_standardYoungTableau_succ lam, huniv,
    Finset.sum_congr rfl fun ν _ => card_standardYoungTableau_of_isEmpty ν, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_youngDiagramOfSize_zero]
  simp

/-- Adding a box to a shape of size `n` in every possible way multiplies the number of standard
tableaux by `n + 1`. -/
theorem sum_card_standardYoungTableau_oneBoxAdditions :
    ∀ {n : ℕ} (ν : YoungDiagramOfSize n),
      ∑ lam ∈ oneBoxAdditions ν, Nat.card (StandardYoungTableau lam) =
        (n + 1) * Nat.card (StandardYoungTableau ν) := by
  intro n
  induction n with
  | zero =>
    intro ν
    rw [Finset.sum_congr rfl fun lam _ => card_standardYoungTableau_of_card_one lam,
      Finset.sum_const, card_oneBoxAdditions, card_oneBoxAddition_of_isEmpty,
      card_standardYoungTableau_of_isEmpty ν]
    simp
  | succ n ih =>
    intro ν
    have hcomm := sum_addition_removal_add_card_removals ν
      fun ν' => Nat.card (StandardYoungTableau ν')
    have hrec : ∑ lam ∈ oneBoxAdditions ν, Nat.card (StandardYoungTableau lam) =
        ∑ lam ∈ oneBoxAdditions ν, ∑ ν' ∈ oneBoxRemovals lam,
          Nat.card (StandardYoungTableau ν') :=
      Finset.sum_congr rfl fun lam _ => card_standardYoungTableau_succ lam
    have hIH : ∑ xi ∈ oneBoxRemovals ν, ∑ ν' ∈ oneBoxAdditions xi,
        Nat.card (StandardYoungTableau ν') =
          (n + 1) * Nat.card (StandardYoungTableau ν) := by
      rw [Finset.sum_congr rfl fun xi _ => ih xi, ← Finset.mul_sum,
        ← card_standardYoungTableau_succ ν]
    have hcard : (oneBoxAdditions ν).card = (oneBoxRemovals ν).card + 1 := by
      rw [card_oneBoxAdditions, card_oneBoxRemovals, card_oneBoxAddition_eq_succ]
    rw [hIH, hcard] at hcomm
    rw [hrec]
    refine Nat.add_right_cancel (m := (oneBoxRemovals ν).card *
      Nat.card (StandardYoungTableau ν)) ?_
    rw [hcomm]
    ring

/-- The sum over all shapes of size `n` of the squared number of standard tableaux is `n !`. -/
theorem sum_card_standardYoungTableau_sq (n : ℕ) :
    ∑ μ : YoungDiagramOfSize n, Nat.card (StandardYoungTableau μ) ^ 2 = n.factorial := by
  induction n with
  | zero =>
    rw [Finset.sum_congr rfl fun μ _ => congrArg (· ^ 2)
        (card_standardYoungTableau_of_isEmpty μ),
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      card_youngDiagramOfSize_zero]
    simp
  | succ n ih =>
    have hrec : ∑ μ : YoungDiagramOfSize (n + 1), Nat.card (StandardYoungTableau μ) ^ 2 =
        ∑ μ : YoungDiagramOfSize (n + 1), ∑ ν ∈ oneBoxRemovals μ,
          Nat.card (StandardYoungTableau μ) * Nat.card (StandardYoungTableau ν) :=
      Finset.sum_congr rfl fun μ _ => by
        rw [← Finset.mul_sum, ← card_standardYoungTableau_succ μ, sq]
    rw [hrec, sum_oneBoxRemovals_comm, Nat.factorial_succ, ← ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Finset.sum_mul, sum_card_standardYoungTableau_oneBoxAdditions ν, sq]
    ring
