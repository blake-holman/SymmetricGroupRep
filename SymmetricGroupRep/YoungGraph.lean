import SymmetricGroupRep.YoungDiagrams
import Mathlib.SetTheory.Cardinal.Finite

/-! # Adding and removing a single box

A Young diagram containing `μ` and one further box is obtained by lengthening a
single row, and a diagram contained in `μ` with one box fewer is obtained by
shortening a single row. This file records both constructions, identifies the
rows they are allowed to use, and derives the two counts that the Young graph is
built from: a diagram has exactly one more one-box addition than it has one-box
removals, and two distinct diagrams of the same size have a common one-box
extension exactly when they have a common one-box contraction.
-/

namespace YoungDiagram

/-- The diagram obtained from `μ` by adding the first empty cell of row `i`. This is a Young
diagram exactly when every earlier row is strictly longer. -/
def addBox (μ : YoungDiagram) (i : ℕ) (h : ∀ k < i, μ.rowLen i < μ.rowLen k) : YoungDiagram where
  cells := insert (i, μ.rowLen i) μ.cells
  isLowerSet := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hba ha
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, mem_cells,
      Prod.mk.injEq] at ha ⊢
    rcases ha with ⟨rfl, rfl⟩ | ha
    · have hb₁ : b₁ ≤ a₁ := hba.1
      have hb₂ : b₂ ≤ μ.rowLen a₁ := hba.2
      rcases Nat.lt_or_ge b₁ a₁ with hlt | hge
      · exact Or.inr (mem_iff_lt_rowLen.mpr (lt_of_le_of_lt hb₂ (h b₁ hlt)))
      · have heq : b₁ = a₁ := le_antisymm hb₁ hge
        rcases Nat.lt_or_ge b₂ (μ.rowLen b₁) with hlt₂ | hge₂
        · exact Or.inr (mem_iff_lt_rowLen.mpr hlt₂)
        · rw [heq] at hge₂
          exact Or.inl ⟨heq, le_antisymm hb₂ hge₂⟩
    · exact Or.inr (μ.isLowerSet hba ha)

/-- The diagram obtained from `μ` by deleting the last cell of row `i`. This is a Young diagram
exactly when every later row is strictly shorter. -/
def removeBox (μ : YoungDiagram) (i : ℕ) (h : ∀ k, i < k → μ.rowLen k < μ.rowLen i) :
    YoungDiagram where
  cells := μ.cells.erase (i, μ.rowLen i - 1)
  isLowerSet := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hba ha
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, mem_cells,
      Set.mem_singleton_iff, Prod.mk.injEq] at ha ⊢
    refine ⟨μ.isLowerSet hba ha.1, ?_⟩
    rintro ⟨rfl, rfl⟩
    have hstep := h (b₁ + 1) (Nat.lt_succ_self _)
    have ha₂ : a₂ < μ.rowLen a₁ := mem_iff_lt_rowLen.mp ha.1
    have hb₁ : b₁ ≤ a₁ := hba.1
    have hb₂ : μ.rowLen b₁ - 1 ≤ a₂ := hba.2
    have ha₁ : a₁ = b₁ := by
      rcases Nat.lt_or_ge b₁ a₁ with hlt | hge
      · have := h a₁ hlt
        omega
      · exact le_antisymm hge hb₁
    refine ha.2 ⟨ha₁, ?_⟩
    rw [ha₁] at ha₂
    omega

variable {μ : YoungDiagram} {i : ℕ}

@[simp]
theorem cells_addBox (h : ∀ k < i, μ.rowLen i < μ.rowLen k) :
    (μ.addBox i h).cells = insert (i, μ.rowLen i) μ.cells := rfl

@[simp]
theorem cells_removeBox (h : ∀ k, i < k → μ.rowLen k < μ.rowLen i) :
    (μ.removeBox i h).cells = μ.cells.erase (i, μ.rowLen i - 1) := rfl

theorem notMem_rowLen (μ : YoungDiagram) (i : ℕ) : (i, μ.rowLen i) ∉ μ := by
  simp [mem_iff_lt_rowLen]

theorem rowLen_pos (h : ∀ k, i < k → μ.rowLen k < μ.rowLen i) : 0 < μ.rowLen i :=
  Nat.pos_of_ne_zero fun h0 => by simpa [h0] using h (i + 1) (Nat.lt_succ_self _)

theorem le_addBox (h : ∀ k < i, μ.rowLen i < μ.rowLen k) : μ ≤ μ.addBox i h :=
  cells_subset_iff.mp (Finset.subset_insert _ _)

theorem removeBox_le (h : ∀ k, i < k → μ.rowLen k < μ.rowLen i) : μ.removeBox i h ≤ μ :=
  cells_subset_iff.mp (Finset.erase_subset _ _)

theorem card_addBox (h : ∀ k < i, μ.rowLen i < μ.rowLen k) :
    (μ.addBox i h).card = μ.card + 1 :=
  Finset.card_insert_of_notMem (μ.notMem_rowLen i)

theorem card_removeBox (h : ∀ k, i < k → μ.rowLen k < μ.rowLen i) :
    (μ.removeBox i h).card + 1 = μ.card :=
  Finset.card_erase_add_one (mem_iff_lt_rowLen.mpr (by have := rowLen_pos h; omega))

/-- The row lengthened by a one-box addition is determined by the resulting diagram. -/
theorem addBox_injective {j : ℕ} {h : ∀ k < i, μ.rowLen i < μ.rowLen k}
    {h' : ∀ k < j, μ.rowLen j < μ.rowLen k} (heq : μ.addBox i h = μ.addBox j h') : i = j := by
  have hmem : (i, μ.rowLen i) ∈ insert (j, μ.rowLen j) μ.cells := by
    rw [show insert (j, μ.rowLen j) μ.cells = (μ.addBox j h').cells from rfl, ← heq]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hmem with h₁ | h₁
  · exact (Prod.mk.injEq .. ▸ h₁).1
  · exact absurd h₁ (μ.notMem_rowLen i)

/-- The row shortened by a one-box removal is determined by the resulting diagram. -/
theorem removeBox_injective {j : ℕ} {h : ∀ k, i < k → μ.rowLen k < μ.rowLen i}
    {h' : ∀ k, j < k → μ.rowLen k < μ.rowLen j} (heq : μ.removeBox i h = μ.removeBox j h') :
    i = j := by
  have hi : (i, μ.rowLen i - 1) ∈ μ.cells :=
    mem_iff_lt_rowLen.mpr (by have := rowLen_pos h; omega)
  have hj : (j, μ.rowLen j - 1) ∈ μ.cells :=
    mem_iff_lt_rowLen.mpr (by have := rowLen_pos h'; omega)
  by_contra hne
  have hmem : (i, μ.rowLen i - 1) ∈ μ.cells.erase (j, μ.rowLen j - 1) :=
    Finset.mem_erase.mpr ⟨fun hcell => hne (Prod.mk.injEq .. ▸ hcell).1, hi⟩
  rw [show μ.cells.erase (j, μ.rowLen j - 1) = (μ.removeBox j h').cells from rfl, ← heq] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

/-- A diagram containing `μ` with one further cell lengthens a single row of `μ`. -/
theorem exists_addBox_eq {lam : YoungDiagram} (hle : μ ≤ lam) (hcard : lam.card = μ.card + 1) :
    ∃ i, ∃ h : ∀ k < i, μ.rowLen i < μ.rowLen k, μ.addBox i h = lam := by
  have hsub : μ.cells ⊆ lam.cells := cells_subset_iff.mpr hle
  have hcard' : lam.cells.card = μ.cells.card + 1 := hcard
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp
    (show (lam.cells \ μ.cells).card = 1 by
      rw [Finset.card_sdiff_of_subset hsub]; omega)
  have hcmem := Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)
  have hkey : ∀ d, d ∈ lam.cells → d ∉ μ.cells → d = c := fun d hd hd' =>
    Finset.mem_singleton.mp (hc ▸ Finset.mem_sdiff.mpr ⟨hd, hd'⟩)
  have hc₂ : c.2 = μ.rowLen c.1 := by
    rcases Nat.lt_trichotomy c.2 (μ.rowLen c.1) with hlt | heq | hgt
    · exact absurd (mem_iff_lt_rowLen.mpr hlt) hcmem.2
    · exact heq
    · have := hkey _ (lam.up_left_mem le_rfl hgt.le hcmem.1) (μ.notMem_rowLen c.1)
      exact absurd (congrArg Prod.snd this) (by omega)
  have hrow : ∀ k < c.1, μ.rowLen c.1 < μ.rowLen k := by
    intro k hk
    by_contra hcon
    rw [not_lt] at hcon
    have := hkey _ (lam.up_left_mem hk.le (hc₂ ▸ hcon) hcmem.1) (μ.notMem_rowLen k)
    exact absurd (congrArg Prod.fst this) (by omega)
  refine ⟨c.1, hrow, YoungDiagram.ext ?_⟩
  have hcc : (c.1, μ.rowLen c.1) = c := by rw [← hc₂]
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · rw [cells_addBox, hcc]
    exact Finset.insert_subset hcmem.1 hsub
  · rw [cells_addBox, hcc, Finset.card_insert_of_notMem hcmem.2]
    omega

/-- A diagram contained in `μ` with one cell fewer shortens a single row of `μ`. -/
theorem exists_removeBox_eq {xi : YoungDiagram} (hle : xi ≤ μ) (hcard : μ.card = xi.card + 1) :
    ∃ i, ∃ h : ∀ k, i < k → μ.rowLen k < μ.rowLen i, μ.removeBox i h = xi := by
  have hsub : xi.cells ⊆ μ.cells := cells_subset_iff.mpr hle
  have hcard' : μ.cells.card = xi.cells.card + 1 := hcard
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp
    (show (μ.cells \ xi.cells).card = 1 by
      rw [Finset.card_sdiff_of_subset hsub]; omega)
  have hcmem := Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)
  have hkey : ∀ d, d ∈ μ.cells → d ∉ xi.cells → d = c := fun d hd hd' =>
    Finset.mem_singleton.mp (hc ▸ Finset.mem_sdiff.mpr ⟨hd, hd'⟩)
  have hlt : c.2 < μ.rowLen c.1 := mem_iff_lt_rowLen.mp hcmem.1
  have hc₂ : c.2 + 1 = μ.rowLen c.1 := by
    by_contra hne
    have hmem : (c.1, c.2 + 1) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
    have := hkey _ hmem fun hxi => hcmem.2 (xi.up_left_mem le_rfl (Nat.le_succ _) hxi)
    exact absurd (congrArg Prod.snd this) (by omega)
  have hrow : ∀ k, c.1 < k → μ.rowLen k < μ.rowLen c.1 := by
    intro k hk
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : (k, c.2) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
    have := hkey _ hmem fun hxi => hcmem.2 (xi.up_left_mem hk.le le_rfl hxi)
    exact absurd (congrArg Prod.fst this) (by omega)
  refine ⟨c.1, hrow, YoungDiagram.ext ?_⟩
  have hcc : (c.1, μ.rowLen c.1 - 1) = c := by
    rw [← hc₂]
    simp
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · rw [cells_removeBox, hcc]
    exact Finset.subset_erase.mpr ⟨hsub, hcmem.2⟩
  · rw [cells_removeBox, hcc, Finset.card_erase_of_mem hcmem.1]
    omega

instance : DecidableEq YoungDiagram := fun μ ν =>
  decidable_of_iff (μ.cells = ν.cells) ⟨YoungDiagram.ext, congrArg _⟩

instance : DecidableRel ((· ≤ ·) : YoungDiagram → YoungDiagram → Prop) := fun _ _ =>
  decidable_of_iff _ cells_subset_iff

/-- The rows of `μ` whose last cell can be deleted. -/
def removeRows (μ : YoungDiagram) : Finset ℕ :=
  (Finset.range μ.card).filter fun i => μ.rowLen (i + 1) < μ.rowLen i

/-- The rows of `μ` that can be extended by one cell, namely the first row and the row below
each row that can be shortened. -/
def addRows (μ : YoungDiagram) : Finset ℕ :=
  insert 0 ((removeRows μ).image (· + 1))

theorem mem_removeRows : i ∈ removeRows μ ↔ ∀ k, i < k → μ.rowLen k < μ.rowLen i := by
  rw [removeRows, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h k hk => lt_of_le_of_lt (μ.rowLen_anti _ _ hk) h.2, fun h => ⟨?_, h _ (by omega)⟩⟩
  exact μ.cell_fst_lt_card (mem_iff_lt_rowLen.mpr (rowLen_pos h))

theorem mem_addRows : i ∈ addRows μ ↔ ∀ k < i, μ.rowLen i < μ.rowLen k := by
  cases i with
  | zero => simp [addRows]
  | succ j =>
    rw [addRows, Finset.mem_insert]
    simp only [Nat.succ_ne_zero, false_or, Finset.mem_image, add_left_inj, exists_eq_right,
      mem_removeRows]
    refine ⟨fun h k hk => lt_of_lt_of_le (h (j + 1) (by omega)) (μ.rowLen_anti _ _ (by omega)),
      fun h k hk => lt_of_le_of_lt (μ.rowLen_anti _ _ hk) (h j (by omega))⟩

theorem card_addRows (μ : YoungDiagram) : (addRows μ).card = (removeRows μ).card + 1 := by
  rw [addRows, Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (add_left_injective 1)]

end YoungDiagram

/-- One-box additions to `ν` are the extensions of its extendable rows. -/
theorem card_oneBoxAddition {n : ℕ} (ν : YoungDiagramOfSize n) :
    Nat.card (OneBoxAddition ν) = (YoungDiagram.addRows ν.val).card := by
  have hcard : ν.val.card = n := ν.property
  have key : Function.Bijective fun i : ↥(YoungDiagram.addRows ν.val) =>
      (⟨⟨ν.val.addBox i.1 (YoungDiagram.mem_addRows.mp i.2), by
          rw [YoungDiagram.card_addBox, hcard]⟩,
        YoungDiagram.le_addBox (YoungDiagram.mem_addRows.mp i.2)⟩ : OneBoxAddition ν) := by
    constructor
    · exact fun i j hij => Subtype.ext (YoungDiagram.addBox_injective
        (h := YoungDiagram.mem_addRows.mp i.2) (h' := YoungDiagram.mem_addRows.mp j.2)
        (congrArg (fun x => x.val.val) hij))
    · rintro ⟨lam, hlam⟩
      obtain ⟨i, h, hi⟩ := YoungDiagram.exists_addBox_eq hlam (by rw [lam.property, hcard])
      exact ⟨⟨i, YoungDiagram.mem_addRows.mpr h⟩, Subtype.ext (Subtype.ext hi)⟩
  rw [← Nat.card_eq_of_bijective _ key, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- One-box removals from `μ` are the contractions of its shortenable rows. -/
theorem card_oneBoxRemoval {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    Nat.card (OneBoxRemoval μ) = (YoungDiagram.removeRows μ.val).card := by
  have hcard : μ.val.card = n + 1 := μ.property
  have key : Function.Bijective fun i : ↥(YoungDiagram.removeRows μ.val) =>
      (⟨⟨μ.val.removeBox i.1 (YoungDiagram.mem_removeRows.mp i.2), by
          have := YoungDiagram.card_removeBox (YoungDiagram.mem_removeRows.mp i.2)
          omega⟩,
        YoungDiagram.removeBox_le (YoungDiagram.mem_removeRows.mp i.2)⟩ : OneBoxRemoval μ) := by
    constructor
    · exact fun i j hij => Subtype.ext (YoungDiagram.removeBox_injective
        (h := YoungDiagram.mem_removeRows.mp i.2) (h' := YoungDiagram.mem_removeRows.mp j.2)
        (congrArg (fun x => x.val.val) hij))
    · rintro ⟨xi, hxi⟩
      obtain ⟨i, h, hi⟩ := YoungDiagram.exists_removeBox_eq hxi (by rw [xi.property, hcard])
      exact ⟨⟨i, YoungDiagram.mem_removeRows.mpr h⟩, Subtype.ext (Subtype.ext hi)⟩
  rw [← Nat.card_eq_of_bijective _ key, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- A diagram has exactly one more one-box addition than it has one-box removals. -/
theorem card_oneBoxAddition_eq_succ {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    Nat.card (OneBoxAddition μ) = Nat.card (OneBoxRemoval μ) + 1 := by
  rw [card_oneBoxAddition, card_oneBoxRemoval, YoungDiagram.card_addRows]

/-- The empty diagram has a single one-box addition. -/
theorem card_oneBoxAddition_of_isEmpty (μ : YoungDiagramOfSize 0) :
    Nat.card (OneBoxAddition μ) = 1 := by
  have hcard : μ.val.card = 0 := μ.property
  rw [card_oneBoxAddition, YoungDiagram.card_addRows,
    show YoungDiagram.removeRows μ.val = ∅ by simp [YoungDiagram.removeRows, hcard]]
  simp

/-- Two distinct diagrams of the same size have exactly as many common one-box extensions as
they have common one-box contractions: the union and the intersection gain and lose the same
number of cells. -/
theorem card_filter_common_addition_eq_card_filter_common_removal {n : ℕ}
    (ν ν' : YoungDiagramOfSize (n + 1)) (hne : ν ≠ ν') :
    (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
        ν.val ≤ lam.val ∧ ν'.val ≤ lam.val).card =
      (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
        xi.val ≤ ν.val ∧ xi.val ≤ ν'.val).card := by
  have hν : ν.val.cells.card = n + 1 := ν.property
  have hν' : ν'.val.cells.card = n + 1 := ν'.property
  have hcells : ν.val.cells ≠ ν'.val.cells := fun h => hne (Subtype.ext (YoungDiagram.ext h))
  have hunion : (ν.val ⊔ ν'.val).cells.card + (ν.val ⊓ ν'.val).cells.card = 2 * n + 2 := by
    rw [YoungDiagram.cells_sup, YoungDiagram.cells_inf, Finset.card_union_add_card_inter, hν, hν']
    omega
  have hsub : ν.val.cells ⊆ (ν.val ⊔ ν'.val).cells :=
    YoungDiagram.cells_subset_iff.mpr le_sup_left
  have hsub' : ν'.val.cells ⊆ (ν.val ⊔ ν'.val).cells :=
    YoungDiagram.cells_subset_iff.mpr le_sup_right
  have hsup : n + 2 ≤ (ν.val ⊔ ν'.val).cells.card := by
    rcases Nat.lt_or_ge (n + 1) (ν.val ⊔ ν'.val).cells.card with h | h
    · omega
    · refine absurd ?_ hcells
      rw [Finset.eq_of_subset_of_card_le hsub (by omega),
        Finset.eq_of_subset_of_card_le hsub' (by omega)]
  have hinf : (ν.val ⊓ ν'.val).cells.card ≤ n := by omega
  by_cases hcase : (ν.val ⊔ ν'.val).cells.card = n + 2
  · rw [show (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
        ν.val ≤ lam.val ∧ ν'.val ≤ lam.val) = {⟨ν.val ⊔ ν'.val, hcase⟩} from ?_,
      show (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
        xi.val ≤ ν.val ∧ xi.val ≤ ν'.val) =
          {⟨ν.val ⊓ ν'.val, show (ν.val ⊓ ν'.val).cells.card = n by omega⟩} from ?_]
    · simp
    · refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp, ?_⟩
      intro xi hxi
      rw [Finset.mem_filter] at hxi
      have hxicard : xi.val.cells.card = n := xi.property
      exact Subtype.ext (YoungDiagram.ext (Finset.eq_of_subset_of_card_le
        (YoungDiagram.cells_subset_iff.mpr (le_inf hxi.2.1 hxi.2.2))
        (show (ν.val ⊓ ν'.val).cells.card ≤ xi.val.cells.card by omega)))
    · refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp, ?_⟩
      intro lam hlam
      rw [Finset.mem_filter] at hlam
      have hlamcard : lam.val.cells.card = n + 2 := lam.property
      exact Subtype.ext (YoungDiagram.ext (Finset.eq_of_subset_of_card_le
        (YoungDiagram.cells_subset_iff.mpr (sup_le hlam.2.1 hlam.2.2))
        (show lam.val.cells.card ≤ (ν.val ⊔ ν'.val).cells.card by omega))).symm
  · have hlamempty : (Finset.univ.filter fun lam : YoungDiagramOfSize (n + 2) =>
        ν.val ≤ lam.val ∧ ν'.val ≤ lam.val) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      rintro lam _ ⟨h₁, h₂⟩
      have hlamcard : lam.val.cells.card = n + 2 := lam.property
      have := Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr (sup_le h₁ h₂))
      omega
    have hxiempty : (Finset.univ.filter fun xi : YoungDiagramOfSize n =>
        xi.val ≤ ν.val ∧ xi.val ≤ ν'.val) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      rintro xi _ ⟨h₁, h₂⟩
      have hxicard : xi.val.cells.card = n := xi.property
      have := Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr (le_inf h₁ h₂))
      omega
    rw [hlamempty, hxiempty]
    simp
