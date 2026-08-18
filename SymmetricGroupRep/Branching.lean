import SymmetricGroupRep.Induction
import SymmetricGroupRep.Classification
import SymmetricGroupRep.Tableaux
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Data.Fin.Embedding
import Mathlib.GroupTheory.Perm.ViaEmbedding

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- The standard inclusion `S_m → S_n`, which fixes every point outside `Fin m`. -/
noncomputable def SymmetricGroup.inclusionOfLE {m n : ℕ} (h : m ≤ n) :
    SymmetricGroup m →* SymmetricGroup n :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h)

/-- The standard inclusion `S_m → S_n` is injective. -/
theorem SymmetricGroup.inclusionOfLE_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (SymmetricGroup.inclusionOfLE h) := by
  simpa [SymmetricGroup.inclusionOfLE] using
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb h))

/-- The standard inclusion acts on the initial block by the original permutation. -/
@[simp]
theorem SymmetricGroup.inclusionOfLE_apply_castLE {m n : ℕ} (h : m ≤ n)
    (σ : SymmetricGroup m) (i : Fin m) :
    SymmetricGroup.inclusionOfLE h σ (Fin.castLE h i) = Fin.castLE h (σ i) := by
  exact Equiv.Perm.viaEmbedding_apply σ (Fin.castLEEmb h) i

/-- The standard inclusion fixes points outside the embedded initial block. -/
@[simp]
theorem SymmetricGroup.inclusionOfLE_apply_of_notMem {m n : ℕ} (h : m ≤ n)
    (σ : SymmetricGroup m) (j : Fin n) (hj : j ∉ Set.range (Fin.castLEEmb h)) :
    SymmetricGroup.inclusionOfLE h σ j = j := by
  exact Equiv.Perm.viaEmbedding_apply_of_notMem σ (Fin.castLEEmb h) j hj

/-- The standard inclusion fixes every point whose index is at least `m`. -/
@[simp]
theorem SymmetricGroup.inclusionOfLE_apply_of_le {m n : ℕ} (h : m ≤ n)
    (σ : SymmetricGroup m) (j : Fin n) (hj : m ≤ j.1) :
    SymmetricGroup.inclusionOfLE h σ j = j := by
  apply SymmetricGroup.inclusionOfLE_apply_of_notMem
  change j ∉ Set.range (Fin.castLE h)
  rw [Fin.range_castLE]
  exact not_lt_of_ge hj

/-- The standard inclusion `S_n → S_(n+1)`, which fixes the final point. -/
noncomputable def SymmetricGroup.inclusion (n : ℕ) :
    SymmetricGroup n →* SymmetricGroup (n + 1) :=
  SymmetricGroup.inclusionOfLE (Nat.le_succ n)

/-- The adjacent inclusion is the corresponding specialization of `inclusionOfLE`. -/
theorem SymmetricGroup.inclusionOfLE_succ (n : ℕ) :
    SymmetricGroup.inclusionOfLE (Nat.le_succ n) = SymmetricGroup.inclusion n :=
  rfl

/-- The adjacent inclusion fixes the largest label. -/
@[simp]
theorem SymmetricGroup.inclusion_apply_last (n : ℕ) (g : SymmetricGroup n) :
    SymmetricGroup.inclusion n g (Fin.last n) = Fin.last n :=
  SymmetricGroup.inclusionOfLE_apply_of_le (Nat.le_succ n) g (Fin.last n) (Fin.val_last n).ge

/-- The adjacent inclusion acts by `g` on every other label. -/
@[simp]
theorem SymmetricGroup.inclusion_apply_castSucc (n : ℕ) (g : SymmetricGroup n) (i : Fin n) :
    SymmetricGroup.inclusion n g i.castSucc = (g i).castSucc :=
  SymmetricGroup.inclusionOfLE_apply_castLE (Nat.le_succ n) g i

/-- The adjacent inclusion preserves signs. -/
@[simp]
theorem SymmetricGroup.sign_inclusion (n : ℕ) (g : SymmetricGroup n) :
    Equiv.Perm.sign (SymmetricGroup.inclusion n g) = Equiv.Perm.sign g := by
  -- `Equiv.Perm.viaEmbedding` is `extendDomain` along the classically decidable range predicate,
  -- so `sign_extendDomain` applies only once that instance is the one in scope.
  letI : DecidablePred fun j : Fin (n + 1) =>
      j ∈ Set.range (Fin.castLEEmb (Nat.le_succ n)).toFun := fun j => Classical.propDecidable _
  exact Equiv.Perm.sign_extendDomain g
    (Equiv.ofInjective (Fin.castLEEmb (Nat.le_succ n)).toFun (Fin.castLEEmb (Nat.le_succ n)).inj')

/-- A permutation of `Fin (n + 1)` fixing the largest label comes from `S_n`. -/
theorem SymmetricGroup.exists_inclusion_of_apply_last {n : ℕ} {π : SymmetricGroup (n + 1)}
    (h : π (Fin.last n) = Fin.last n) :
    ∃ g : SymmetricGroup n, SymmetricGroup.inclusion n g = π := by
  have hne : ∀ σ : SymmetricGroup (n + 1), σ (Fin.last n) = Fin.last n →
      ∀ i : Fin n, σ i.castSucc ≠ Fin.last n := fun σ hσ i hi =>
    (Fin.castSucc_lt_last i).ne (σ.injective (hi.trans hσ.symm))
  have hinv : π⁻¹ (Fin.last n) = Fin.last n := by
    conv_lhs => rw [← h]
    simp
  refine ⟨⟨fun i => (π i.castSucc).castPred (hne π h i),
    fun i => (π⁻¹ i.castSucc).castPred (hne π⁻¹ hinv i), fun i => ?_, fun i => ?_⟩, ?_⟩
  · apply Fin.castSucc_injective
    rw [Fin.castSucc_castPred, Fin.castSucc_castPred]
    simp
  · apply Fin.castSucc_injective
    rw [Fin.castSucc_castPred, Fin.castSucc_castPred]
    simp
  · refine Equiv.ext fun j => ?_
    rcases eq_or_ne j (Fin.last n) with rfl | hj
    · rw [SymmetricGroup.inclusion_apply_last, h]
    · have hj' : (j.castPred hj).castSucc = j := Fin.castSucc_castPred j hj
      calc SymmetricGroup.inclusion n _ j
          = SymmetricGroup.inclusion n _ (j.castPred hj).castSucc := by rw [hj']
        _ = ((π (j.castPred hj).castSucc).castPred (hne π h (j.castPred hj))).castSucc :=
            SymmetricGroup.inclusion_apply_castSucc _ _ _
        _ = π j := by rw [Fin.castSucc_castPred, hj']

/-- Restriction from representations of `S_(n+1)` to representations of `S_n`. -/
noncomputable abbrev SymmetricGroupRepresentation.restriction (n : ℕ) :
    SymmetricGroupRepresentation (n + 1) ⥤ SymmetricGroupRepresentation n :=
  Action.res (FGModuleCat ℂ) (SymmetricGroup.inclusion n)

/-- Induction from representations of `S_n` to representations of `S_(n+1)`. -/
noncomputable abbrev SymmetricGroupRepresentation.induction (n : ℕ) :
    SymmetricGroupRepresentation n ⥤ SymmetricGroupRepresentation (n + 1) :=
  FDRep.indFunctor ℂ (SymmetricGroup.inclusion n)

/-- The adjacent inclusion leaves the row of the largest label untouched. -/
@[simp]
theorem Tabloid.rowOf_last_smul {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (g : SymmetricGroup n) (T : Tabloid μ) :
    ((SymmetricGroup.inclusion n g) • T).rowOf (Fin.last n) = T.rowOf (Fin.last n) := by
  rw [Tabloid.smul_rowOf, ← map_inv, SymmetricGroup.inclusion_apply_last]

namespace OneBoxRemoval

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}

/-- Removing the corner cell shortens exactly the row that cell sits in. -/
theorem rowLen_removal (ν : OneBoxRemoval μ) (row : ℕ) :
    μ.val.rowLen row = ν.val.val.rowLen row + (if row = (cell ν).1 then 1 else 0) := by
  classical
  have hrow : ν.val.val.row row = (μ.val.row row).erase (cell ν) := by
    simp only [YoungDiagram.row, cells_eq_erase ν, Finset.filter_erase]
  rw [YoungDiagram.rowLen_eq_card, YoungDiagram.rowLen_eq_card, hrow]
  by_cases hc : row = (cell ν).1
  · have hmem : cell ν ∈ μ.val.row row :=
      YoungDiagram.mem_row_iff.mpr ⟨cell_mem ν, hc.symm⟩
    have hpos := Finset.card_pos.mpr ⟨cell ν, hmem⟩
    rw [if_pos hc, Finset.card_erase_of_mem hmem]
    omega
  · rw [if_neg hc, add_zero, Finset.erase_eq_of_notMem fun hmem =>
      hc (YoungDiagram.mem_row_iff.mp hmem).2.symm]

/-- Once the largest label is deleted from the corner row, every remaining label still sits in a
nonempty row of the smaller diagram. -/
theorem rowLen_pos_restrict (ν : OneBoxRemoval μ) (T : Tabloid μ)
    (h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1) (i : Fin n) :
    0 < ν.val.val.rowLen (T.rowOf i.castSucc) := by
  have hμ := T.row_nonempty i.castSucc
  have hsplit := rowLen_removal ν (T.rowOf i.castSucc)
  by_cases hc : (T.rowOf i.castSucc : ℕ) = (cell ν).1
  · have hlt : 1 < (Finset.univ.filter fun j : Fin (n + 1) =>
        (T.rowOf j : ℕ) = (T.rowOf i.castSucc : ℕ)).card :=
      Finset.one_lt_card.mpr ⟨i.castSucc, by simp, Fin.last n, by simp [h, hc],
        (Fin.castSucc_lt_last i).ne⟩
    rw [T.content] at hlt
    rw [if_pos hc] at hsplit
    omega
  · rw [if_neg hc] at hsplit
    omega

/-- Row indices of the smaller diagram are labels of the smaller symmetric group. -/
theorem rowOf_castSucc_lt (ν : OneBoxRemoval μ) (T : Tabloid μ)
    (h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1) (i : Fin n) :
    (T.rowOf i.castSucc : ℕ) < n := by
  have hmem : ((T.rowOf i.castSucc : ℕ), 0) ∈ ν.val.val.cells :=
    (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_rowLen.mpr
      (rowLen_pos_restrict ν T h i))
  simpa [ν.val.property] using ν.val.val.cell_fst_lt_card hmem

/-- Deleting the largest label from the corner row leaves each row with the number of labels the
smaller diagram prescribes. -/
theorem card_restrict (ν : OneBoxRemoval μ) (T : Tabloid μ)
    (h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1) (row : ℕ) :
    (Finset.univ.filter fun i : Fin n => (T.rowOf i.castSucc : ℕ) = row).card
      = ν.val.val.rowLen row := by
  classical
  have hset : (Finset.univ.filter fun i : Fin n => (T.rowOf i.castSucc : ℕ) = row).image
      Fin.castSucc = (Finset.univ.filter fun j : Fin (n + 1) =>
        (T.rowOf j : ℕ) = row).erase (Fin.last n) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Fin.castSucc_lt_last i).ne, hi⟩
    · rintro ⟨hne, hj⟩
      exact ⟨j.castPred hne, by rwa [Fin.castSucc_castPred], Fin.castSucc_castPred j hne⟩
  rw [← Finset.card_image_of_injective _ (Fin.castSucc_injective n), hset]
  have hsplit := rowLen_removal ν row
  by_cases hc : row = (cell ν).1
  · have hmem : Fin.last n ∈ Finset.univ.filter fun j : Fin (n + 1) => (T.rowOf j : ℕ) = row :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h, hc]⟩
    have hpos := Finset.card_pos.mpr ⟨Fin.last n, hmem⟩
    rw [Finset.card_erase_of_mem hmem, T.content row]
    rw [if_pos hc] at hsplit
    rw [T.content row] at hpos
    omega
  · rw [Finset.erase_eq_of_notMem fun hmem =>
      hc (by rw [← (Finset.mem_filter.mp hmem).2, h]), T.content row]
    rw [if_neg hc] at hsplit
    omega

/-- The tabloid of the smaller diagram obtained by deleting the largest label, which the hypothesis
places in the row of the removed corner. -/
def restrictTabloid (ν : OneBoxRemoval μ) (T : Tabloid μ)
    (h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1) : Tabloid ν.val where
  rowOf i := ⟨T.rowOf i.castSucc, rowOf_castSucc_lt ν T h i⟩
  row_nonempty i := rowLen_pos_restrict ν T h i
  content row := card_restrict ν T h row

@[simp]
theorem restrictTabloid_rowOf (ν : OneBoxRemoval μ) (T : Tabloid μ)
    (h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1) (i : Fin n) :
    ((restrictTabloid ν T h).rowOf i : ℕ) = (T.rowOf i.castSucc : ℕ) :=
  rfl

/-- Restricting a tabloid commutes with the action of the smaller symmetric group. -/
theorem restrictTabloid_smul (ν : OneBoxRemoval μ) (T : Tabloid μ) (g : SymmetricGroup n)
    (h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1) :
    restrictTabloid ν ((SymmetricGroup.inclusion n g) • T)
        (by rw [Tabloid.rowOf_last_smul]; exact h) = g • restrictTabloid ν T h := by
  refine Tabloid.ext (funext fun i => Fin.ext ?_)
  rw [restrictTabloid_rowOf, Tabloid.smul_rowOf, Tabloid.smul_rowOf, restrictTabloid_rowOf,
    ← map_inv, SymmetricGroup.inclusion_apply_castSucc]

/-- Sagan's map `θ` on the tabloid bases: it keeps the tabloids carrying the largest label in the
row of the removed corner, and forgets that label.

See Sagan, *The Symmetric Group*, 2nd ed., proof of Theorem 2.8.3. -/
noncomputable def rowProjectionMap (ν : OneBoxRemoval μ) :
    (MonoidAlgebra ℂ (Tabloid μ)) →ₗ[ℂ] (MonoidAlgebra ℂ (Tabloid ν.val)) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap.comp <|
    (Finsupp.lsum ℂ fun T => if h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1
      then Finsupp.lsingle (restrictTabloid ν T h) else 0).comp
        (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem rowProjectionMap_single (ν : OneBoxRemoval μ) (T : Tabloid μ) (c : ℂ) :
    rowProjectionMap ν (MonoidAlgebra.single T c)
      = if h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1
        then MonoidAlgebra.single (restrictTabloid ν T h) c else 0 := by
  apply MonoidAlgebra.coeff_injective
  simp only [rowProjectionMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change ((Finsupp.lsum ℂ) (fun T => if h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1
    then Finsupp.lsingle (restrictTabloid ν T h) else 0)) (Finsupp.single T c) = _
  rw [Finsupp.lsum_single]
  by_cases h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

theorem rowProjectionMap_ofMulAction (ν : OneBoxRemoval μ) (g : SymmetricGroup n)
    (v : MonoidAlgebra ℂ (Tabloid μ)) :
    rowProjectionMap ν (Representation.ofMulAction ℂ (SymmetricGroup (n + 1)) (Tabloid μ)
        (SymmetricGroup.inclusion n g) v)
      = Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid ν.val) g
        (rowProjectionMap ν v) := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single T c =>
      rw [Representation.ofMulAction_single, rowProjectionMap_single, rowProjectionMap_single]
      by_cases h : (T.rowOf (Fin.last n) : ℕ) = (cell ν).1
      · rw [dif_pos h, dif_pos (show (((SymmetricGroup.inclusion n g) • T).rowOf (Fin.last n) : ℕ)
          = (cell ν).1 by rw [Tabloid.rowOf_last_smul]; exact h), restrictTabloid_smul,
          Representation.ofMulAction_single]
      · rw [dif_neg h, dif_neg (show ¬(((SymmetricGroup.inclusion n g) • T).rowOf (Fin.last n) : ℕ)
          = (cell ν).1 by rwa [Tabloid.rowOf_last_smul]), map_zero]

/-- Some tableau of shape `μ` carries the largest label in the corner cell that `ν` deletes. -/
theorem exists_tableau_last_at_cell (ν : OneBoxRemoval μ) :
    ∃ t : YoungTableau μ, t ⟨cell ν, cell_mem ν⟩ = Fin.last n := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  exact ⟨Equiv.swap (t ⟨cell ν, cell_mem ν⟩) (Fin.last n) • t, Equiv.swap_apply_left _ _⟩

theorem apply_ne_last (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) (d : ↥ν.val.val.cells) :
    t ⟨d.1, cells_subset ν d.2⟩ ≠ Fin.last n := fun h => by
  have hcell : (d : ℕ × ℕ) = cell ν := congrArg Subtype.val (t.injective (h.trans ht.symm))
  exact cell_notMem ν (hcell ▸ d.2)

theorem symm_castSucc_mem (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) (i : Fin n) :
    (t.symm i.castSucc).1 ∈ ν.val.val.cells := by
  by_contra hmem
  refine (Fin.castSucc_lt_last i).ne ?_
  calc i.castSucc = t (t.symm i.castSucc) := (t.apply_symm_apply _).symm
    _ = t ⟨cell ν, cell_mem ν⟩ :=
        congrArg t (Subtype.ext (eq_cell_of_notMem ν (t.symm i.castSucc).2 hmem))
    _ = Fin.last n := ht

/-- The tableau of the smaller diagram obtained by deleting the corner cell, which the hypothesis
fills with the largest label. -/
def restrictTableau (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) : YoungTableau ν.val where
  toFun d := (t ⟨d.1, cells_subset ν d.2⟩).castPred (apply_ne_last ν t ht d)
  invFun i := ⟨(t.symm i.castSucc).1, symm_castSucc_mem ν t ht i⟩
  left_inv d := by
    apply Subtype.ext
    show ((t.symm ((t ⟨d.1, cells_subset ν d.2⟩).castPred
      (apply_ne_last ν t ht d)).castSucc) : ℕ × ℕ) = (d : ℕ × ℕ)
    rw [Fin.castSucc_castPred]
    exact congrArg Subtype.val (t.symm_apply_apply _)
  right_inv i := by
    apply Fin.castSucc_injective
    rw [Fin.castSucc_castPred]
    exact congrArg t (Subtype.ext rfl) |>.trans (t.apply_symm_apply i.castSucc)

@[simp]
theorem restrictTableau_column (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) (i : Fin n) :
    (restrictTableau ν t ht).column i = t.column i.castSucc :=
  rfl

/-- The largest label sits in the row of the removed corner. -/
theorem tabloid_rowOf_last (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) :
    (t.tabloid.rowOf (Fin.last n) : ℕ) = (cell ν).1 := by
  show (t.symm (Fin.last n)).1.1 = (cell ν).1
  rw [t.symm_apply_eq.mpr ht.symm]

theorem restrictTableau_tabloid (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) :
    (restrictTableau ν t ht).tabloid = restrictTabloid ν t.tabloid (tabloid_rowOf_last ν t ht) :=
  Tabloid.ext (funext fun _ => Fin.ext rfl)

/-- Column-preserving relabellings of `μ` that come from `S_n` are exactly the column-preserving
relabellings of the restricted tableau. -/
theorem mem_columnGroup_inclusion_iff (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) (g : SymmetricGroup n) :
    SymmetricGroup.inclusion n g ∈ t.columnGroup ↔
      g ∈ (restrictTableau ν t ht).columnGroup := by
  constructor
  · intro hg
    refine YoungTableau.mem_columnGroup.mpr fun i => ?_
    rw [restrictTableau_column, restrictTableau_column]
    have hi := YoungTableau.mem_columnGroup.mp hg i.castSucc
    rwa [SymmetricGroup.inclusion_apply_castSucc] at hi
  · intro hg
    refine YoungTableau.mem_columnGroup.mpr fun j => ?_
    rcases eq_or_ne j (Fin.last n) with rfl | hj
    · rw [SymmetricGroup.inclusion_apply_last]
    · have hi := YoungTableau.mem_columnGroup.mp hg (j.castPred hj)
      rw [restrictTableau_column, restrictTableau_column] at hi
      rw [← Fin.castSucc_castPred j hj, SymmetricGroup.inclusion_apply_castSucc]
      exact hi

/-- A column-preserving relabelling leaves the largest label in the corner row exactly when it
fixes that label: the corner cell is the only cell in both its row and its column. -/
theorem row_inv_last_iff (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) {π : SymmetricGroup (n + 1)}
    (hπ : π ∈ t.columnGroup) :
    t.row (π⁻¹ (Fin.last n)) = (cell ν).1 ↔ π (Fin.last n) = Fin.last n := by
  have hsymm : t.symm (Fin.last n) = ⟨cell ν, cell_mem ν⟩ := t.symm_apply_eq.mpr ht.symm
  have hrow : t.row (Fin.last n) = (cell ν).1 := by
    show (t.symm (Fin.last n)).1.1 = (cell ν).1
    rw [hsymm]
  have happly : ∀ j, π (π⁻¹ j) = j := fun j => by simp
  constructor
  · intro hr
    have hcolumn : t.column (π⁻¹ (Fin.last n)) = t.column (Fin.last n) := by
      have hc := YoungTableau.mem_columnGroup.mp hπ (π⁻¹ (Fin.last n))
      rw [happly] at hc
      exact hc.symm
    have hfix : π⁻¹ (Fin.last n) = Fin.last n :=
      t.symm.injective (Subtype.ext (Prod.ext (hr.trans hrow.symm) hcolumn))
    calc π (Fin.last n) = π (π⁻¹ (Fin.last n)) := by rw [hfix]
      _ = Fin.last n := happly _
  · intro hfix
    have hinv : π⁻¹ (Fin.last n) = Fin.last n := by
      conv_lhs => rw [← hfix]
      simp
    rw [hinv, hrow]

/-- Sagan's identity (2.8): the row projection carries the polytabloid of a tableau whose largest
label fills the removed corner to the polytabloid of the restricted tableau. -/
theorem rowProjectionMap_polytabloid (ν : OneBoxRemoval μ) (t : YoungTableau μ)
    (ht : t ⟨cell ν, cell_mem ν⟩ = Fin.last n) :
    rowProjectionMap ν (YoungTableau.polytabloid t)
      = YoungTableau.polytabloid (restrictTableau ν t ht) := by
  classical
  let incl : (restrictTableau ν t ht).columnGroup → t.columnGroup := fun g =>
    ⟨SymmetricGroup.inclusion n g, (mem_columnGroup_inclusion_iff ν t ht g).mpr g.2⟩
  have hincl : Function.Injective incl := fun g₁ g₂ hg => Subtype.ext
    (SymmetricGroup.inclusionOfLE_injective (Nat.le_succ n) (congrArg Subtype.val hg))
  have houtside : ∀ σ ∈ (Finset.univ : Finset t.columnGroup), σ ∉ Finset.univ.image incl →
      rowProjectionMap ν (MonoidAlgebra.single ((σ : SymmetricGroup (n + 1)) • t.tabloid) 1) = 0 := by
    intro σ _ hσ
    rw [rowProjectionMap_single, dif_neg]
    intro hrow
    rw [Tabloid.smul_rowOf, YoungTableau.tabloid_rowOf] at hrow
    obtain ⟨g, hg⟩ := SymmetricGroup.exists_inclusion_of_apply_last
      ((row_inv_last_iff ν t ht σ.2).mp hrow)
    exact hσ (Finset.mem_image.mpr ⟨⟨g, (mem_columnGroup_inclusion_iff ν t ht g).mp (hg ▸ σ.2)⟩,
      Finset.mem_univ _, Subtype.ext hg⟩)
  calc rowProjectionMap ν (YoungTableau.polytabloid t)
      = ∑ σ : t.columnGroup, ((Equiv.Perm.sign (σ : SymmetricGroup (n + 1)) : ℤ) : ℂ) •
          rowProjectionMap ν (MonoidAlgebra.single ((σ : SymmetricGroup (n + 1)) • t.tabloid) 1) := by
        rw [YoungTableau.polytabloid, map_sum]
        exact Finset.sum_congr rfl fun σ _ => map_smul _ _ _
    _ = ∑ σ ∈ Finset.univ.image incl, ((Equiv.Perm.sign (σ : SymmetricGroup (n + 1)) : ℤ) : ℂ) •
          rowProjectionMap ν (MonoidAlgebra.single ((σ : SymmetricGroup (n + 1)) • t.tabloid) 1) :=
        (Finset.sum_subset (Finset.subset_univ _) fun σ hσ hσ' => by
          rw [houtside σ hσ hσ', smul_zero]).symm
    _ = ∑ g : (restrictTableau ν t ht).columnGroup,
          ((Equiv.Perm.sign (SymmetricGroup.inclusion n (g : SymmetricGroup n)) : ℤ) : ℂ) •
            rowProjectionMap ν (MonoidAlgebra.single
              ((SymmetricGroup.inclusion n (g : SymmetricGroup n)) • t.tabloid) 1) :=
        Finset.sum_image fun x _ y _ hxy => hincl hxy
    _ = YoungTableau.polytabloid (restrictTableau ν t ht) := by
        have hlast : ∀ g : SymmetricGroup n,
            (((SymmetricGroup.inclusion n g) • t.tabloid).rowOf (Fin.last n) : ℕ) = (cell ν).1 := by
          intro g
          rw [Tabloid.rowOf_last_smul]
          exact tabloid_rowOf_last ν t ht
        rw [YoungTableau.polytabloid]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [rowProjectionMap_single, dif_pos (hlast g),
          restrictTabloid_smul ν t.tabloid g (tabloid_rowOf_last ν t ht),
          ← restrictTableau_tabloid ν t ht, SymmetricGroup.sign_inclusion]

/-- The row projection as a morphism of `S_n`-representations. -/
noncomputable def rowProjection (ν : OneBoxRemoval μ) :
    (SymmetricGroupRepresentation.restriction n).obj (youngPermutationModule μ) ⟶
      youngPermutationModule ν.val :=
  Action.Hom.mk (FGModuleCat.ofHom (rowProjectionMap ν)) (by
    intro g
    apply FGModuleCat.hom_ext
    ext v
    exact rowProjectionMap_ofMulAction ν g v)

/-- Every one-box removal really occurs in the restriction: the row projection, restricted to the
Specht module of `μ` and split off the Specht submodule of `M^ν`, is a nonzero morphism
`Res S^μ ⟶ S^ν`. -/
theorem finrank_hom_res_spechtModule_pos (ν : OneBoxRemoval μ) :
    0 < Module.finrank ℂ ((SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ⟶
      spechtModule ν.val) := by
  obtain ⟨t, ht⟩ := exists_tableau_last_at_cell ν
  obtain ⟨r, hr⟩ := Subrepresentation.exists_retraction_toFDRepHom
    (youngPermutationModule ν.val) (spechtSubrepresentation ν.val)
  have hmem : ∀ s : YoungTableau ν.val, YoungTableau.polytabloid s ∈
      (spechtSubrepresentation ν.val).toSubmodule := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hsplit : ∀ s : YoungTableau ν.val,
      r.hom.hom (YoungTableau.polytabloid s) = ⟨YoungTableau.polytabloid s, hmem s⟩ :=
    fun s => congrArg (fun f : spechtModule ν.val ⟶ spechtModule ν.val =>
      f.hom.hom ⟨YoungTableau.polytabloid s, hmem s⟩) hr
  have hne : (SymmetricGroupRepresentation.restriction n).map
        (Subrepresentation.toFDRepHom (youngPermutationModule μ) (spechtSubrepresentation μ)) ≫
      rowProjection ν ≫ r ≠ 0 := by
    intro hzero
    have hvalue := congrArg (fun f : (SymmetricGroupRepresentation.restriction n).obj
        (spechtModule μ) ⟶ spechtModule ν.val =>
      f.hom.hom ⟨YoungTableau.polytabloid t, Submodule.subset_span ⟨t, rfl⟩⟩) hzero
    have hzero' : r.hom.hom (rowProjectionMap ν (YoungTableau.polytabloid t)) = 0 := by
      change r.hom.hom (rowProjectionMap ν (YoungTableau.polytabloid t)) = 0 at hvalue
      exact hvalue
    rw [rowProjectionMap_polytabloid ν t ht, hsplit] at hzero'
    exact YoungTableau.polytabloid_ne_zero (restrictTableau ν t ht)
      (by
        have hzero'' := congrArg Subtype.val hzero'
        change YoungTableau.polytabloid (restrictTableau ν t ht) = 0 at hzero''
        exact hzero'')
  haveI : Nontrivial ((SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ⟶
    spechtModule ν.val) := nontrivial_of_ne _ _ hne
  exact Module.finrank_pos

end OneBoxRemoval

/-- A Specht module is nonzero: it contains the polytabloid of any tableau. -/
theorem finrank_spechtModule_pos {n : ℕ} (μ : YoungDiagramOfSize n) :
    0 < Module.finrank ℂ (spechtModule μ) := by
  haveI : Nontrivial (spechtModule μ : Type) :=
    Submodule.nontrivial_iff_ne_bot.mpr (spechtSubrepresentation_ne_bot μ)
  exact Module.finrank_pos

open scoped Classical in
/-- Counting `S^λ` inside the biproduct of the Specht modules selected by a predicate: it occurs
once if the predicate selects `λ`, and not at all otherwise. -/
theorem finrank_hom_spechtModule_biproduct {m : ℕ} (P : YoungDiagramOfSize m → Prop)
    (lam : YoungDiagramOfSize m) :
    Module.finrank ℂ (spechtModule lam ⟶
        ⨁ fun ν : {ν : YoungDiagramOfSize m // P ν} => spechtModule ν.val) =
      if P lam then 1 else 0 := by
  letI : Fintype {ν : YoungDiagramOfSize m // P ν} := Fintype.ofFinite _
  have hterm : ∀ ν : {ν : YoungDiagramOfSize m // P ν},
      Module.finrank ℂ (spechtModule lam ⟶ spechtModule ν.val) =
        if lam = ν.val then 1 else 0 := by
    intro ν
    haveI := spechtModule_irreducible lam
    haveI := spechtModule_irreducible ν.val
    rw [FDRep.finrank_hom_simple_simple]
    exact if_congr (spechtModule_iso_iff_eq lam ν.val) rfl rfl
  rw [(FDRep.homBiproductLinearEquiv _ _).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_congr rfl fun ν _ => hterm ν]
  by_cases hP : P lam
  · rw [if_pos hP, Finset.sum_eq_single (⟨lam, hP⟩ : {ν : YoungDiagramOfSize m // P ν})
      (fun ν _ hne => if_neg fun h => hne (Subtype.ext h.symm))
      (fun hmem => absurd (Finset.mem_univ _) hmem), if_pos rfl]
  · rw [if_neg hP, Finset.sum_eq_zero]
    intro ν _
    exact if_neg fun h => hP (by rw [h]; exact ν.2)

/-- Restricting `S^λ` from `S_(n+1)` to `S_n` gives the multiplicity-free direct sum of
the Specht modules obtained by removing one box from `λ`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.8.3. -/
theorem spechtModule_branching {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
  Nonempty ((SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val) := by
  classical
  refine FDRep.nonempty_iso_of_finrank_hom_eq spechtModule spechtModule_irreducible
    (fun α β h => (spechtModule_iso_iff_eq α β).mp h)
    (fun T hT => @exists_iso_spechtModule n T hT) fun lam => ?_
  -- Each removal occurs at least once, and the dimensions leave room for nothing more.
  have hle : ∀ ξ ∈ (Finset.univ : Finset (YoungDiagramOfSize n)),
      (if ξ ∈ oneBoxRemovals μ then Module.finrank ℂ (spechtModule ξ) else 0) ≤
        Module.finrank ℂ (spechtModule ξ ⟶
            (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ)) *
          Module.finrank ℂ (spechtModule ξ) := by
    intro ξ _
    by_cases hξ : ξ ∈ oneBoxRemovals μ
    · rw [if_pos hξ]
      refine Nat.le_mul_of_pos_left _ ?_
      rw [FDRep.finrank_hom_symm]
      exact OneBoxRemoval.finrank_hom_res_spechtModule_pos
        ⟨ξ, show IsOneBoxRemoval ξ μ from mem_oneBoxRemovals.mp hξ⟩
    · rw [if_neg hξ]
      exact Nat.zero_le _
  have htotal : ∑ ξ : YoungDiagramOfSize n,
      (if ξ ∈ oneBoxRemovals μ then Module.finrank ℂ (spechtModule ξ) else 0) =
        ∑ ξ : YoungDiagramOfSize n, Module.finrank ℂ (spechtModule ξ ⟶
            (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ)) *
          Module.finrank ℂ (spechtModule ξ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter,
      FDRep.finrank_eq_sum_finrank_hom_mul spechtModule spechtModule_irreducible
        (fun α β h => (spechtModule_iso_iff_eq α β).mp h)
        (fun T hT => @exists_iso_spechtModule n T hT)]
    exact (finrank_spechtModule_eq_sum_oneBoxRemovals μ).symm
  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp htotal lam (Finset.mem_univ lam)
  rw [finrank_hom_spechtModule_biproduct (fun ξ => IsOneBoxRemoval ξ μ) lam]
  by_cases hlam : lam ∈ oneBoxRemovals μ
  · rw [if_pos hlam] at hpoint
    rw [if_pos (show IsOneBoxRemoval lam μ from mem_oneBoxRemovals.mp hlam)]
    refine (Nat.eq_of_mul_eq_mul_right (finrank_spechtModule_pos lam) ?_).symm
    rw [one_mul]
    exact hpoint
  · rw [if_neg hlam] at hpoint
    rw [if_neg (show ¬IsOneBoxRemoval lam μ from fun h => hlam (mem_oneBoxRemovals.mpr h))]
    exact (Nat.mul_eq_zero.mp hpoint.symm).resolve_right (finrank_spechtModule_pos lam).ne'

/-- Inducing `S^μ` from `S_n` to `S_(n+1)` gives the multiplicity-free direct sum of
the Specht modules obtained by adding one box to `μ`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.8.3. -/
theorem spechtModule_induction_branching {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.induction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxAddition μ => spechtModule ν.val) := by
  classical
  refine FDRep.nonempty_iso_of_finrank_hom_eq spechtModule spechtModule_irreducible
    (fun α β h => (spechtModule_iso_iff_eq α β).mp h)
    (fun T hT => @exists_iso_spechtModule (n + 1) T hT) fun lam => ?_
  -- Frobenius reciprocity turns the multiplicity of `S^λ` in the induced module into the
  -- multiplicity of `S^μ` in the restricted one, which the branching rule already counts.
  rw [FDRep.finrank_hom_symm, FDRep.indFunctor_obj,
    (FDRep.indResHomEquiv (SymmetricGroup.inclusion n) (spechtModule μ)
      (spechtModule lam)).finrank_eq,
    (FDRep.homCongrTarget (spechtModule μ)
      (Classical.choice (spechtModule_branching lam))).finrank_eq,
    finrank_hom_spechtModule_biproduct (fun ν => IsOneBoxRemoval ν lam) μ,
    finrank_hom_spechtModule_biproduct (fun ν => IsOneBoxAddition μ ν) lam]
  rfl

/-- A path of two successive one-box removals from `μ`. -/
abbrev TwoStepRemoval {n : ℕ} (μ : YoungDiagramOfSize (n + 2)) :=
  Σ ν : OneBoxRemoval μ, OneBoxRemoval ν.val

/-- A path of three successive one-box removals from `μ`. -/
abbrev ThreeStepRemoval {n : ℕ} (μ : YoungDiagramOfSize (n + 3)) :=
  Σ ν : OneBoxRemoval μ, TwoStepRemoval ν.val

/-- The endpoint of a two-step path in the Young graph. -/
def TwoStepRemoval.endpoint {n : ℕ} {μ : YoungDiagramOfSize (n + 2)}
    (p : TwoStepRemoval μ) : YoungDiagramOfSize n :=
  p.2.val

/-- Two-step removal paths from `μ` with endpoint `ν`. -/
abbrev TwoStepRemovalTo {n : ℕ} (μ : YoungDiagramOfSize (n + 2))
    (ν : YoungDiagramOfSize n) :=
  { p : TwoStepRemoval μ // p.endpoint = ν }

/-- The multiplicity of `S^ν` after restricting `S^μ` through two adjacent groups. -/
noncomputable def twoStepBranchingMultiplicity {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n) : ℕ :=
  Nat.card (TwoStepRemovalTo μ ν)

/-- The endpoint of a three-step path in the Young graph. -/
def ThreeStepRemoval.endpoint {n : ℕ} {μ : YoungDiagramOfSize (n + 3)}
    (p : ThreeStepRemoval μ) : YoungDiagramOfSize n :=
  p.2.2.val

/-- Three-step removal paths from `μ` with endpoint `ν`. -/
abbrev ThreeStepRemovalTo {n : ℕ} (μ : YoungDiagramOfSize (n + 3))
    (ν : YoungDiagramOfSize n) :=
  { p : ThreeStepRemoval μ // p.endpoint = ν }

/-- The multiplicity of `S^ν` after restricting `S^μ` through three adjacent groups. -/
noncomputable def threeStepBranchingMultiplicity {n : ℕ}
    (μ : YoungDiagramOfSize (n + 3)) (ν : YoungDiagramOfSize n) : ℕ :=
  Nat.card (ThreeStepRemovalTo μ ν)

/-- Restricting a Specht module through two adjacent symmetric groups is indexed by
paths of two one-box removals in the Young graph. -/
theorem spechtModule_branching_twoSteps {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) :
    Nonempty
      ((SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ≅
        ⨁ fun p : TwoStepRemoval μ => spechtModule p.2.val) := by
  let e := Classical.choice (spechtModule_branching μ)
  exact ⟨
    (SymmetricGroupRepresentation.restriction n).mapIso e ≪≫
      (SymmetricGroupRepresentation.restriction n).mapBiproduct
        (fun ν : OneBoxRemoval μ => spechtModule ν.val) ≪≫
      biproduct.mapIso (fun ν : OneBoxRemoval μ =>
        Classical.choice (spechtModule_branching ν.val)) ≪≫
      biproductBiproductIso
        (fun ν : OneBoxRemoval μ => OneBoxRemoval ν.val)
        (fun _ ξ => spechtModule ξ.val)⟩

/-- Restricting a Specht module through three adjacent symmetric groups is indexed by
paths of three one-box removals in the Young graph. -/
theorem spechtModule_branching_threeSteps {n : ℕ}
    (μ : YoungDiagramOfSize (n + 3)) :
    Nonempty
      ((SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj
            ((SymmetricGroupRepresentation.restriction (n + 2)).obj (spechtModule μ))) ≅
        ⨁ fun p : ThreeStepRemoval μ => spechtModule p.2.2.val) := by
  let e := Classical.choice (spechtModule_branching μ)
  let F := SymmetricGroupRepresentation.restriction (n + 1) ⋙
    SymmetricGroupRepresentation.restriction n
  exact ⟨
    F.mapIso e ≪≫
      F.mapBiproduct (fun ν : OneBoxRemoval μ => spechtModule ν.val) ≪≫
      biproduct.mapIso (fun ν : OneBoxRemoval μ =>
        Classical.choice (spechtModule_branching_twoSteps ν.val)) ≪≫
      biproductBiproductIso
        (fun ν : OneBoxRemoval μ => TwoStepRemoval ν.val)
        (fun _ p => spechtModule p.2.val)⟩

/-- Two-step restriction regrouped by endpoint. The copies of `S^ν` are indexed by
the two-step paths from `μ` to `ν`. -/
theorem spechtModule_branching_twoSteps_byEndpoint {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) :
    Nonempty
      ((SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ≅
        ⨁ fun ν : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo μ ν => spechtModule ν) := by
  let e := Classical.choice (spechtModule_branching_twoSteps μ)
  let endpoint := fun p : TwoStepRemoval μ => p.2.val
  let fibers := fun ν : YoungDiagramOfSize n => { p : TwoStepRemoval μ // endpoint p = ν }
  let reindex :
      (⨁ fun p : TwoStepRemoval μ => spechtModule p.2.val) ≅
        ⨁ fun q : Σ ν, fibers ν => spechtModule q.1 :=
    biproduct.reindex (Equiv.sigmaFiberEquiv endpoint).symm
      (fun q : Σ ν, fibers ν => spechtModule q.1)
  exact ⟨e ≪≫ reindex ≪≫
    (biproductBiproductIso fibers (fun ν _ => spechtModule ν)).symm⟩

/-- Three-step restriction regrouped by endpoint. The copies of `S^ν` are indexed by
the three-step paths from `μ` to `ν`. -/
theorem spechtModule_branching_threeSteps_byEndpoint {n : ℕ}
    (μ : YoungDiagramOfSize (n + 3)) :
    Nonempty
      ((SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj
            ((SymmetricGroupRepresentation.restriction (n + 2)).obj (spechtModule μ))) ≅
        ⨁ fun ν : YoungDiagramOfSize n =>
          ⨁ fun _ : ThreeStepRemovalTo μ ν => spechtModule ν) := by
  let e := Classical.choice (spechtModule_branching_threeSteps μ)
  let endpoint := fun p : ThreeStepRemoval μ => p.2.2.val
  let fibers := fun ν : YoungDiagramOfSize n => { p : ThreeStepRemoval μ // endpoint p = ν }
  let reindex :
      (⨁ fun p : ThreeStepRemoval μ => spechtModule p.2.2.val) ≅
        ⨁ fun q : Σ ν, fibers ν => spechtModule q.1 :=
    biproduct.reindex (Equiv.sigmaFiberEquiv endpoint).symm
      (fun q : Σ ν, fibers ν => spechtModule q.1)
  exact ⟨e ≪≫ reindex ≪≫
    (biproductBiproductIso fibers (fun ν _ => spechtModule ν)).symm⟩
