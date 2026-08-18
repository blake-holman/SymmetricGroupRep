import SymmetricGroupRep.OuterTensor
import SymmetricGroupRep.TwoStepBranchingBasis
import SymmetricGroupRep.YoungSubgroup

/-! # Inducing a Specht module along with a character of `S_2`

Induction from `S_n × S_2` is read off from the two-step branching rule. The
transposition of the last two labels commutes with `S_n`, so it acts on the
multiplicity space of `S^μ` inside the twice-restricted `S^ξ`, and a morphism
out of `S^μ ⊠ X` is exactly a morphism out of `S^μ` on which that action is the
scalar by which the transposition acts on `X`. Young's orthogonal form computes
the action on the path-indexed multiplicity space, and its eigenvalues split the
two-step paths according to whether the two added cells share a row or a column.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- A Young diagram contains every cell weakly above and to the left of one of
its cells. -/
theorem YoungDiagram.mem_cells_of_le {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hrow : c.1 ≤ d.1) (hcol : c.2 ≤ d.2) (hd : d ∈ μ.cells) : c ∈ μ.cells := by
  rcases c with ⟨_, _⟩
  rcases d with ⟨_, _⟩
  exact μ.up_left_mem hrow hcol hd

/-- Containment of Young diagrams is containment of their rows. -/
theorem YoungDiagram.rowLen_le_of_le {μ ξ : YoungDiagram} (hle : μ ≤ ξ) (k : ℕ) :
    μ.rowLen k ≤ ξ.rowLen k := by
  rcases Nat.eq_zero_or_pos (μ.rowLen k) with h | h
  · omega
  · have hmem : (k, μ.rowLen k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have := YoungDiagram.mem_iff_lt_rowLen.mp (hle hmem)
    omega

/-- Rows beyond the number of cells are empty. -/
theorem YoungDiagram.rowLen_eq_zero_of_card_le {μ : YoungDiagram} {k : ℕ}
    (hk : μ.card ≤ k) : μ.rowLen k = 0 := by
  by_contra hne
  have hmem : (k, 0) ∈ μ.cells := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  exact absurd (μ.cell_fst_lt_card hmem) (by omega)

/-- A Young diagram containing another with two more cells has an intermediate
diagram: the last row in which the two differ can lose its final cell. -/
theorem YoungDiagram.exists_intermediate {μ ξ : YoungDiagram} (hle : μ ≤ ξ)
    (hcard : ξ.card = μ.card + 2) :
    ∃ lam : YoungDiagram, μ ≤ lam ∧ lam ≤ ξ ∧ lam.card = μ.card + 1 := by
  classical
  have hrow := YoungDiagram.rowLen_le_of_le hle
  have hne : ∃ k, μ.rowLen k < ξ.rowLen k := by
    by_contra hall
    have hall' : ∀ k, ξ.rowLen k ≤ μ.rowLen k := fun k => not_lt.mp (not_exists.mp hall k)
    exact absurd (YoungDiagram.ext_of_rowLen fun k => le_antisymm (hrow k) (hall' k)) fun h => by
      rw [h] at hcard; omega
  obtain ⟨k, hk⟩ := hne
  have hkle : k ≤ ξ.card := by
    by_contra hgt
    have hzero : ξ.rowLen k = 0 := YoungDiagram.rowLen_eq_zero_of_card_le (by omega)
    omega
  set i := Nat.findGreatest (fun k => μ.rowLen k < ξ.rowLen k) ξ.card with hi
  have hspec : μ.rowLen i < ξ.rowLen i :=
    Nat.findGreatest_spec (P := fun k => μ.rowLen k < ξ.rowLen k) hkle hk
  have hgreatest : ∀ m, i < m → ξ.rowLen m < ξ.rowLen i := by
    intro m hm
    rcases le_or_gt m ξ.card with hmle | hmgt
    · have hm' : Nat.findGreatest (fun k => μ.rowLen k < ξ.rowLen k) ξ.card < m := by
        rw [← hi]; exact hm
      have hnot : ¬ μ.rowLen m < ξ.rowLen m :=
        Nat.findGreatest_is_greatest (P := fun k => μ.rowLen k < ξ.rowLen k) hm' hmle
      have := ξ.rowLen_anti i m hm.le
      have := μ.rowLen_anti i m hm.le
      have := hrow m
      omega
    · rw [YoungDiagram.rowLen_eq_zero_of_card_le (by omega)]
      omega
  refine ⟨ξ.removeBox i hgreatest, ?_, YoungDiagram.removeBox_le hgreatest, ?_⟩
  · rw [← YoungDiagram.cells_subset_iff, YoungDiagram.cells_removeBox]
    intro c hc
    refine Finset.mem_erase.mpr ⟨fun hcell => ?_, hle (by simpa using hc)⟩
    rw [hcell] at hc
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)
  · have := YoungDiagram.card_removeBox hgreatest
    omega

/-- A two-box skew shape carries a two-step removal path. -/
theorem nonempty_twoStepRemovalTo {n : ℕ} (μ : YoungDiagramOfSize n)
    (ξ : YoungDiagramOfSize (n + 2)) (hle : μ.val ≤ ξ.val) :
    Nonempty (TwoStepRemovalTo ξ μ) := by
  obtain ⟨lam, hμlam, hlamξ, hcard⟩ :=
    YoungDiagram.exists_intermediate hle (by rw [ξ.property, μ.property])
  exact ⟨⟨⟨⟨⟨lam, by rw [hcard, μ.property]⟩, hlamξ⟩, ⟨μ, hμlam⟩⟩, rfl⟩⟩

namespace TwoStepRemovalTo

variable {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)} {μ : YoungDiagramOfSize n}

/-- The cell removed first along a two-step path. -/
noncomputable def firstCell (p : TwoStepRemovalTo ξ μ) : ℕ × ℕ :=
  OneBoxRemoval.cell p.val.1

/-- The cell removed second along a two-step path. -/
noncomputable def secondCell (p : TwoStepRemovalTo ξ μ) : ℕ × ℕ :=
  OneBoxRemoval.cell p.val.2

/-- The endpoint of a path is the diagram the path lands on. -/
theorem endpoint_cells (p : TwoStepRemovalTo ξ μ) : p.val.2.val.val.cells = μ.val.cells :=
  congrArg (fun ν : YoungDiagramOfSize n => ν.val.cells) p.property

/-- The intermediate diagram of a path is its endpoint together with the cell
removed second. -/
theorem middleDifference_eq_secondCell (p : TwoStepRemovalTo ξ μ) :
    p.middleDifference = {p.secondCell} := by
  have h := OneBoxRemoval.sdiff_eq_cell p.val.2
  rw [p.endpoint_cells] at h
  exact h

/-- The cell removed second still belongs to the intermediate diagram. -/
theorem secondCell_mem_middle (p : TwoStepRemovalTo ξ μ) :
    p.secondCell ∈ p.val.1.val.val.cells :=
  OneBoxRemoval.cell_mem p.val.2

/-- The cell removed first is gone from the intermediate diagram. -/
theorem firstCell_notMem_middle (p : TwoStepRemovalTo ξ μ) :
    p.firstCell ∉ p.val.1.val.val.cells :=
  OneBoxRemoval.cell_notMem p.val.1

/-- The two removed cells are distinct. -/
theorem firstCell_ne_secondCell (p : TwoStepRemovalTo ξ μ) :
    p.firstCell ≠ p.secondCell := fun h =>
  p.firstCell_notMem_middle (h ▸ p.secondCell_mem_middle)

/-- The endpoint of a path is contained in its start. -/
theorem endpoint_le (p : TwoStepRemovalTo ξ μ) : μ.val ≤ ξ.val :=
  p.endpoint_le_middle.trans p.val.1.property

/-- The two cells a path removes are exactly the cells of the skew shape. -/
theorem cells_sdiff_eq (p : TwoStepRemovalTo ξ μ) :
    ξ.val.cells \ μ.val.cells = {p.firstCell, p.secondCell} := by
  classical
  have hcard : (ξ.val.cells \ μ.val.cells).card = 2 := by
    simpa using YoungDiagramOfSize.card_sdiff μ ξ p.endpoint_le
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_sdiff.mpr ⟨OneBoxRemoval.cell_mem p.val.1,
        fun hmem => p.firstCell_notMem_middle
          (YoungDiagram.cells_subset_iff.mp p.endpoint_le_middle hmem)⟩
    · rw [Finset.mem_singleton] at hc
      subst hc
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact YoungDiagram.cells_subset_iff.mp p.val.1.property p.secondCell_mem_middle
      · rw [← p.endpoint_cells]
        exact OneBoxRemoval.cell_notMem p.val.2
  · rw [hcard, Finset.card_insert_of_notMem (by simpa using p.firstCell_ne_secondCell),
      Finset.card_singleton]

/-- A two-box skew shape is a horizontal strip exactly when its two cells lie in
different columns. -/
theorem isHorizontalTwoStrip_iff (p : TwoStepRemovalTo ξ μ) :
    IsHorizontalTwoStrip μ ξ ↔ p.firstCell.2 ≠ p.secondCell.2 := by
  classical
  rw [IsHorizontalTwoStrip, p.cells_sdiff_eq]
  constructor
  · rintro ⟨-, hinj⟩ hcol
    exact p.firstCell_ne_secondCell (hinj (by simp) (by simp) hcol)
  · intro hcol
    refine ⟨p.endpoint_le, ?_⟩
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hab hcol
    · exact absurd hab.symm hcol
    · rfl

/-- A two-box skew shape is a vertical strip exactly when its two cells lie in
different rows. -/
theorem isVerticalTwoStrip_iff (p : TwoStepRemovalTo ξ μ) :
    IsVerticalTwoStrip μ ξ ↔ p.firstCell.1 ≠ p.secondCell.1 := by
  classical
  rw [IsVerticalTwoStrip, p.cells_sdiff_eq]
  constructor
  · rintro ⟨-, hinj⟩ hrow
    exact p.firstCell_ne_secondCell (hinj (by simp) (by simp) hrow)
  · intro hrow
    refine ⟨p.endpoint_le, ?_⟩
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hab hrow
    · exact absurd hab.symm hrow
    · rfl

/-- Every path to the same endpoint removes one of the same two cells first. -/
theorem exists_middleDifference_eq (r : TwoStepRemovalTo ξ μ) (p : TwoStepRemovalTo ξ μ) :
    r.middleDifference = {p.firstCell} ∨ r.middleDifference = {p.secondCell} := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp r.middleDifference_card
  have hmem : c ∈ ξ.val.cells \ μ.val.cells :=
    r.middleDifference_subset (hc ▸ Finset.mem_singleton_self c)
  rw [p.cells_sdiff_eq] at hmem
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact Or.inl hc
  · rw [Finset.mem_singleton] at hmem
    exact Or.inr (hc.trans (by rw [hmem]))

/-- A path is determined by the cell it removes second. -/
theorem eq_of_middleDifference_eq (r p : TwoStepRemovalTo ξ μ)
    (h : r.middleDifference = {p.secondCell}) : r = p :=
  middleDifference_injective (h.trans p.middleDifference_eq_secondCell.symm)

/-- Along a path whose two cells share a row or a column, the cell removed
second is weakly above and to the left of the cell removed first. -/
theorem secondCell_le_firstCell (p : TwoStepRemovalTo ξ μ)
    (h : p.firstCell.1 = p.secondCell.1 ∨ p.firstCell.2 = p.secondCell.2) :
    p.secondCell.1 ≤ p.firstCell.1 ∧ p.secondCell.2 ≤ p.firstCell.2 := by
  have key : p.firstCell.1 ≤ p.secondCell.1 → p.firstCell.2 ≤ p.secondCell.2 → False :=
    fun hrow hcol => p.firstCell_notMem_middle
      (YoungDiagram.mem_cells_of_le hrow hcol p.secondCell_mem_middle)
  rcases h with h | h
  · refine ⟨h.ge, ?_⟩
    by_contra hlt
    exact key h.le (le_of_not_ge hlt)
  · refine ⟨?_, h.ge⟩
    by_contra hlt
    exact key (le_of_not_ge hlt) h.le

/-- If the two added cells share a row or a column, only one removal order is
available. -/
theorem eq_of_secondCell_le (p : TwoStepRemovalTo ξ μ)
    (hle : p.secondCell.1 ≤ p.firstCell.1 ∧ p.secondCell.2 ≤ p.firstCell.2)
    (r : TwoStepRemovalTo ξ μ) : r = p := by
  classical
  rcases r.exists_middleDifference_eq p with hr | hr
  · exfalso
    have hfirst : p.firstCell ∈ r.val.1.val.val.cells := by
      have : p.firstCell ∈ r.middleDifference := by rw [hr]; exact Finset.mem_singleton_self _
      exact (Finset.mem_sdiff.mp this).1
    have hsecond : p.secondCell ∈ r.val.1.val.val.cells :=
      YoungDiagram.mem_cells_of_le hle.1 hle.2 hfirst
    have hnot : p.secondCell ∉ μ.val.cells := by
      have := p.cells_sdiff_eq ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self p.secondCell)
        : p.secondCell ∈ ({p.firstCell, p.secondCell} : Finset (ℕ × ℕ)))
      exact (Finset.mem_sdiff.mp this).2
    have hmem : p.secondCell ∈ r.middleDifference := Finset.mem_sdiff.mpr ⟨hsecond, hnot⟩
    rw [hr, Finset.mem_singleton] at hmem
    exact p.firstCell_ne_secondCell hmem.symm
  · exact r.eq_of_middleDifference_eq p hr

end TwoStepRemovalTo

/-- Writing the largest label into the removed cell recovers both the removal
and the smaller tableau. -/
theorem OneBoxRemoval.sigma_extend {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val) :
    (⟨(OneBoxRemoval.extend ν S).largestRemoval,
        (OneBoxRemoval.extend ν S).restrictLargest⟩ :
      Σ ν : OneBoxRemoval μ, StandardYoungTableau ν.val) = ⟨ν, S⟩ := by
  apply (standardYoungTableauEquivRemovals μ).injective
  exact OneBoxRemoval.extend_restrictLargest (OneBoxRemoval.extend ν S)

/-- Extending a tableau selects the removal it was extended along. -/
theorem OneBoxRemoval.largestRemoval_extend {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (ν : OneBoxRemoval μ) (S : StandardYoungTableau ν.val) :
    (OneBoxRemoval.extend ν S).largestRemoval = ν :=
  congrArg Sigma.fst (OneBoxRemoval.sigma_extend ν S)

/-- Writing the two largest labels into the two removed cells realises a
two-step path by a standard tableau. -/
theorem StandardYoungTableau.largestTwoStepRemoval_extend {n : ℕ}
    {ξ : YoungDiagramOfSize (n + 2)} (p : TwoStepRemoval ξ)
    (S : StandardYoungTableau p.2.val) :
    (OneBoxRemoval.extend p.1 (OneBoxRemoval.extend p.2 S)).largestTwoStepRemoval = p := by
  have hsigma := OneBoxRemoval.sigma_extend p.1 (OneBoxRemoval.extend p.2 S)
  have hstep : (⟨(OneBoxRemoval.extend p.1 (OneBoxRemoval.extend p.2 S)).largestRemoval,
        (OneBoxRemoval.extend p.1
          (OneBoxRemoval.extend p.2 S)).restrictLargest.largestRemoval⟩ : TwoStepRemoval ξ) =
      ⟨p.1, (OneBoxRemoval.extend p.2 S).largestRemoval⟩ :=
    congrArg (fun q : Σ ν : OneBoxRemoval ξ, StandardYoungTableau ν.val =>
      (⟨q.1, q.2.largestRemoval⟩ : TwoStepRemoval ξ)) hsigma
  rw [StandardYoungTableau.largestTwoStepRemoval, hstep,
    OneBoxRemoval.largestRemoval_extend]

namespace TwoStepRemovalTo

variable {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)} {μ : YoungDiagramOfSize n}

/-- A standard tableau of shape `ξ` whose two largest labels trace the path. -/
noncomputable def tableau (p : TwoStepRemovalTo ξ μ) : StandardYoungTableau ξ :=
  OneBoxRemoval.extend p.val.1
    (OneBoxRemoval.extend p.val.2 (readingTableau p.val.2.val))

/-- The realising tableau selects the path it was built from. -/
theorem largestTwoStepRemoval_tableau (p : TwoStepRemovalTo ξ μ) :
    p.tableau.largestTwoStepRemoval = p.val :=
  StandardYoungTableau.largestTwoStepRemoval_extend p.val _

/-- Deleting the two largest labels of the realising tableau gives the endpoint. -/
theorem eraseTwoLargestShape_tableau (p : TwoStepRemovalTo ξ μ) :
    p.tableau.eraseTwoLargestShape = μ := by
  have h := congrArg (fun q : TwoStepRemoval ξ => q.2.val) p.largestTwoStepRemoval_tableau
  exact h.trans p.property

/-- The realising tableau selects the path it was built from, as a path indexed
by the endpoint. -/
theorem largestTwoStepRemovalTo_tableau (p : TwoStepRemovalTo ξ μ) :
    p.tableau.largestTwoStepRemovalTo.cast p.eraseTwoLargestShape_tableau = p :=
  Subtype.ext ((TwoStepRemovalTo.cast_val _ _).trans p.largestTwoStepRemoval_tableau)

/-- The largest label of the realising tableau sits in the cell removed first. -/
theorem position_tableau_last (p : TwoStepRemovalTo ξ μ) :
    p.tableau.position (Fin.last (n + 1)) = p.firstCell :=
  OneBoxRemoval.position_extend_last p.val.1 _

/-- The second largest label of the realising tableau sits in the cell removed
second. -/
theorem position_tableau_castSucc_last (p : TwoStepRemovalTo ξ μ) :
    p.tableau.position (Fin.castSucc (Fin.last n)) = p.secondCell :=
  (OneBoxRemoval.position_extend_castSucc p.val.1 _ (Fin.last n)).trans
    (OneBoxRemoval.position_extend_last p.val.2 _)

end TwoStepRemovalTo

/-- When the two largest labels have no admissible swap, the last adjacent
transposition acts on the tableau basis vector by the Young coefficient alone. -/
theorem lastAdjacentTranspositionEndomorphism_apply_basis_of_not_swap {n : ℕ}
    (ξ : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau ξ)
    (h : ¬ T.IsAdjacentSwapStandard (Fin.last n)) :
    (lastAdjacentTranspositionEndomorphism ξ).hom.hom.hom (spechtOrthogonalBasis ξ T) =
      ((T.axialDistance (Fin.last n) : ℂ)⁻¹) • spechtOrthogonalBasis ξ T := by
  rw [lastAdjacentTranspositionEndomorphism_hom]
  change (spechtModule ξ).ρ (SymmetricGroup.adjacentTransposition (Fin.last n))
      (spechtOrthogonalBasis ξ T) = _
  simpa [swappedOrthogonalBasisVector, h] using
    spechtOrthogonalBasis_adjacentTransposition ξ T (Fin.last n)

/-- When the two largest labels have no admissible swap, the diagonal block of
the last adjacent transposition is still the Young axial-distance coefficient. -/
theorem twoStepBranchingBlockEntry_lastAdjacent_pp_of_not_swap {n : ℕ}
    (ξ : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau ξ)
    (h : ¬ T.IsAdjacentSwapStandard (Fin.last n)) :
    twoStepBranchingBlockEntry ξ T.eraseTwoLargestShape
        (lastAdjacentTranspositionEndomorphism ξ)
        T.largestTwoStepRemovalTo T.largestTwoStepRemovalTo =
      ((T.axialDistance (Fin.last n) : ℂ)⁻¹) •
        𝟙 (spechtModule T.eraseTwoLargestShape) := by
  apply spechtEndomorphism_eq_smul_id_of_apply_basis
    T.eraseTwoLargestShape T.restrictTwoLargest
  unfold twoStepBranchingBlockEntry
  change
    (twoStepBranchingProjection ξ T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        ((lastAdjacentTranspositionEndomorphism ξ).hom.hom.hom
          ((twoStepBranchingInclusion ξ T.eraseTwoLargestShape
            T.largestTwoStepRemovalTo).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest))) = _
  rw [twoStepBranchingInclusion_apply_spechtOrthogonalBasis,
    lastAdjacentTranspositionEndomorphism_apply_basis_of_not_swap ξ T h]
  let P := (twoStepBranchingProjection ξ T.eraseTwoLargestShape
    T.largestTwoStepRemovalTo).hom.hom.hom
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let eT := spechtOrthogonalBasis ξ T
  have hPT : P eT =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest :=
    twoStepBranchingProjection_apply_spechtOrthogonalBasis ξ T
  change P (a • eT) = a • _
  exact (P.map_smul a eT).trans (by rw [hPT])

/-- Transporting a path along an equality of endpoints does not change the
scalar it contributes to an endpoint block. -/
theorem twoStepMultiplicityMatrix_cast {n : ℕ} (ξ : YoungDiagramOfSize (n + 2))
    {ν ν' : YoungDiagramOfSize n} (h : ν = ν')
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ)))
    (p q : TwoStepRemovalTo ξ ν) :
    twoStepMultiplicityMatrix ξ ν' A (p.cast h) (q.cast h) =
      twoStepMultiplicityMatrix ξ ν A p q := by
  subst h
  rfl

namespace TwoStepRemovalTo

variable {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)} {μ : YoungDiagramOfSize n}

/-- The largest label of the realising tableau sits in the cell removed first. -/
theorem position_tableau_succ_last (p : TwoStepRemovalTo ξ μ) :
    p.tableau.position (Fin.last n).succ = p.firstCell := by
  rw [Fin.succ_last]
  exact p.position_tableau_last

/-- The two largest labels of the realising tableau may be swapped exactly when
the two removed cells share neither a row nor a column. -/
theorem isAdjacentSwapStandard_tableau_iff (p : TwoStepRemovalTo ξ μ) :
    p.tableau.IsAdjacentSwapStandard (Fin.last n) ↔
      p.secondCell.1 ≠ p.firstCell.1 ∧ p.secondCell.2 ≠ p.firstCell.2 := by
  rw [StandardYoungTableau.isAdjacentSwapStandard_iff, p.position_tableau_castSucc_last,
    p.position_tableau_succ_last]

/-- Two cells in the same row are at axial distance one. -/
theorem axialDistance_tableau_eq_one (p : TwoStepRemovalTo ξ μ)
    (h : p.firstCell.1 = p.secondCell.1) : p.tableau.axialDistance (Fin.last n) = 1 :=
  p.tableau.axialDistance_eq_one_of_row_eq (Fin.last n) (by
    rw [p.position_tableau_castSucc_last, p.position_tableau_succ_last]
    exact h.symm)

/-- Two cells in the same column are at axial distance minus one. -/
theorem axialDistance_tableau_eq_neg_one (p : TwoStepRemovalTo ξ μ)
    (h : p.firstCell.2 = p.secondCell.2) : p.tableau.axialDistance (Fin.last n) = -1 :=
  p.tableau.axialDistance_eq_neg_one_of_column_eq (Fin.last n) (by
    rw [p.position_tableau_castSucc_last, p.position_tableau_succ_last]
    exact h.symm)

/-- Two distinct paths to the same endpoint differ by swapping the two largest
labels of the tableau realising either one. -/
theorem cast_swappedLargestTwoStepRemovalTo (p q : TwoStepRemovalTo ξ μ) (hne : p ≠ q)
    (h : p.tableau.IsAdjacentSwapStandard (Fin.last n)) :
    (p.tableau.swappedLargestTwoStepRemovalTo h).cast p.eraseTwoLargestShape_tableau = q := by
  have hswap : (p.tableau.swappedLargestTwoStepRemovalTo h).cast
      p.eraseTwoLargestShape_tableau ≠ p := by
    intro heq
    refine p.tableau.largestTwoStepRemovalTo_ne_swapped h (Subtype.ext ?_)
    have h₁ := congrArg Subtype.val heq
    have h₂ := congrArg Subtype.val p.largestTwoStepRemovalTo_tableau
    rw [TwoStepRemovalTo.cast_val] at h₁ h₂
    exact h₂.trans h₁.symm
  rcases TwoStepRemovalTo.eq_or_eq_of_ne p q hne _ with heq | heq
  · exact absurd heq hswap
  · exact heq

/-- The diagonal entry of the transposition on a path block is the reciprocal of
the axial distance between the two removed cells. -/
theorem twoStepMultiplicityMatrix_lastAdjacent_self (p : TwoStepRemovalTo ξ μ) :
    twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p =
      ((p.tableau.axialDistance (Fin.last n) : ℂ)⁻¹) := by
  have hcast := twoStepMultiplicityMatrix_cast ξ p.eraseTwoLargestShape_tableau
    (lastAdjacentTranspositionEndomorphism ξ) p.tableau.largestTwoStepRemovalTo
    p.tableau.largestTwoStepRemovalTo
  rw [p.largestTwoStepRemovalTo_tableau] at hcast
  rw [hcast]
  apply twoStepMultiplicityMatrix_eq_of_blockEntry_eq_smul_id
  by_cases h : p.tableau.IsAdjacentSwapStandard (Fin.last n)
  · exact twoStepBranchingBlockEntry_lastAdjacent_pp ξ p.tableau h
  · exact twoStepBranchingBlockEntry_lastAdjacent_pp_of_not_swap ξ p.tableau h

/-- On two distinct paths the transposition has Young's two-by-two matrix. -/
theorem twoStepMultiplicityMatrix_lastAdjacent_of_ne (p q : TwoStepRemovalTo ξ μ)
    (hne : p ≠ q) (h : p.tableau.IsAdjacentSwapStandard (Fin.last n)) :
    twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q =
        Complex.sqrt (1 - ((p.tableau.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) ∧
      twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) q p =
        Complex.sqrt (1 - ((p.tableau.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) ∧
      twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) q q =
        -((p.tableau.axialDistance (Fin.last n) : ℂ)⁻¹) := by
  have hq := p.cast_swappedLargestTwoStepRemovalTo q hne h
  have hp := p.largestTwoStepRemovalTo_tableau
  refine ⟨?_, ?_, ?_⟩
  · have hcast := twoStepMultiplicityMatrix_cast ξ p.eraseTwoLargestShape_tableau
      (lastAdjacentTranspositionEndomorphism ξ) p.tableau.largestTwoStepRemovalTo
      (p.tableau.swappedLargestTwoStepRemovalTo h)
    rw [hp, hq] at hcast
    rw [hcast]
    exact twoStepMultiplicityMatrix_eq_of_blockEntry_eq_smul_id _ _ _ _ _ _
      (twoStepBranchingBlockEntry_lastAdjacent_pq ξ p.tableau h)
  · have hcast := twoStepMultiplicityMatrix_cast ξ p.eraseTwoLargestShape_tableau
      (lastAdjacentTranspositionEndomorphism ξ) (p.tableau.swappedLargestTwoStepRemovalTo h)
      p.tableau.largestTwoStepRemovalTo
    rw [hp, hq] at hcast
    rw [hcast]
    exact twoStepMultiplicityMatrix_eq_of_blockEntry_eq_smul_id _ _ _ _ _ _
      (twoStepBranchingBlockEntry_lastAdjacent_qp ξ p.tableau h)
  · have hcast := twoStepMultiplicityMatrix_cast ξ p.eraseTwoLargestShape_tableau
      (lastAdjacentTranspositionEndomorphism ξ) (p.tableau.swappedLargestTwoStepRemovalTo h)
      (p.tableau.swappedLargestTwoStepRemovalTo h)
    rw [hq] at hcast
    rw [hcast]
    exact twoStepMultiplicityMatrix_eq_of_blockEntry_eq_smul_id _ _ _ _ _ _
      (twoStepBranchingBlockEntry_lastAdjacent_qq ξ p.tableau h)

end TwoStepRemovalTo

/-- A morphism into a twice-restricted Specht module vanishes as soon as all of
its two-step branching components do. -/
theorem hom_eq_zero_of_twoStepBranchingProjection {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)}
    {V : SymmetricGroupRepresentation n}
    (g : V ⟶ (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ)))
    (h : ∀ (ν : YoungDiagramOfSize n) (r : TwoStepRemovalTo ξ ν),
      g ≫ twoStepBranchingProjection ξ ν r = 0) : g = 0 := by
  have hcomp : g ≫ (spechtBranchingIso_twoSteps_byEndpoint ξ).hom = 0 := by
    refine biproduct.hom_ext _ _ fun ν => ?_
    refine biproduct.hom_ext _ _ fun r => ?_
    have := h ν r
    rw [twoStepBranchingProjection, ← Category.assoc, ← Category.assoc] at this
    simpa [Category.assoc] using this
  calc g = (g ≫ (spechtBranchingIso_twoSteps_byEndpoint ξ).hom) ≫
        (spechtBranchingIso_twoSteps_byEndpoint ξ).inv := by simp
    _ = 0 := by rw [hcomp, Limits.zero_comp]

/-- Morphisms out of `S^μ` on which the transposition of the last two labels
acts by the scalar `c`. -/
noncomputable def lastAdjacentEigenspace {n : ℕ} (ξ : YoungDiagramOfSize (n + 2))
    (μ : YoungDiagramOfSize n) (c : ℂ) :
    Submodule ℂ (spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
      ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ))) where
  carrier := {f | f ≫ lastAdjacentTranspositionEndomorphism ξ = c • f}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [Preadditive.add_comp, hf, hg, smul_add]
  zero_mem' := by simp
  smul_mem' := by
    intro a f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    rw [Linear.smul_comp, hf, smul_comm]

@[simp]
theorem mem_lastAdjacentEigenspace {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)}
    {μ : YoungDiagramOfSize n} {c : ℂ} {f : spechtModule μ ⟶
      (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ))} :
    f ∈ lastAdjacentEigenspace ξ μ c ↔
      f ≫ lastAdjacentTranspositionEndomorphism ξ = c • f := Iff.rfl

section Multiplicity

variable {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)} {μ : YoungDiagramOfSize n}

/-- Scalars are read off a multiple of a path inclusion by its own projection. -/
theorem smul_twoStepBranchingInclusion_injective (p : TwoStepRemovalTo ξ μ) {x y : ℂ}
    (h : x • twoStepBranchingInclusion ξ μ p = y • twoStepBranchingInclusion ξ μ p) : x = y := by
  letI := spechtModule_irreducible μ
  have hcomp := congrArg (fun g => g ≫ twoStepBranchingProjection ξ μ p) h
  simp only [Linear.smul_comp, twoStepBranchingInclusion_projection] at hcomp
  exact smul_left_injective ℂ (CategoryTheory.id_nonzero (spechtModule μ)) hcomp

/-- A path inclusion is nonzero. -/
theorem twoStepBranchingInclusion_ne_zero (p : TwoStepRemovalTo ξ μ) :
    twoStepBranchingInclusion ξ μ p ≠ 0 := by
  letI := spechtModule_irreducible μ
  intro h
  refine CategoryTheory.id_nonzero (spechtModule μ) ?_
  have := congrArg (fun g => g ≫ twoStepBranchingProjection ξ μ p) h
  simpa [twoStepBranchingInclusion_projection] using this

/-- With only one two-step path to `μ`, every morphism out of `S^μ` is a
multiple of that path's inclusion. -/
theorem exists_eq_smul_twoStepBranchingInclusion (p : TwoStepRemovalTo ξ μ)
    (hsub : ∀ r : TwoStepRemovalTo ξ μ, r = p)
    (f : spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
      ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ))) :
    ∃ a : ℂ, f = a • twoStepBranchingInclusion ξ μ p := by
  obtain ⟨a, ha⟩ := spechtEndomorphism_eq_smul_id μ (f ≫ twoStepBranchingProjection ξ μ p)
  refine ⟨a, sub_eq_zero.mp (hom_eq_zero_of_twoStepBranchingProjection _ fun ν r => ?_)⟩
  by_cases hν : ν = μ
  · subst hν
    rw [hsub r, Preadditive.sub_comp, Linear.smul_comp,
      twoStepBranchingInclusion_projection, if_pos rfl, ha, sub_self]
  · exact spechtHom_eq_zero_of_ne (fun heq => hν heq.symm) _

/-- With two two-step paths to `μ`, every morphism out of `S^μ` is a
combination of their inclusions. -/
theorem exists_eq_add_smul_twoStepBranchingInclusion (p q : TwoStepRemovalTo ξ μ) (hpq : p ≠ q)
    (f : spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
      ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ))) :
    ∃ a b : ℂ, f = a • twoStepBranchingInclusion ξ μ p + b • twoStepBranchingInclusion ξ μ q := by
  obtain ⟨a, ha⟩ := spechtEndomorphism_eq_smul_id μ (f ≫ twoStepBranchingProjection ξ μ p)
  obtain ⟨b, hb⟩ := spechtEndomorphism_eq_smul_id μ (f ≫ twoStepBranchingProjection ξ μ q)
  refine ⟨a, b, sub_eq_zero.mp (hom_eq_zero_of_twoStepBranchingProjection _ fun ν r => ?_)⟩
  by_cases hν : ν = μ
  · subst hν
    rcases TwoStepRemovalTo.eq_or_eq_of_ne p q hpq r with rfl | rfl
    · rw [Preadditive.sub_comp, Preadditive.add_comp, Linear.smul_comp, Linear.smul_comp,
        twoStepBranchingInclusion_projection, twoStepBranchingInclusion_projection,
        if_pos rfl, if_neg (Ne.symm hpq), ha, smul_zero, add_zero, sub_self]
    · rw [Preadditive.sub_comp, Preadditive.add_comp, Linear.smul_comp, Linear.smul_comp,
        twoStepBranchingInclusion_projection, twoStepBranchingInclusion_projection,
        if_pos rfl, if_neg hpq, hb, smul_zero, zero_add, sub_self]
  · exact spechtHom_eq_zero_of_ne (fun heq => hν heq.symm) _

/-- The last adjacent transposition acts on a lone path inclusion by its
diagonal matrix entry. -/
theorem twoStepBranchingInclusion_comp_lastAdjacent (p : TwoStepRemovalTo ξ μ)
    (hsub : ∀ r : TwoStepRemovalTo ξ μ, r = p) :
    twoStepBranchingInclusion ξ μ p ≫ lastAdjacentTranspositionEndomorphism ξ =
      twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p •
        twoStepBranchingInclusion ξ μ p := by
  refine sub_eq_zero.mp (hom_eq_zero_of_twoStepBranchingProjection _ fun ν r => ?_)
  by_cases hν : ν = μ
  · subst hν
    rw [hsub r, Preadditive.sub_comp, Linear.smul_comp,
      twoStepBranchingInclusion_projection, if_pos rfl, Category.assoc,
      ← twoStepBranchingBlockEntry, twoStepBranchingBlockEntry_eq_matrix_smul_id, sub_self]
  · exact spechtHom_eq_zero_of_ne (fun heq => hν heq.symm) _

/-- The last adjacent transposition acts on path inclusions through its
two-by-two matrix. -/
theorem twoStepBranchingInclusion_comp_lastAdjacent_pair (p q : TwoStepRemovalTo ξ μ)
    (hpq : p ≠ q) :
    twoStepBranchingInclusion ξ μ p ≫ lastAdjacentTranspositionEndomorphism ξ =
      twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p •
          twoStepBranchingInclusion ξ μ p +
        twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q •
          twoStepBranchingInclusion ξ μ q := by
  refine sub_eq_zero.mp (hom_eq_zero_of_twoStepBranchingProjection _ fun ν r => ?_)
  by_cases hν : ν = μ
  · subst hν
    rcases TwoStepRemovalTo.eq_or_eq_of_ne p q hpq r with rfl | rfl
    · rw [Preadditive.sub_comp, Preadditive.add_comp, Linear.smul_comp, Linear.smul_comp,
        twoStepBranchingInclusion_projection, twoStepBranchingInclusion_projection,
        if_pos rfl, if_neg (Ne.symm hpq), Category.assoc, ← twoStepBranchingBlockEntry,
        twoStepBranchingBlockEntry_eq_matrix_smul_id, smul_zero, add_zero, sub_self]
    · rw [Preadditive.sub_comp, Preadditive.add_comp, Linear.smul_comp, Linear.smul_comp,
        twoStepBranchingInclusion_projection, twoStepBranchingInclusion_projection,
        if_pos rfl, if_neg hpq, Category.assoc, ← twoStepBranchingBlockEntry,
        twoStepBranchingBlockEntry_eq_matrix_smul_id, smul_zero, zero_add, sub_self]
  · exact spechtHom_eq_zero_of_ne (fun heq => hν heq.symm) _

end Multiplicity

section Eigenspace

variable {n : ℕ} {ξ : YoungDiagramOfSize (n + 2)} {μ : YoungDiagramOfSize n}

/-- Inclusions of distinct paths are linearly independent. -/
theorem smul_add_smul_twoStepBranchingInclusion_injective {p q : TwoStepRemovalTo ξ μ}
    (hpq : p ≠ q) {x y x' y' : ℂ}
    (h : x • twoStepBranchingInclusion ξ μ p + y • twoStepBranchingInclusion ξ μ q =
      x' • twoStepBranchingInclusion ξ μ p + y' • twoStepBranchingInclusion ξ μ q) :
    x = x' ∧ y = y' := by
  letI := spechtModule_irreducible μ
  constructor
  · have hcomp := congrArg (fun g => g ≫ twoStepBranchingProjection ξ μ p) h
    simp only [Preadditive.add_comp, Linear.smul_comp, twoStepBranchingInclusion_projection,
      if_neg (Ne.symm hpq), smul_zero, add_zero] at hcomp
    exact smul_left_injective ℂ (CategoryTheory.id_nonzero (spechtModule μ)) hcomp
  · have hcomp := congrArg (fun g => g ≫ twoStepBranchingProjection ξ μ q) h
    simp only [Preadditive.add_comp, Linear.smul_comp, twoStepBranchingInclusion_projection,
      if_neg hpq, smul_zero, zero_add] at hcomp
    exact smul_left_injective ℂ (CategoryTheory.id_nonzero (spechtModule μ)) hcomp

/-- With no two-step path to `μ` the eigenspaces are trivial. -/
theorem finrank_lastAdjacentEigenspace_of_isEmpty (hempty : IsEmpty (TwoStepRemovalTo ξ μ))
    (c : ℂ) : Module.finrank ℂ (lastAdjacentEigenspace ξ μ c) = 0 := by
  have hbot : lastAdjacentEigenspace ξ μ c = ⊥ := by
    refine Submodule.eq_bot_iff _ |>.mpr fun f _ => ?_
    refine hom_eq_zero_of_twoStepBranchingProjection _ fun ν r => ?_
    by_cases hν : ν = μ
    · subst hν
      exact (hempty.false r).elim
    · exact spechtHom_eq_zero_of_ne (fun heq => hν heq.symm) _
  rw [hbot, finrank_bot]

/-- With one two-step path to `μ` the eigenspace is the diagonal entry's
eigenline. -/
theorem finrank_lastAdjacentEigenspace_of_subsingleton (p : TwoStepRemovalTo ξ μ)
    (hsub : ∀ r : TwoStepRemovalTo ξ μ, r = p) (c : ℂ) :
    Module.finrank ℂ (lastAdjacentEigenspace ξ μ c) =
      if twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p = c
        then 1 else 0 := by
  by_cases hM : twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p = c
  · rw [if_pos hM]
    have hspan : lastAdjacentEigenspace ξ μ c = Submodule.span ℂ {twoStepBranchingInclusion ξ μ p} := by
      refine le_antisymm (fun f _ => ?_) ?_
      · obtain ⟨a, ha⟩ := exists_eq_smul_twoStepBranchingInclusion p hsub f
        exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        show twoStepBranchingInclusion ξ μ p ≫ _ = _
        rw [twoStepBranchingInclusion_comp_lastAdjacent p hsub, hM]
    rw [hspan, finrank_span_singleton (twoStepBranchingInclusion_ne_zero p)]
  · rw [if_neg hM]
    have hbot : lastAdjacentEigenspace ξ μ c = ⊥ := by
      refine Submodule.eq_bot_iff _ |>.mpr fun f hf => ?_
      obtain ⟨a, ha⟩ := exists_eq_smul_twoStepBranchingInclusion p hsub f
      rw [mem_lastAdjacentEigenspace, ha, Linear.smul_comp,
        twoStepBranchingInclusion_comp_lastAdjacent p hsub, smul_smul, smul_smul] at hf
      have hcoeff := smul_twoStepBranchingInclusion_injective p hf
      have ha0 : a = 0 := by
        have hfactor : a * (twoStepMultiplicityMatrix ξ μ
            (lastAdjacentTranspositionEndomorphism ξ) p p - c) = 0 := by
          linear_combination hcoeff
        rcases mul_eq_zero.mp hfactor with h | h
        · exact h
        · exact absurd (by linear_combination h) hM
      rw [ha, ha0, zero_smul]
    rw [hbot, finrank_bot]

/-- With two two-step paths to `μ` each eigenvalue of the transposition block
contributes one dimension. -/
theorem finrank_lastAdjacentEigenspace_of_pair (p q : TwoStepRemovalTo ξ μ) (hpq : p ≠ q)
    (c : ℂ) (hc : c ^ 2 = 1)
    (hsq : (twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p) ^ 2 +
      (twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q) ^ 2 = 1)
    (hqp : twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) q p =
      twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q)
    (hqq : twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) q q =
      -twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p)
    (hcα : c - twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p ≠ 0) :
    Module.finrank ℂ (lastAdjacentEigenspace ξ μ c) = 1 := by
  letI := spechtModule_irreducible μ
  set α := twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p with hαdef
  set β := twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q with hβdef
  have hιp := twoStepBranchingInclusion_comp_lastAdjacent_pair p q hpq
  have hιq := twoStepBranchingInclusion_comp_lastAdjacent_pair q p (Ne.symm hpq)
  rw [hqq, hqp] at hιq
  set v := β • twoStepBranchingInclusion ξ μ p +
    (c - α) • twoStepBranchingInclusion ξ μ q with hvdef
  have hvmem : v ∈ lastAdjacentEigenspace ξ μ c := by
    rw [mem_lastAdjacentEigenspace, hvdef, Preadditive.add_comp, Linear.smul_comp,
      Linear.smul_comp, hιp, hιq]
    match_scalars
    · ring
    · linear_combination hsq - hc
  have hvne : v ≠ 0 := by
    intro h0
    have hcomp := congrArg (fun g => g ≫ twoStepBranchingProjection ξ μ q) h0
    simp only [hvdef, Preadditive.add_comp, Linear.smul_comp,
      twoStepBranchingInclusion_projection, if_neg hpq, smul_zero, zero_add,
      Limits.zero_comp] at hcomp
    exact hcα (by
      have := smul_left_injective ℂ (CategoryTheory.id_nonzero (spechtModule μ))
        (hcomp.trans (zero_smul ℂ (𝟙 (spechtModule μ))).symm)
      exact this)
  have hspan : lastAdjacentEigenspace ξ μ c = Submodule.span ℂ {v} := by
    refine le_antisymm (fun f hf => ?_) ?_
    · obtain ⟨a, b, hab⟩ := exists_eq_add_smul_twoStepBranchingInclusion p q hpq f
      rw [mem_lastAdjacentEigenspace, hab, Preadditive.add_comp, Linear.smul_comp,
        Linear.smul_comp, hιp, hιq] at hf
      have hcoeff : a * α + b * β = c * a ∧ a * β + b * -α = c * b := by
        refine smul_add_smul_twoStepBranchingInclusion_injective hpq ?_
        linear_combination (norm := module) hf
      refine Submodule.mem_span_singleton.mpr ⟨b / (c - α), ?_⟩
      rw [hvdef, hab, smul_add, smul_smul, smul_smul]
      have hb : b / (c - α) * (c - α) = b := div_mul_cancel₀ b hcα
      have ha : b / (c - α) * β = a := by
        field_simp
        linear_combination hcoeff.1
      rw [ha, hb]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hvmem
  rw [hspan, finrank_span_singleton hvne]

end Eigenspace

section YoungSubgroup

/-- On the first block the Young subgroup inclusion is the two-step inclusion. -/
theorem SymmetricGroup.youngSubgroupInclusion_left {n : ℕ} (σ : SymmetricGroup n) :
    SymmetricGroup.youngSubgroupInclusion n 2 (σ, 1) =
      SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n σ) := by
  refine Equiv.ext fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    have hcast : (Fin.castAdd 2 i : Fin (n + 2)) = Fin.castSucc (Fin.castSucc i) := Fin.ext rfl
    rw [SymmetricGroup.youngSubgroupInclusion_apply_castAdd, hcast,
      SymmetricGroup.inclusion_apply_castSucc, SymmetricGroup.inclusion_apply_castSucc]
    exact Fin.ext rfl
  | right i =>
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have hpoint : (Fin.natAdd n (0 : Fin 2) : Fin (n + 2)) = Fin.castSucc (Fin.last n) :=
        Fin.ext (by simp)
      rw [SymmetricGroup.youngSubgroupInclusion_apply_natAdd, hpoint,
        SymmetricGroup.inclusion_apply_castSucc, SymmetricGroup.inclusion_apply_last]
      exact Fin.ext (by simp)
    · have hpoint : (Fin.natAdd n (1 : Fin 2) : Fin (n + 2)) = Fin.last (n + 1) :=
        Fin.ext (by simp)
      rw [SymmetricGroup.youngSubgroupInclusion_apply_natAdd, hpoint,
        SymmetricGroup.inclusion_apply_last]
      exact Fin.ext (by simp)

/-- On the second block the Young subgroup inclusion is the transposition of the
last two labels. -/
theorem SymmetricGroup.youngSubgroupInclusion_right {n : ℕ} :
    SymmetricGroup.youngSubgroupInclusion n 2 (1, Equiv.swap 0 1) =
      SymmetricGroup.adjacentTransposition (Fin.last n) := by
  refine Equiv.ext fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    rw [SymmetricGroup.youngSubgroupInclusion_apply_castAdd,
      SymmetricGroup.adjacentTransposition_apply_of_ne]
    · simp
    · exact fun h => absurd (congrArg Fin.val h) (by simp; omega)
    · exact fun h => absurd (congrArg Fin.val h) (by simp; omega)
  | right i =>
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have hpoint : (Fin.natAdd n (0 : Fin 2) : Fin (n + 2)) = Fin.castSucc (Fin.last n) :=
        Fin.ext (by simp)
      rw [SymmetricGroup.youngSubgroupInclusion_apply_natAdd, hpoint,
        SymmetricGroup.adjacentTransposition_apply_left]
      exact Fin.ext (by simp)
    · have hpoint : (Fin.natAdd n (1 : Fin 2) : Fin (n + 2)) = (Fin.last n).succ :=
        Fin.ext (by simp)
      rw [SymmetricGroup.youngSubgroupInclusion_apply_natAdd, hpoint,
        SymmetricGroup.adjacentTransposition_apply_right]
      exact Fin.ext (by simp)

/-- The two elements of `S_2`. -/
theorem SymmetricGroup.eq_one_or_swap : ∀ π : SymmetricGroup 2, π = 1 ∨ π = Equiv.swap 0 1 := by
  decide

end YoungSubgroup

section Bridge

variable {n : ℕ} {μ : YoungDiagramOfSize n} {ξ : YoungDiagramOfSize (n + 2)}
  {X : SymmetricGroupRepresentation 2} {c : ℂ}

/-- Evaluating a morphism out of `S^μ ⊠ X` at a vector of `X`. -/
noncomputable def outerTensorEval
    (F : FDRep.outerTensor (spechtModule μ) X ⟶
      (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion n 2)).obj
        (spechtModule ξ)) (x : X) :
    spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
      ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ)) where
  hom := FGModuleCat.ofHom
    (F.hom.hom.hom ∘ₗ (TensorProduct.mk ℂ (spechtModule μ) X).flip x)
  comm g := by
    ext v
    show F.hom.hom.hom ((spechtModule μ).ρ g v ⊗ₜ[ℂ] x) =
      (spechtModule ξ).ρ (SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n g))
        (F.hom.hom.hom (v ⊗ₜ[ℂ] x))
    rw [← SymmetricGroup.youngSubgroupInclusion_left]
    change _ = (((Action.res (FGModuleCat ℂ)
      (SymmetricGroup.youngSubgroupInclusion n 2)).obj (spechtModule ξ)).ρ (g, 1)).hom
        (F.hom.hom.hom (v ⊗ₜ[ℂ] x))
    have hF := FDRep.hom_apply_rho F (g, (1 : SymmetricGroup 2)) (v ⊗ₜ[ℂ] x)
    rw [FDRep.outerTensor_ρ_tmul] at hF
    simp only [map_one, Module.End.one_apply] at hF
    change F.hom.hom.hom ((spechtModule μ).ρ g v ⊗ₜ[ℂ] x) =
      (((Action.res (FGModuleCat ℂ)
        (SymmetricGroup.youngSubgroupInclusion n 2)).obj (spechtModule ξ)).ρ (g, 1)).hom
          (F.hom.hom.hom (v ⊗ₜ[ℂ] x)) at hF
    exact hF

theorem outerTensorEval_mem (hc : ∀ y : X, X.ρ (Equiv.swap 0 1) y = c • y)
    (F : FDRep.outerTensor (spechtModule μ) X ⟶
      (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion n 2)).obj
        (spechtModule ξ)) (x : X) :
    outerTensorEval F x ∈ lastAdjacentEigenspace ξ μ c := by
  rw [mem_lastAdjacentEigenspace]
  apply ConcreteCategory.hom_ext
  intro v
  have hF := FDRep.hom_apply_rho F ((1 : SymmetricGroup n), Equiv.swap (0 : Fin 2) 1)
    (v ⊗ₜ[ℂ] x)
  have key : F.hom.hom.hom ((FDRep.outerTensor (spechtModule μ) X).ρ
      ((1 : SymmetricGroup n), Equiv.swap (0 : Fin 2) 1) (v ⊗ₜ[ℂ] x)) =
      c • F.hom.hom.hom (v ⊗ₜ[ℂ] x) := by
    have hL : (FDRep.outerTensor (spechtModule μ) X).ρ
        ((1 : SymmetricGroup n), Equiv.swap (0 : Fin 2) 1) (v ⊗ₜ[ℂ] x) =
        c • (v ⊗ₜ[ℂ] x) := by
      rw [FDRep.outerTensor_ρ_tmul, hc x, map_one, TensorProduct.tmul_smul]
      rfl
    rw [hL]
    exact F.hom.hom.hom.map_smul c (v ⊗ₜ[ℂ] x)
  show (spechtModule ξ).ρ (SymmetricGroup.adjacentTransposition (Fin.last n))
      (F.hom.hom.hom (v ⊗ₜ[ℂ] x)) = c • F.hom.hom.hom (v ⊗ₜ[ℂ] x)
  rw [← SymmetricGroup.youngSubgroupInclusion_right]
  exact hF.symm.trans key

/-- The defining eigenvalue equation, read pointwise. -/
theorem lastAdjacentEigenspace_apply
    {f : spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
      ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ))}
    (hf : f ∈ lastAdjacentEigenspace ξ μ c) (v : spechtModule μ) :
    (spechtModule ξ).ρ (SymmetricGroup.adjacentTransposition (Fin.last n)) (f.hom.hom.hom v) =
      c • f.hom.hom.hom v := by
  rw [mem_lastAdjacentEigenspace] at hf
  exact congrArg (fun g : spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
    ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ)) =>
      g.hom.hom.hom v) hf

/-- A morphism out of `S^μ` on which the last transposition acts by the scalar
of `X` extends to a morphism out of `S^μ ⊠ X`. -/
noncomputable def eigenspaceOuterTensorHom (e : (X : Type) ≃ₗ[ℂ] ℂ)
    (hc : ∀ y : X, X.ρ (Equiv.swap 0 1) y = c • y)
    (f : spechtModule μ ⟶ (SymmetricGroupRepresentation.restriction n).obj
      ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule ξ)))
    (hf : f ∈ lastAdjacentEigenspace ξ μ c) :
    FDRep.outerTensor (spechtModule μ) X ⟶
      (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion n 2)).obj
        (spechtModule ξ) where
  hom := FGModuleCat.ofHom ((TensorProduct.rid ℂ (spechtModule ξ)).toLinearMap ∘ₗ
    TensorProduct.map f.hom.hom.hom e.toLinearMap)
  comm g := by
    obtain ⟨σ, π⟩ := g
    apply FGModuleCat.hom_ext
    refine TensorProduct.ext' fun v x => ?_
    show e (X.ρ π x) • f.hom.hom.hom ((spechtModule μ).ρ σ v) =
      (spechtModule ξ).ρ (SymmetricGroup.youngSubgroupInclusion n 2 (σ, π))
        (e x • f.hom.hom.hom v)
    have hsm : (spechtModule ξ).ρ (SymmetricGroup.youngSubgroupInclusion n 2 (σ, π))
        (e x • f.hom.hom.hom v) = e x • (spechtModule ξ).ρ
          (SymmetricGroup.youngSubgroupInclusion n 2 (σ, π)) (f.hom.hom.hom v) :=
      map_smul _ _ _
    rw [FDRep.hom_apply_rho f σ v, hsm]
    show e (X.ρ π x) •
        (spechtModule ξ).ρ (SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n σ))
          (f.hom.hom.hom v) = _
    rw [← SymmetricGroup.youngSubgroupInclusion_left]
    rcases SymmetricGroup.eq_one_or_swap π with rfl | rfl
    · rw [map_one]
      rfl
    · have hex : e (X.ρ (Equiv.swap (0 : Fin 2) 1) x) = c * e x := by
        rw [hc x, map_smul]
        rfl
      have hmul : SymmetricGroup.youngSubgroupInclusion n 2 (σ, Equiv.swap (0 : Fin 2) 1) =
          SymmetricGroup.youngSubgroupInclusion n 2 (σ, 1) *
            SymmetricGroup.youngSubgroupInclusion n 2 (1, Equiv.swap (0 : Fin 2) 1) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      have hsm' : (spechtModule ξ).ρ (SymmetricGroup.youngSubgroupInclusion n 2 (σ, 1))
          (c • f.hom.hom.hom v) = c • (spechtModule ξ).ρ
            (SymmetricGroup.youngSubgroupInclusion n 2 (σ, 1)) (f.hom.hom.hom v) :=
        map_smul _ _ _
      rw [hex, hmul, map_mul, Module.End.mul_apply,
        SymmetricGroup.youngSubgroupInclusion_right, lastAdjacentEigenspace_apply hf v,
        hsm', smul_smul, mul_comm]

/-- Morphisms out of `S^μ ⊠ X` are exactly the morphisms out of `S^μ` on which
the transposition of the last two labels acts by the scalar of `X`. -/
noncomputable def homOuterTensorLinearEquiv (e : (X : Type) ≃ₗ[ℂ] ℂ)
    (hc : ∀ y : X, X.ρ (Equiv.swap 0 1) y = c • y) :
    (FDRep.outerTensor (spechtModule μ) X ⟶
        (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion n 2)).obj
          (spechtModule ξ)) ≃ₗ[ℂ] lastAdjacentEigenspace ξ μ c where
  toFun F := ⟨outerTensorEval F (e.symm 1), outerTensorEval_mem hc F _⟩
  map_add' F G := by
    apply Subtype.ext
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  map_smul' a F := by
    apply Subtype.ext
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  invFun f := eigenspaceOuterTensorHom e hc f.1 f.2
  left_inv F := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    refine TensorProduct.ext' fun v x => ?_
    show e x • F.hom.hom.hom (v ⊗ₜ[ℂ] (e.symm 1)) = F.hom.hom.hom (v ⊗ₜ[ℂ] x)
    have hx : e x • (e.symm 1 : X) = x := by
      rw [← map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
    calc e x • F.hom.hom.hom (v ⊗ₜ[ℂ] (e.symm 1))
        = F.hom.hom.hom (e x • (v ⊗ₜ[ℂ] (e.symm 1))) := (F.hom.hom.hom.map_smul _ _).symm
      _ = F.hom.hom.hom (v ⊗ₜ[ℂ] (e x • (e.symm 1 : X))) := by rw [TensorProduct.tmul_smul]
      _ = F.hom.hom.hom (v ⊗ₜ[ℂ] x) := by rw [hx]
  right_inv f := by
    apply Subtype.ext
    apply ConcreteCategory.hom_ext
    intro v
    show e (e.symm 1) • f.1.hom.hom.hom v = f.1.hom.hom.hom v
    rw [e.apply_symm_apply, one_smul]

theorem finrank_hom_outerTensor_res (e : (X : Type) ≃ₗ[ℂ] ℂ)
    (hc : ∀ y : X, X.ρ (Equiv.swap 0 1) y = c • y) :
    Module.finrank ℂ (FDRep.outerTensor (spechtModule μ) X ⟶
        (Action.res (FGModuleCat ℂ) (SymmetricGroup.youngSubgroupInclusion n 2)).obj
          (spechtModule ξ)) =
      Module.finrank ℂ (lastAdjacentEigenspace ξ μ c) :=
  (homOuterTensorLinearEquiv e hc).finrank_eq

end Bridge

section Strips

variable {n : ℕ} (μ : YoungDiagramOfSize n) (ξ : YoungDiagramOfSize (n + 2))

/-- The reciprocal of an axial distance of size at least two is neither `1` nor
`-1`. -/
theorem sub_inv_intCast_ne_zero {d : ℤ} (hd : 2 ≤ d.natAbs) {z : ℂ} (hz : z = 1 ∨ z = -1) :
    z - (d : ℂ)⁻¹ ≠ 0 := by
  intro hzero
  have heq : ((d : ℂ))⁻¹ = z := (sub_eq_zero.mp hzero).symm
  have hcast : (d : ℂ) = z⁻¹ := by
    have := congrArg (fun w : ℂ => w⁻¹) heq
    simpa using this
  rcases hz with rfl | rfl
  · have : d = 1 := by exact_mod_cast (by simpa using hcast : (d : ℂ) = 1)
    simp [this] at hd
  · have : d = -1 := by exact_mod_cast (by simpa using hcast : (d : ℂ) = -1)
    simp [this] at hd

open scoped Classical in
/-- The eigenvalues of the last transposition on the multiplicity space of `S^μ`
inside the twice-restricted `S^ξ` split the two-box skew shapes into horizontal
and vertical strips. -/
theorem finrank_lastAdjacentEigenspace_eq :
    Module.finrank ℂ (lastAdjacentEigenspace ξ μ 1) =
        (if IsHorizontalTwoStrip μ ξ then 1 else 0) ∧
      Module.finrank ℂ (lastAdjacentEigenspace ξ μ (-1)) =
        (if IsVerticalTwoStrip μ ξ then 1 else 0) := by
  classical
  by_cases hpath : Nonempty (TwoStepRemovalTo ξ μ)
  · obtain ⟨p⟩ := hpath
    by_cases hsub : ∀ r : TwoStepRemovalTo ξ μ, r = p
    · have hnotswap : ¬ p.tableau.IsAdjacentSwapStandard (Fin.last n) := by
        intro h
        refine p.tableau.largestTwoStepRemovalTo_ne_swapped h (Subtype.ext ?_)
        have h₁ := congrArg Subtype.val (hsub
          ((p.tableau.swappedLargestTwoStepRemovalTo h).cast p.eraseTwoLargestShape_tableau))
        have h₂ := congrArg Subtype.val p.largestTwoStepRemovalTo_tableau
        rw [TwoStepRemovalTo.cast_val] at h₁ h₂
        exact h₂.trans h₁.symm
      have hcells : p.firstCell.1 = p.secondCell.1 ∨ p.firstCell.2 = p.secondCell.2 := by
        by_contra hcon
        exact hnotswap (p.isAdjacentSwapStandard_tableau_iff.mpr
          ⟨fun h => (not_or.mp hcon).1 h.symm, fun h => (not_or.mp hcon).2 h.symm⟩)
      have hself := p.twoStepMultiplicityMatrix_lastAdjacent_self
      rw [finrank_lastAdjacentEigenspace_of_subsingleton p hsub,
        finrank_lastAdjacentEigenspace_of_subsingleton p hsub, hself]
      rcases hcells with hrow | hcol
      · rw [p.axialDistance_tableau_eq_one hrow]
        rw [if_pos (p.isHorizontalTwoStrip_iff.mpr fun hc =>
            p.firstCell_ne_secondCell (Prod.ext hrow hc)),
          if_neg (fun hv => (p.isVerticalTwoStrip_iff.mp hv) hrow)]
        norm_num
      · rw [p.axialDistance_tableau_eq_neg_one hcol]
        rw [if_neg (fun hh => (p.isHorizontalTwoStrip_iff.mp hh) hcol),
          if_pos (p.isVerticalTwoStrip_iff.mpr fun hr =>
            p.firstCell_ne_secondCell (Prod.ext hr hcol))]
        norm_num
    · obtain ⟨q, hq⟩ : ∃ q : TwoStepRemovalTo ξ μ, q ≠ p := by
        by_contra hall
        exact hsub fun r => not_not.mp fun hr => hall ⟨r, hr⟩
      have hswap : p.tableau.IsAdjacentSwapStandard (Fin.last n) := by
        by_contra hcon
        refine hq (p.eq_of_secondCell_le (p.secondCell_le_firstCell ?_) q)
        rcases not_and_or.mp (fun h => hcon (p.isAdjacentSwapStandard_tableau_iff.mpr h)) with h | h
        · exact Or.inl (not_not.mp h).symm
        · exact Or.inr (not_not.mp h).symm
      have hpq : p ≠ q := Ne.symm hq
      obtain ⟨hM₁, hM₂, hM₃⟩ := p.twoStepMultiplicityMatrix_lastAdjacent_of_ne q hpq hswap
      have hself := p.twoStepMultiplicityMatrix_lastAdjacent_self
      have hsq : (twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p) ^ 2 +
          (twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q) ^ 2 = 1 := by
        rw [hself, hM₁]
        exact lastAdjacentTransposition_coefficients_sq_add ξ p.tableau hswap
      have hqq : twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) q q =
          -twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p p := by
        rw [hM₃, hself]
      have hqp : twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) q p =
          twoStepMultiplicityMatrix ξ μ (lastAdjacentTranspositionEndomorphism ξ) p q := by
        rw [hM₂, hM₁]
      have htwo : 2 ≤ (p.tableau.axialDistance (Fin.last n)).natAbs :=
        (p.tableau.isAdjacentSwapStandard_iff_two_le_natAbs (Fin.last n)).mp hswap
      have hstrip := p.isAdjacentSwapStandard_tableau_iff.mp hswap
      constructor
      · rw [finrank_lastAdjacentEigenspace_of_pair p q hpq 1 (by norm_num) hsq hqp hqq
          (by rw [hself]; exact sub_inv_intCast_ne_zero htwo (Or.inl rfl)),
          if_pos (p.isHorizontalTwoStrip_iff.mpr fun h => hstrip.2 h.symm)]
      · rw [finrank_lastAdjacentEigenspace_of_pair p q hpq (-1) (by norm_num) hsq hqp hqq
          (by rw [hself]; exact sub_inv_intCast_ne_zero htwo (Or.inr rfl)),
          if_pos (p.isVerticalTwoStrip_iff.mpr fun h => hstrip.1 h.symm)]
  · have hempty : IsEmpty (TwoStepRemovalTo ξ μ) := not_nonempty_iff.mp hpath
    have hnotle : ¬ (μ.val ≤ ξ.val) := fun hle => hpath (nonempty_twoStepRemovalTo μ ξ hle)
    rw [finrank_lastAdjacentEigenspace_of_isEmpty hempty,
      finrank_lastAdjacentEigenspace_of_isEmpty hempty,
      if_neg (fun h => hnotle h.1), if_neg (fun h => hnotle h.1)]
    exact ⟨rfl, rfl⟩

end Strips
