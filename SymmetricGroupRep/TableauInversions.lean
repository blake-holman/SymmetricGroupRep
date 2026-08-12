import SymmetricGroupRep.TableauContent

/-! # Inversions of a standard tableau relative to reading order

Every standard tableau is obtained from the reading tableau by a permutation of
the labels, and the number of inverted pairs of that permutation is a length
function: an admissible adjacent swap changes it by at most one, and a tableau
other than the reading tableau always admits an adjacent swap that decreases it.
That is what makes the induction behind Young's orthogonal form terminate.
-/

/-- The permutation carrying the reading tableau to `T`. -/
noncomputable def StandardYoungTableau.readingPermutation {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : SymmetricGroup n :=
  (readingTableau μ).entry.symm.trans T.entry

/-- The pairs of labels that a permutation inverts. -/
def inversionPairs {n : ℕ} (σ : SymmetricGroup n) : Finset (Fin n × Fin n) :=
  (transpositionPairs n).filter fun p => σ p.2 < σ p.1

@[simp]
theorem mem_inversionPairs {n : ℕ} {σ : SymmetricGroup n} {p : Fin n × Fin n} :
    p ∈ inversionPairs σ ↔ p.1 < p.2 ∧ σ p.2 < σ p.1 := by
  simp [inversionPairs]

/-- The number of pairs of labels that a standard tableau inverts. -/
noncomputable def StandardYoungTableau.inversions {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : ℕ :=
  (inversionPairs T.readingPermutation).card

/-- A permutation inverting nothing is the identity. -/
theorem eq_one_of_inversionPairs_eq_empty {n : ℕ} {σ : SymmetricGroup n}
    (h : inversionPairs σ = ∅) : σ = 1 := by
  have hmono : StrictMono σ := by
    intro x y hxy
    by_contra hlt
    exact absurd (Finset.eq_empty_iff_forall_notMem.mp h (x, y)
      (mem_inversionPairs.mpr ⟨hxy, lt_of_le_of_ne (not_lt.mp hlt)
        fun hcontra => absurd (σ.injective hcontra) hxy.ne'⟩)) not_false
  have hsum : ∑ x : Fin n, ((σ x : ℕ)) = ∑ x : Fin n, (x : ℕ) :=
    Equiv.sum_comp σ (fun y => (y : ℕ))
  have hle : ∀ x : Fin n, (x : ℕ) ≤ (σ x : ℕ) := fun x => hmono.le_apply
  have hpoint := (Finset.sum_eq_sum_iff_of_le fun x _ => hle x).mp hsum.symm
  exact Equiv.ext fun x => Fin.ext (hpoint x (Finset.mem_univ x)).symm

namespace StandardYoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ)

theorem readingPermutation_inv_apply (k : Fin n) :
    ((T.readingPermutation⁻¹ k : Fin n) : ℕ) = μ.val.readingIndex (T.position k) :=
  rfl

theorem readingPermutation_readingTableau : (readingTableau μ).readingPermutation = 1 :=
  Equiv.symm_trans_self _

theorem eq_readingTableau_of_inversions_eq_zero (h : T.inversions = 0) :
    T = readingTableau μ := by
  have hone : T.readingPermutation = 1 :=
    eq_one_of_inversionPairs_eq_empty (Finset.card_eq_zero.mp h)
  refine StandardYoungTableau.ext (Equiv.ext fun c => ?_)
  have := congrArg (fun σ : SymmetricGroup n => σ ((readingTableau μ).entry c)) hone
  simpa [readingPermutation] using this

theorem pos_of_inversions_ne_zero (h : T.inversions ≠ 0) : 0 < n := by
  obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp h
  exact Fin.pos_iff_nonempty.mpr ⟨p.1⟩

end StandardYoungTableau

section Adjacent

variable {n : ℕ} (σ : SymmetricGroup (n + 1)) (i : Fin n)

/-- Only one pair is created by composing with an adjacent transposition. -/
theorem inversionPairs_adjacent_subset_insert :
    inversionPairs (SymmetricGroup.adjacentTransposition i * σ) ⊆
      insert (σ⁻¹ (Fin.castSucc i), σ⁻¹ i.succ) (inversionPairs σ) := by
  intro p hp
  rw [mem_inversionPairs] at hp
  by_cases hmem : σ p.2 < σ p.1
  · exact Finset.mem_insert_of_mem (mem_inversionPairs.mpr ⟨hp.1, hmem⟩)
  · have hlt : σ p.1 < σ p.2 :=
      lt_of_le_of_ne (not_lt.mp hmem) fun hcontra => absurd (σ.injective hcontra) hp.1.ne
    have hexc : σ p.1 = Fin.castSucc i ∧ σ p.2 = i.succ := by
      by_contra hne
      exact absurd (SymmetricGroup.adjacentTransposition_lt i hlt hne) (asymm hp.2)
    have hp1 : p.1 = σ⁻¹ (Fin.castSucc i) := by rw [← hexc.1]; simp
    have hp2 : p.2 = σ⁻¹ i.succ := by rw [← hexc.2]; simp
    rw [show p = (σ⁻¹ (Fin.castSucc i), σ⁻¹ i.succ) from Prod.ext hp1 hp2]
    exact Finset.mem_insert_self _ _

/-- At a descent, composing with the adjacent transposition only destroys
inversions. -/
theorem inversionPairs_adjacent_subset (hdesc : σ⁻¹ i.succ < σ⁻¹ (Fin.castSucc i)) :
    inversionPairs (SymmetricGroup.adjacentTransposition i * σ) ⊆ inversionPairs σ := by
  intro p hp
  have hins := inversionPairs_adjacent_subset_insert σ i hp
  rcases Finset.mem_insert.mp hins with heq | hmem
  · rw [mem_inversionPairs] at hp
    rw [heq] at hp
    exact absurd hp.1 (asymm hdesc)
  · exact hmem

theorem mem_inversionPairs_of_descent (hdesc : σ⁻¹ i.succ < σ⁻¹ (Fin.castSucc i)) :
    (σ⁻¹ i.succ, σ⁻¹ (Fin.castSucc i)) ∈ inversionPairs σ := by
  refine mem_inversionPairs.mpr ⟨hdesc, ?_⟩
  have hinv : ∀ x, σ (σ⁻¹ x) = x := fun x => (Equiv.apply_eq_iff_eq_symm_apply σ).mpr rfl
  show σ (σ⁻¹ (Fin.castSucc i)) < σ (σ⁻¹ i.succ)
  rw [hinv, hinv]
  exact Fin.castSucc_lt_succ

theorem notMem_inversionPairs_adjacent_of_descent :
    (σ⁻¹ i.succ, σ⁻¹ (Fin.castSucc i)) ∉
      inversionPairs (SymmetricGroup.adjacentTransposition i * σ) := by
  intro hmem
  rw [mem_inversionPairs] at hmem
  have h : SymmetricGroup.adjacentTransposition i (σ (σ⁻¹ (Fin.castSucc i))) <
      SymmetricGroup.adjacentTransposition i (σ (σ⁻¹ i.succ)) := hmem.2
  have hinv : ∀ x, σ (σ⁻¹ x) = x := fun x => (Equiv.apply_eq_iff_eq_symm_apply σ).mpr rfl
  rw [hinv, hinv, SymmetricGroup.adjacentTransposition_apply_left,
    SymmetricGroup.adjacentTransposition_apply_right] at h
  exact absurd h (asymm Fin.castSucc_lt_succ)

theorem card_inversionPairs_adjacent_lt (hdesc : σ⁻¹ i.succ < σ⁻¹ (Fin.castSucc i)) :
    (inversionPairs (SymmetricGroup.adjacentTransposition i * σ)).card <
      (inversionPairs σ).card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset
    (inversionPairs_adjacent_subset σ i hdesc)).mpr
      ⟨_, mem_inversionPairs_of_descent σ i hdesc,
        notMem_inversionPairs_adjacent_of_descent σ i⟩)

theorem inv_adjacent_mul_apply (x : Fin (n + 1)) :
    (SymmetricGroup.adjacentTransposition i * σ)⁻¹ x =
      σ⁻¹ (SymmetricGroup.adjacentTransposition i x) := by
  rw [mul_inv_rev, Equiv.Perm.mul_apply]
  congr 1

/-- At an ascent, composing with the adjacent transposition creates an
inversion. -/
theorem card_inversionPairs_lt_adjacent (hasc : σ⁻¹ (Fin.castSucc i) < σ⁻¹ i.succ) :
    (inversionPairs σ).card <
      (inversionPairs (SymmetricGroup.adjacentTransposition i * σ)).card := by
  have hdesc : (SymmetricGroup.adjacentTransposition i * σ)⁻¹ i.succ <
      (SymmetricGroup.adjacentTransposition i * σ)⁻¹ (Fin.castSucc i) := by
    rw [inv_adjacent_mul_apply, inv_adjacent_mul_apply,
      SymmetricGroup.adjacentTransposition_apply_left,
      SymmetricGroup.adjacentTransposition_apply_right]
    exact hasc
  have hcancel : SymmetricGroup.adjacentTransposition i *
      (SymmetricGroup.adjacentTransposition i * σ) = σ := by
    rw [← mul_assoc, adjacentTransposition_mul_self, one_mul]
  have := card_inversionPairs_adjacent_lt (SymmetricGroup.adjacentTransposition i * σ) i hdesc
  rwa [hcancel] at this

theorem exists_descent_of_ne_one (h : σ ≠ 1) :
    ∃ i : Fin n, σ⁻¹ i.succ < σ⁻¹ (Fin.castSucc i) := by
  by_contra hcontra
  push Not at hcontra
  have hmono : StrictMono (fun x : Fin (n + 1) => σ⁻¹ x) :=
    Fin.strictMono_iff_lt_succ.mpr fun j =>
      lt_of_le_of_ne (hcontra j) fun hcontra' =>
        absurd (σ⁻¹.injective hcontra') (Fin.castSucc_lt_succ (i := j)).ne
  have hsum : ∑ x : Fin (n + 1), ((σ⁻¹ x : ℕ)) = ∑ x : Fin (n + 1), (x : ℕ) :=
    Equiv.sum_comp σ⁻¹ (fun y => (y : ℕ))
  have hle : ∀ x : Fin (n + 1), (x : ℕ) ≤ (σ⁻¹ x : ℕ) := fun x => hmono.le_apply
  have hpoint := (Finset.sum_eq_sum_iff_of_le fun x _ => hle x).mp hsum.symm
  refine h (inv_eq_one.mp (Equiv.ext fun x => Fin.ext ?_))
  exact (hpoint x (Finset.mem_univ x)).symm

end Adjacent

namespace StandardYoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau μ) (i : Fin n)

theorem readingPermutation_swapAdjacent (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).readingPermutation =
      SymmetricGroup.adjacentTransposition i * T.readingPermutation :=
  Equiv.ext fun _ => rfl

theorem inversions_swapAdjacent_le (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).inversions ≤ T.inversions + 1 := by
  classical
  rw [inversions, readingPermutation_swapAdjacent]
  refine le_trans (Finset.card_le_card
    (inversionPairs_adjacent_subset_insert T.readingPermutation i)) ?_
  exact (Finset.card_insert_le _ _).trans_eq rfl

/-- A descent in reading order is an admissible adjacent swap. -/
theorem isAdjacentSwapStandard_of_descent
    (hdesc : T.readingPermutation⁻¹ i.succ < T.readingPermutation⁻¹ (Fin.castSucc i)) :
    T.IsAdjacentSwapStandard i := by
  have hindex : μ.val.readingIndex (T.position i.succ) <
      μ.val.readingIndex (T.position (Fin.castSucc i)) := by
    have := hdesc
    rw [Fin.lt_def, T.readingPermutation_inv_apply, T.readingPermutation_inv_apply] at this
    exact this
  refine (T.isAdjacentSwapStandard_iff i).mpr ⟨fun hrow => ?_, fun hcol => ?_⟩
  · have hlt := T.column_lt_column_of_row_eq hrow Fin.castSucc_lt_succ
    exact absurd (YoungDiagram.readingIndex_lt_readingIndex (T.position_mem _)
      (Or.inr ⟨hrow, hlt⟩)) (asymm hindex)
  · have hlt := T.row_lt_row_of_column_eq hcol Fin.castSucc_lt_succ
    exact absurd (YoungDiagram.readingIndex_lt_readingIndex (T.position_mem _)
      (Or.inl hlt)) (asymm hindex)

theorem inversions_swapAdjacent_lt_or_lt (h : T.IsAdjacentSwapStandard i) :
    (T.swapAdjacent i h).inversions < T.inversions ∨
      T.inversions < (T.swapAdjacent i h).inversions := by
  rw [inversions, inversions, readingPermutation_swapAdjacent]
  rcases lt_trichotomy (T.readingPermutation⁻¹ i.succ)
    (T.readingPermutation⁻¹ (Fin.castSucc i)) with hlt | heq | hgt
  · exact Or.inl (card_inversionPairs_adjacent_lt T.readingPermutation i hlt)
  · exact absurd (T.readingPermutation⁻¹.injective heq) (Fin.castSucc_lt_succ (i := i)).ne'
  · exact Or.inr (card_inversionPairs_lt_adjacent T.readingPermutation i hgt)

/-- **A tableau other than the reading tableau admits a descending adjacent
swap.** -/
theorem exists_swapAdjacent_inversions_lt (hT : T.inversions ≠ 0) :
    ∃ (i : Fin n) (h : T.IsAdjacentSwapStandard i),
      (T.swapAdjacent i h).inversions < T.inversions := by
  classical
  have hne : T.readingPermutation ≠ 1 := by
    intro hone
    refine hT ?_
    rw [inversions, hone, Finset.card_eq_zero]
    refine Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    rw [mem_inversionPairs] at hp
    exact absurd hp.1 (asymm hp.2)
  obtain ⟨j, hj⟩ := exists_descent_of_ne_one T.readingPermutation hne
  refine ⟨j, T.isAdjacentSwapStandard_of_descent j hj, ?_⟩
  rw [inversions, inversions, readingPermutation_swapAdjacent]
  exact card_inversionPairs_adjacent_lt T.readingPermutation j hj

end StandardYoungTableau
