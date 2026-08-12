import SymmetricGroupRep.MultiplicitySpaces
import SymmetricGroupRep.Orthogonal

/-! # The coherent basis under two-step branching -/

/- `spechtModule` is now a concrete definition rather than an axiom, so terms
mentioning it carry real definitional content and `whnf` has more work to do.
Two proofs below exceed the default budget as a result. This raises the limit
only; it is a resource bound, not an assumption. The same device is already used
in `Induction.lean` and `PaddedHookBounds.lean`. -/
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Classical

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

private theorem singleton_finset_eq_or_eq_of_subset_card_two
    {alpha : Type} [DecidableEq alpha] (A B C D : Finset alpha)
    (hA : A.card = 1) (hB : B.card = 1) (hC : C.card = 1)
    (hD : D.card = 2) (hAD : A ⊆ D) (hBD : B ⊆ D) (hCD : C ⊆ D)
    (hne : A ≠ B) : C = A ∨ C = B := by
  rcases Finset.card_eq_one.mp hA with ⟨a, rfl⟩
  rcases Finset.card_eq_one.mp hB with ⟨b, rfl⟩
  rcases Finset.card_eq_one.mp hC with ⟨c, rfl⟩
  rcases Finset.card_eq_two.mp hD with ⟨x, y, hxy, rfl⟩
  simp only [Finset.singleton_subset_iff, Finset.mem_insert,
    Finset.mem_singleton] at hAD hBD hCD
  simp only [Finset.singleton_inj]
  aesop

namespace TwoStepRemovalTo

/-- Transport a two-step path along an equality of its endpoint. -/
def cast {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu xi : YoungDiagramOfSize n} (h : nu = xi)
    (p : TwoStepRemovalTo mu nu) : TwoStepRemovalTo mu xi := by
  subst xi
  exact p

@[simp]
theorem cast_val {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu xi : YoungDiagramOfSize n} (h : nu = xi)
    (p : TwoStepRemovalTo mu nu) : (p.cast h).val = p.val := by
  subst xi
  rfl

/-- The cell added to the endpoint to form the intermediate diagram of a
two-step removal path. -/
def middleDifference {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu : YoungDiagramOfSize n} (p : TwoStepRemovalTo mu nu) :
    Finset (ℕ × ℕ) :=
  p.val.1.val.val.cells \ nu.val.cells

theorem endpoint_le_middle {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu : YoungDiagramOfSize n} (p : TwoStepRemovalTo mu nu) :
    nu.val ≤ p.val.1.val.val := by
  have hendpoint : p.val.2.val.val = nu.val := congrArg Subtype.val p.property
  exact Eq.mp
    (congrArg (fun xi : YoungDiagram => xi ≤ p.val.1.val.val) hendpoint)
    p.val.2.property

@[simp]
theorem middleDifference_card {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu : YoungDiagramOfSize n} (p : TwoStepRemovalTo mu nu) :
    p.middleDifference.card = 1 := by
  simpa [middleDifference] using
    YoungDiagramOfSize.card_sdiff nu p.val.1.val p.endpoint_le_middle

theorem middleDifference_subset {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu : YoungDiagramOfSize n} (p : TwoStepRemovalTo mu nu) :
    p.middleDifference ⊆ mu.val.cells \ nu.val.cells := by
  intro cell hcell
  change cell ∈ p.val.1.val.val.cells \ nu.val.cells at hcell
  rw [Finset.mem_sdiff] at hcell ⊢
  exact ⟨YoungDiagram.cells_subset_iff.mpr p.val.1.property hcell.1, hcell.2⟩

theorem middleDifference_injective {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} {nu : YoungDiagramOfSize n} :
    Function.Injective (middleDifference (mu := mu) (nu := nu)) := by
  intro p q hpq
  have hmid : p.val.1 = q.val.1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply YoungDiagram.ext
    have hpSub : nu.val.cells ⊆ p.val.1.val.val.cells :=
      YoungDiagram.cells_subset_iff.mp p.endpoint_le_middle
    have hqSub : nu.val.cells ⊆ q.val.1.val.val.cells :=
      YoungDiagram.cells_subset_iff.mp q.endpoint_le_middle
    calc
      p.val.1.val.val.cells =
          (p.val.1.val.val.cells \ nu.val.cells) ∪ nu.val.cells :=
        (Finset.sdiff_union_of_subset hpSub).symm
      _ = (q.val.1.val.val.cells \ nu.val.cells) ∪ nu.val.cells := by
        rw [show p.val.1.val.val.cells \ nu.val.cells =
            q.val.1.val.val.cells \ nu.val.cells by exact hpq]
      _ = q.val.1.val.val.cells := Finset.sdiff_union_of_subset hqSub
  apply Subtype.ext
  apply Sigma.ext hmid
  apply (Subtype.heq_iff_coe_eq (fun xi => by rw [hmid])).2
  exact p.property.trans q.property.symm

/-- A two-box skew difference has at most two removal paths. -/
theorem eq_or_eq_of_ne {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    {nu : YoungDiagramOfSize n} (p q : TwoStepRemovalTo mu nu) (hne : p ≠ q)
    (r : TwoStepRemovalTo mu nu) : r = p ∨ r = q := by
  have hdiff : p.middleDifference ≠ q.middleDifference :=
    fun h => hne (middleDifference_injective h)
  have hr : r.middleDifference = p.middleDifference ∨
      r.middleDifference = q.middleDifference := by
    apply singleton_finset_eq_or_eq_of_subset_card_two
      p.middleDifference q.middleDifference r.middleDifference
      (mu.val.cells \ nu.val.cells)
    · exact p.middleDifference_card
    · exact q.middleDifference_card
    · exact r.middleDifference_card
    · have hnu : nu.val ≤ mu.val := p.endpoint_le_middle.trans p.val.1.property
      simpa using YoungDiagramOfSize.card_sdiff nu mu hnu
    · exact p.middleDifference_subset
    · exact q.middleDifference_subset
    · exact r.middleDifference_subset
    · exact hdiff
  rcases hr with hr | hr
  · exact Or.inl (middleDifference_injective (a₁ := r) (a₂ := p) hr)
  · exact Or.inr (middleDifference_injective (a₁ := r) (a₂ := q) hr)

end TwoStepRemovalTo

/-- Coherent basis vectors transport naturally when their diagram index is
transported along an equality. -/
theorem spechtOrthogonalBasis_cast {n : ℕ} {nu xi : YoungDiagramOfSize n}
    (h : nu = xi) (T : StandardYoungTableau nu) :
    h ▸ spechtOrthogonalBasis nu T =
      spechtOrthogonalBasis xi (h ▸ T) := by
  subst xi
  rfl

/-- Branching inclusion is unchanged by transporting its endpoint index. -/
theorem twoStepBranchingInclusion_cast {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) {nu xi : YoungDiagramOfSize n}
    (h : nu = xi) (p : TwoStepRemovalTo mu nu) (v : spechtModule nu) :
    (twoStepBranchingInclusion mu xi (p.cast h)).hom.hom.hom (h ▸ v) =
      (twoStepBranchingInclusion mu nu p).hom.hom.hom v := by
  subst xi
  rfl

/-- Branching projection is unchanged by transporting its endpoint index. -/
theorem twoStepBranchingProjection_cast {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) {nu xi : YoungDiagramOfSize n}
    (h : nu = xi) (p : TwoStepRemovalTo mu nu) (v : spechtModule mu) :
    h ▸ (twoStepBranchingProjection mu nu p).hom.hom.hom v =
      (twoStepBranchingProjection mu xi (p.cast h)).hom.hom.hom v := by
  subst xi
  rfl

namespace StandardYoungTableau

/-- The cell carrying the second-largest entry. -/
def secondLargestCell {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    (T : StandardYoungTableau mu) : ↥mu.val.cells :=
  T.entry.symm (Fin.castSucc (Fin.last n))

/-- After deleting the largest entry, the new largest cell is the original
second-largest cell. -/
theorem remainingCellEquiv_restrictLargest_largestCell {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu) :
    (T.remainingCellEquiv T.restrictLargest.largestCell).1 =
      T.secondLargestCell := by
  apply T.entry.injective
  apply Fin.ext
  have h := T.restrictedEntryEquiv_val T.restrictLargest.largestCell
  have hlargest :
      T.restrictedEntryEquiv T.restrictLargest.largestCell = Fin.last n :=
    T.restrictLargest.entry_largestCell
  rw [congrArg Fin.val hlargest] at h
  rw [secondLargestCell, T.entry.apply_symm_apply]
  exact h.symm

/-- The path obtained by deleting the two largest tableau entries in order. -/
def largestTwoStepRemoval {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    (T : StandardYoungTableau mu) : TwoStepRemoval mu :=
  ⟨T.largestRemoval, T.restrictLargest.largestRemoval⟩

/-- The shape obtained by deleting the two largest tableau entries. -/
def eraseTwoLargestShape {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    (T : StandardYoungTableau mu) : YoungDiagramOfSize n :=
  T.restrictLargest.eraseLargestShape

/-- Deleting the two largest entries erases their two original cells. -/
theorem eraseTwoLargestShape_cells {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu) :
    T.eraseTwoLargestShape.val.cells =
      (mu.val.cells.erase T.largestCell.val).erase T.secondLargestCell.val := by
  have hcell : T.restrictLargest.largestCell.val = T.secondLargestCell.val := by
    have h := congrArg Subtype.val
      (T.remainingCellEquiv_restrictLargest_largestCell)
    simpa [StandardYoungTableau.remainingCellEquiv] using h
  unfold eraseTwoLargestShape eraseLargestShape eraseLargestDiagram
  change (mu.val.cells.erase T.largestCell.val).erase
      T.restrictLargest.largestCell.val = _
  rw [hcell]

/-- Swapping the two largest entries exchanges their cells. -/
theorem largestCell_swapAdjacent_last {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (T.swapAdjacent (Fin.last n) h).largestCell = T.secondLargestCell := by
  simp [largestCell, secondLargestCell, swapAdjacent, swappedEntry]

/-- Swapping the two largest entries exchanges their cells. -/
theorem secondLargestCell_swapAdjacent_last {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (T.swapAdjacent (Fin.last n) h).secondLargestCell = T.largestCell := by
  simp [largestCell, secondLargestCell, swapAdjacent, swappedEntry]

/-- Swapping the two largest entries leaves the shape below them unchanged. -/
theorem eraseTwoLargestShape_swapAdjacent_last {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (T.swapAdjacent (Fin.last n) h).eraseTwoLargestShape =
      T.eraseTwoLargestShape := by
  apply Subtype.ext
  apply YoungDiagram.ext
  rw [eraseTwoLargestShape_cells, eraseTwoLargestShape_cells,
    largestCell_swapAdjacent_last, secondLargestCell_swapAdjacent_last]
  ext cell
  simp [and_left_comm]

/-- The tableau obtained by deleting the two largest entries. -/
def restrictTwoLargest {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    (T : StandardYoungTableau mu) : StandardYoungTableau T.eraseTwoLargestShape :=
  T.restrictLargest.restrictLargest

/-- Regard a cell remaining below the two largest entries as a cell of the
original diagram. -/
def originalCellOfRestrictTwoLargest {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (cell : ↥T.eraseTwoLargestShape.val.cells) : ↥mu.val.cells :=
  ⟨cell.val, by
    let c : ℕ × ℕ := cell.val
    have hcell : c ∈ T.eraseTwoLargestShape.val.cells := by
      simpa [c] using cell.property
    rw [T.eraseTwoLargestShape_cells] at hcell
    simpa [c] using (Finset.mem_erase.mp
      (Finset.mem_erase.mp hcell).2).2⟩

/-- Transport a diagram cell backward along an equality of shapes. -/
def cellCast {n : ℕ} {mu nu : YoungDiagramOfSize n} (h : mu = nu)
    (cell : ↥nu.val.cells) : ↥mu.val.cells := by
  subst nu
  exact cell

@[simp]
theorem cellCast_val {n : ℕ} {mu nu : YoungDiagramOfSize n} (h : mu = nu)
    (cell : ↥nu.val.cells) : (cellCast h cell).val = cell.val := by
  subst nu
  rfl

/-- Transporting a tableau transports entry evaluation through the matching
cell cast. -/
theorem transport_entry_val {n : ℕ} {mu nu : YoungDiagramOfSize n}
    (h : mu = nu) (T : StandardYoungTableau mu) (cell : ↥nu.val.cells) :
    ((h ▸ T).entry cell).val = (T.entry (cellCast h cell)).val := by
  subst nu
  rfl

/-- Restricting twice preserves the labels of every remaining cell. -/
theorem restrictTwoLargest_entry_val {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (cell : ↥T.eraseTwoLargestShape.val.cells) :
    (T.restrictTwoLargest.entry cell).val =
      (T.entry (T.originalCellOfRestrictTwoLargest cell)).val := by
  calc
    (T.restrictTwoLargest.entry cell).val =
        (T.restrictLargest.entry
          ((T.restrictLargest.remainingCellEquiv cell).1)).val :=
      T.restrictLargest.restrictedEntryEquiv_val cell
    _ = (T.entry
          ((T.remainingCellEquiv
            ((T.restrictLargest.remainingCellEquiv cell).1)).1)).val :=
      T.restrictedEntryEquiv_val
        ((T.restrictLargest.remainingCellEquiv cell).1)
    _ = (T.entry (T.originalCellOfRestrictTwoLargest cell)).val := by
      congr 2

/-- Swapping the two largest entries does not change the tableau below them. -/
theorem restrictTwoLargest_swapAdjacent_last {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (eraseTwoLargestShape_swapAdjacent_last T h) ▸
        (T.swapAdjacent (Fin.last n) h).restrictTwoLargest =
      T.restrictTwoLargest := by
  let U := T.swapAdjacent (Fin.last n) h
  let hs : U.eraseTwoLargestShape = T.eraseTwoLargestShape :=
    eraseTwoLargestShape_swapAdjacent_last T h
  change hs ▸ U.restrictTwoLargest = T.restrictTwoLargest
  apply StandardYoungTableau.ext
  apply Equiv.ext
  intro cell
  apply Fin.ext
  let cellU := cellCast hs cell
  let originalU := U.originalCellOfRestrictTwoLargest cellU
  let originalT := T.originalCellOfRestrictTwoLargest cell
  have horiginal : originalU = originalT := by
    apply Subtype.ext
    simp [originalU, originalT, cellU, originalCellOfRestrictTwoLargest]
  have hlt : (T.entry originalT).val < n := by
    rw [← T.restrictTwoLargest_entry_val cell]
    exact (T.restrictTwoLargest.entry cell).isLt
  have hleft : T.entry originalT ≠ Fin.castSucc (Fin.last n) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_last]
    omega
  have hright : T.entry originalT ≠ (Fin.last n).succ := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_succ, Fin.val_last]
    omega
  calc
    ((hs ▸ U.restrictTwoLargest).entry cell).val =
        (U.restrictTwoLargest.entry cellU).val :=
      transport_entry_val hs U.restrictTwoLargest cell
    _ = (U.entry originalU).val := U.restrictTwoLargest_entry_val cellU
    _ = (T.entry originalT).val := by
      rw [horiginal]
      change
        ((Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last n).succ)
          (T.entry originalT)).val = (T.entry originalT).val
      rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
    _ = (T.restrictTwoLargest.entry cell).val :=
      (T.restrictTwoLargest_entry_val cell).symm

/-- The two-step removal path selected by a tableau, indexed by its endpoint. -/
def largestTwoStepRemovalTo {n : ℕ} {mu : YoungDiagramOfSize (n + 2)}
    (T : StandardYoungTableau mu) : TwoStepRemovalTo mu T.eraseTwoLargestShape :=
  ⟨T.largestTwoStepRemoval, rfl⟩

/-- The other two-step path obtained by swapping the two largest entries. -/
def swappedLargestTwoStepRemovalTo {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    TwoStepRemovalTo mu T.eraseTwoLargestShape :=
  ⟨(T.swapAdjacent (Fin.last n) h).largestTwoStepRemoval,
    eraseTwoLargestShape_swapAdjacent_last T h⟩

/-- The largest and second-largest entries occupy different cells. -/
theorem largestCell_ne_secondLargestCell {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu) :
    T.largestCell ≠ T.secondLargestCell := by
  intro heq
  have hentry := congrArg T.entry heq
  have hval := congrArg Fin.val hentry
  simp [largestCell, secondLargestCell] at hval

/-- Swapping the two largest entries changes the first intermediate shape. -/
theorem eraseLargestShape_swapAdjacent_last_ne {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (T.swapAdjacent (Fin.last n) h).eraseLargestShape ≠
      T.eraseLargestShape := by
  intro hshape
  have hswapCells :
      (T.swapAdjacent (Fin.last n) h).eraseLargestShape.val.cells =
        mu.val.cells.erase T.secondLargestCell.val := by
    change mu.val.cells.erase
        (T.swapAdjacent (Fin.last n) h).largestCell.val = _
    rw [congrArg Subtype.val (largestCell_swapAdjacent_last T h)]
  have hmem : T.largestCell.val ∈
      (T.swapAdjacent (Fin.last n) h).eraseLargestShape.val.cells := by
    rw [hswapCells]
    exact Finset.mem_erase.mpr
      ⟨fun heq => T.largestCell_ne_secondLargestCell (Subtype.ext heq),
        T.largestCell.property⟩
  rw [hshape] at hmem
  have hnot : T.largestCell.val ∉ T.eraseLargestShape.val.cells := by
    change T.largestCell.val ∉ mu.val.cells.erase T.largestCell.val
    simp
  exact hnot hmem

/-- An admissible swap of the two largest entries selects the other path. -/
theorem largestTwoStepRemovalTo_ne_swapped {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    T.largestTwoStepRemovalTo ≠ T.swappedLargestTwoStepRemovalTo h := by
  intro hpath
  have hfirst := congrArg (fun p : TwoStepRemoval mu => p.1)
    (congrArg Subtype.val hpath)
  exact T.eraseLargestShape_swapAdjacent_last_ne h
    (congrArg (fun nu : OneBoxRemoval mu => nu.val) hfirst.symm)

end StandardYoungTableau

/-- The transposition of the last two labels commutes with the copy of
`S_n` fixing those labels. -/
theorem lastAdjacentTransposition_commutes_doubleInclusion {n : ℕ}
    (g : SymmetricGroup n) :
    SymmetricGroup.adjacentTransposition (Fin.last n) *
        SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n g) =
      SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n g) *
        SymmetricGroup.adjacentTransposition (Fin.last n) := by
  apply Equiv.ext
  intro j
  let s := SymmetricGroup.adjacentTransposition (Fin.last n)
  let gfull := SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n g)
  change s (gfull j) = gfull (s j)
  have houter_apply (y : Fin (n + 1)) :
      gfull (Fin.castLE (Nat.le_succ (n + 1)) y) =
        Fin.castLE (Nat.le_succ (n + 1)) (SymmetricGroup.inclusion n g y) := by
    dsimp [gfull]
    simpa [SymmetricGroup.inclusion] using
      (SymmetricGroup.inclusionOfLE_apply_castLE (Nat.le_succ (n + 1))
        (SymmetricGroup.inclusion n g) y)
  have hinner_apply (z : Fin n) :
      SymmetricGroup.inclusion n g (Fin.castLE (Nat.le_succ n) z) =
        Fin.castLE (Nat.le_succ n) (g z) := by
    simpa [SymmetricGroup.inclusion] using
      (SymmetricGroup.inclusionOfLE_apply_castLE (Nat.le_succ n) g z)
  have hinner_of_ge (y : Fin (n + 1)) (hy : n ≤ y.val) :
      SymmetricGroup.inclusion n g y = y := by
    simpa [SymmetricGroup.inclusion] using
      (SymmetricGroup.inclusionOfLE_apply_of_le (Nat.le_succ n) g y hy)
  have hs_of_lt (x : Fin (n + 2)) (hx : x.val < n) : s x = x := by
    apply SymmetricGroup.adjacentTransposition_apply_of_ne
    · apply Fin.ne_of_val_ne
      simp
      omega
    · apply Fin.ne_of_val_ne
      simp
      omega
  have hg_of_ge (x : Fin (n + 2)) (hx : n ≤ x.val) : gfull x = x := by
    by_cases houter : x.val < n + 1
    · let y : Fin (n + 1) := ⟨x.val, houter⟩
      have hxy : x = Fin.castLE (Nat.le_succ (n + 1)) y := by
        apply Fin.ext
        rfl
      rw [hxy, houter_apply, hinner_of_ge _ hx]
    · exact SymmetricGroup.inclusionOfLE_apply_of_le _ _ _
        (Nat.le_of_not_gt houter)
  by_cases hj : j.val < n
  · let j0 : Fin n := ⟨j.val, hj⟩
    have hjcast : j = Fin.castLE (Nat.le_succ (n + 1))
        (Fin.castLE (Nat.le_succ n) j0) := by
      apply Fin.ext
      rfl
    have hgval : (gfull j).val < n := by
      rw [hjcast, houter_apply, hinner_apply]
      exact (g j0).isLt
    rw [hs_of_lt j hj, hs_of_lt (gfull j) hgval]
  · have hjcases :
        j = Fin.castSucc (Fin.last n) ∨ j = (Fin.last n).succ := by
      by_cases heq : j.val = n
      · left
        apply Fin.ext
        simpa using heq
      · right
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_last]
        omega
    rcases hjcases with rfl | rfl
    · rw [hg_of_ge _ (by simp),
        SymmetricGroup.adjacentTransposition_apply_left]
      rw [hg_of_ge _ (by simp)]
    · rw [hg_of_ge _ (by simp),
        SymmetricGroup.adjacentTransposition_apply_right]
      rw [hg_of_ge _ (by simp)]

/-- The action of the last adjacent transposition, regarded as an
endomorphism after restricting past the last two labels. -/
noncomputable def lastAdjacentTranspositionEndomorphism {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj
          (spechtModule mu)) ⟶
      (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj
          (spechtModule mu)) where
  hom := FGModuleCat.ofHom
    ((spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n)))
  comm g := by
    apply FGModuleCat.hom_ext
    simp only [FGModuleCat.hom_hom_comp, Action.res_obj_ρ]
    change
      (spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n)) *
          (spechtModule mu).ρ
            (SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n g)) =
        (spechtModule mu).ρ
            (SymmetricGroup.inclusion (n + 1) (SymmetricGroup.inclusion n g)) *
          (spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n))
    rw [← (spechtModule mu).ρ.map_mul, ← (spechtModule mu).ρ.map_mul,
      lastAdjacentTransposition_commutes_doubleInclusion]

@[simp]
theorem lastAdjacentTranspositionEndomorphism_hom {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) :
    (lastAdjacentTranspositionEndomorphism mu).hom.hom.hom =
      (spechtModule mu).ρ
        (SymmetricGroup.adjacentTransposition (Fin.last n)) :=
  rfl

@[simp]
theorem lastAdjacentTranspositionEndomorphism_sq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) :
    lastAdjacentTranspositionEndomorphism mu ≫
        lastAdjacentTranspositionEndomorphism mu = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro v
  change (spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n))
      ((spechtModule mu).ρ
        (SymmetricGroup.adjacentTransposition (Fin.last n)) v) = v
  change (((spechtModule mu).ρ
      (SymmetricGroup.adjacentTransposition (Fin.last n))) *
        ((spechtModule mu).ρ
          (SymmetricGroup.adjacentTransposition (Fin.last n)))) v = v
  rw [← (spechtModule mu).ρ.map_mul]
  simp [SymmetricGroup.adjacentTransposition]

/-- Schur's lemma identifies a Specht endomorphism from its value on one
coherent basis vector. -/
theorem spechtEndomorphism_eq_smul_id_of_apply_basis {n : ℕ}
    (nu : YoungDiagramOfSize n) (R : StandardYoungTableau nu)
    (f : spechtModule nu ⟶ spechtModule nu) (c : ℂ)
    (happly : f.hom.hom.hom (spechtOrthogonalBasis nu R) =
      c • spechtOrthogonalBasis nu R) :
    f = c • 𝟙 (spechtModule nu) := by
  obtain ⟨d, hd⟩ := spechtEndomorphism_eq_smul_id nu f
  have hdc : d = c := by
    apply smul_left_injective ℂ
      (Module.Basis.ne_zero (spechtOrthogonalBasis nu) R)
    rw [hd] at happly
    simpa using happly
  subst d
  exact hd

/-- The coherent two-step branching isomorphism sends a tableau basis vector
to the summand selected by deleting its two largest entries. -/
theorem spechtBranchingIso_twoSteps_basis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu) :
    FDRep.isoToLinearEquiv (spechtBranchingIso_twoSteps mu)
        (spechtOrthogonalBasis mu T) =
      (biproduct.ι (fun p : TwoStepRemoval mu => spechtModule p.2.val)
        T.largestTwoStepRemoval).hom.hom.hom
          (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest) := by
  change (spechtBranchingIso_twoSteps mu).hom.hom.hom
      (spechtOrthogonalBasis mu T) = _
  classical
  unfold spechtBranchingIso_twoSteps
  change
    (biproductBiproductIso
        (fun nu : OneBoxRemoval mu => OneBoxRemoval nu.val)
        (fun _ xi => spechtModule xi.val)).hom.hom.hom
      ((biproduct.mapIso
          (fun nu : OneBoxRemoval mu => spechtBranchingIso nu.val)).hom.hom.hom
        (((SymmetricGroupRepresentation.restriction n).mapBiproduct
          (fun nu : OneBoxRemoval mu => spechtModule nu.val)).hom.hom.hom
          ((spechtBranchingIso mu).hom.hom.hom
            (spechtOrthogonalBasis mu T)))) = _
  have htop :
      (spechtBranchingIso mu).hom.hom.hom (spechtOrthogonalBasis mu T) =
        (biproduct.ι (fun nu : OneBoxRemoval mu => spechtModule nu.val)
          T.largestRemoval).hom.hom.hom
            (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest) := by
    simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv] using
      spechtBranchingIso_basis mu T
  rw [htop]
  let F := SymmetricGroupRepresentation.restriction n
  let f := fun nu : OneBoxRemoval mu => spechtModule nu.val
  let e := F.mapBiproduct f
  have hmapMor :
      F.map (biproduct.ι f T.largestRemoval) ≫ e.hom =
        biproduct.ι (fun nu => F.obj (spechtModule nu.val)) T.largestRemoval := by
    rw [← Functor.ι_biproductComparison']
    change (biproduct.ι (fun nu => F.obj (spechtModule nu.val)) T.largestRemoval ≫
      e.inv) ≫ e.hom = _
    calc
      _ = biproduct.ι (fun nu => F.obj (spechtModule nu.val)) T.largestRemoval ≫
          (e.inv ≫ e.hom) := Category.assoc _ _ _
      _ = biproduct.ι (fun nu => F.obj (spechtModule nu.val)) T.largestRemoval ≫ 𝟙 _ :=
        congrArg
          (fun h => biproduct.ι (fun nu => F.obj (spechtModule nu.val))
            T.largestRemoval ≫ h)
          e.inv_hom_id
      _ = _ := Category.comp_id _
  have hmap := congrArg
    (fun h => (ModuleCat.Hom.hom h.hom.hom)
      (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest)) hmapMor
  have hmapApply :
      e.hom.hom.hom
          ((biproduct.ι f T.largestRemoval).hom.hom.hom
            (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest)) =
        (biproduct.ι (fun nu => F.obj (spechtModule nu.val))
          T.largestRemoval).hom.hom.hom
            (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest) := by
    simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply] using hmap
  rw [hmapApply]
  have hmapIsoMor := biproduct.ι_map
    (fun nu : OneBoxRemoval mu => (spechtBranchingIso nu.val).hom)
    T.largestRemoval
  have hmapIso := congrArg
    (fun h => (ModuleCat.Hom.hom h.hom.hom)
      (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest)) hmapIsoMor
  have hmapIsoApply :
      (biproduct.mapIso
          (fun nu : OneBoxRemoval mu => spechtBranchingIso nu.val)).hom.hom.hom
          ((biproduct.ι (fun nu => F.obj (spechtModule nu.val))
            T.largestRemoval).hom.hom.hom
              (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest)) =
        (biproduct.ι
          (fun nu : OneBoxRemoval mu =>
            ⨁ fun xi : OneBoxRemoval nu.val => spechtModule xi.val)
          T.largestRemoval).hom.hom.hom
            ((spechtBranchingIso T.largestRemoval.val).hom.hom.hom
              (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest)) := by
    simpa only [biproduct.mapIso_hom, ConcreteCategory.comp_apply,
      ModuleCat.comp_apply] using hmapIso
  rw [hmapIsoApply]
  have hinner :
      (spechtBranchingIso T.largestRemoval.val).hom.hom.hom
          (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest) =
        (biproduct.ι
          (fun xi : OneBoxRemoval T.largestRemoval.val => spechtModule xi.val)
          T.restrictLargest.largestRemoval).hom.hom.hom
            (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest) := by
    simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv] using
      spechtBranchingIso_basis T.largestRemoval.val T.restrictLargest
  rw [hinner]
  have hflatten (i : OneBoxRemoval mu) (j : OneBoxRemoval i.val) :
      biproduct.ι (fun xi : OneBoxRemoval i.val => spechtModule xi.val) j ≫
          biproduct.ι
            (fun nu : OneBoxRemoval mu =>
              ⨁ fun xi : OneBoxRemoval nu.val => spechtModule xi.val) i ≫
          (biproductBiproductIso
            (fun nu : OneBoxRemoval mu => OneBoxRemoval nu.val)
            (fun _ xi => spechtModule xi.val)).hom =
        biproduct.ι (fun p : TwoStepRemoval mu => spechtModule p.2.val) ⟨i, j⟩ := by
    ext p
    rcases p with ⟨i', j'⟩
    by_cases hi : i = i'
    · subst i'
      by_cases hj : j = j'
      · subst j'
        simp [biproductBiproductIso]
      · simp [biproductBiproductIso, hj]
    · simp [biproductBiproductIso, hi]
  have happ := congrArg
    (fun h => h.hom.hom.hom
      (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest))
    (hflatten T.largestRemoval T.restrictLargest.largestRemoval)
  simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply,
    StandardYoungTableau.largestTwoStepRemoval] using happ

/-- The endpoint-regrouped two-step branching isomorphism sends a tableau
basis vector to the copy selected by its two largest entries. -/
theorem spechtBranchingIso_twoSteps_byEndpoint_basis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu) :
    FDRep.isoToLinearEquiv (spechtBranchingIso_twoSteps_byEndpoint mu)
        (spechtOrthogonalBasis mu T) =
      (biproduct.ι
        (fun nu : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
        T.eraseTwoLargestShape).hom.hom.hom
          ((biproduct.ι
            (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
              spechtModule T.eraseTwoLargestShape)
            T.largestTwoStepRemovalTo).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest)) := by
  classical
  change (spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
    (spechtOrthogonalBasis mu T) = _
  unfold spechtBranchingIso_twoSteps_byEndpoint
  change
    (biproductBiproductIso
      (fun nu : YoungDiagramOfSize n =>
        {p : TwoStepRemoval mu // p.2.val = nu})
      (fun nu _ => spechtModule nu)).inv.hom.hom.hom
        ((biproduct.reindex
          (Equiv.sigmaFiberEquiv
            (fun p : TwoStepRemoval mu => p.2.val)).symm
          (fun q : Σ nu : YoungDiagramOfSize n,
            {p : TwoStepRemoval mu // p.2.val = nu} =>
              spechtModule q.1)).hom.hom.hom
            ((spechtBranchingIso_twoSteps mu).hom.hom.hom
              (spechtOrthogonalBasis mu T))) = _
  rw [show (spechtBranchingIso_twoSteps mu).hom.hom.hom
      (spechtOrthogonalBasis mu T) = _ by
    simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv] using
      spechtBranchingIso_twoSteps_basis mu T]
  have hreindex :
      biproduct.ι (fun p : TwoStepRemoval mu => spechtModule p.2.val)
          T.largestTwoStepRemoval ≫
        (biproduct.reindex
          (Equiv.sigmaFiberEquiv
            (fun p : TwoStepRemoval mu => p.2.val)).symm
          (fun q : Σ nu : YoungDiagramOfSize n,
            {p : TwoStepRemoval mu // p.2.val = nu} =>
              spechtModule q.1)).hom =
        biproduct.ι
          (fun q : Σ nu : YoungDiagramOfSize n,
            {p : TwoStepRemoval mu // p.2.val = nu} =>
              spechtModule q.1)
          ⟨T.eraseTwoLargestShape, T.largestTwoStepRemovalTo⟩ := by
    change biproduct.ι
        ((fun q : Σ nu : YoungDiagramOfSize n,
            {p : TwoStepRemoval mu // p.2.val = nu} =>
              spechtModule q.1) ∘
          (Equiv.sigmaFiberEquiv
            (fun p : TwoStepRemoval mu => p.2.val)).symm)
        T.largestTwoStepRemoval ≫
      (biproduct.reindex
        (Equiv.sigmaFiberEquiv
          (fun p : TwoStepRemoval mu => p.2.val)).symm
        (fun q : Σ nu : YoungDiagramOfSize n,
          {p : TwoStepRemoval mu // p.2.val = nu} =>
            spechtModule q.1)).hom = _
    rw [biproduct.reindex_hom, biproduct.ι_desc]
    rfl
  let e := biproductBiproductIso
    (fun nu : YoungDiagramOfSize n =>
      {p : TwoStepRemoval mu // p.2.val = nu})
    (fun nu _ => spechtModule nu)
  have hunflatten :
      biproduct.ι
          (fun q : Σ nu : YoungDiagramOfSize n,
            {p : TwoStepRemoval mu // p.2.val = nu} =>
              spechtModule q.1)
          ⟨T.eraseTwoLargestShape, T.largestTwoStepRemovalTo⟩ ≫
        e.inv =
      biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo ≫
        biproduct.ι
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape := by
    apply biproduct.hom_ext
    intro nu
    apply biproduct.hom_ext
    intro p
    by_cases hnu : T.eraseTwoLargestShape = nu
    · subst nu
      by_cases hp : T.largestTwoStepRemovalTo = p
      · subst p
        simp [e, biproductBiproductIso, Category.assoc]
        symm
        let inner := biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo
        let outer := biproduct.ι
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape
        let outerProjection := biproduct.π
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape
        let innerProjection := biproduct.π
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo
        change (inner ≫ outer) ≫ (outerProjection ≫ innerProjection) = _
        calc
          _ = inner ≫ (outer ≫ (outerProjection ≫ innerProjection)) :=
            Category.assoc _ _ _
          _ = inner ≫ innerProjection := congrArg (fun h => inner ≫ h)
            (by
              simpa [outer, outerProjection] using
                (biproduct.ι_π_assoc
                  (fun nu : YoungDiagramOfSize n =>
                    ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
                  T.eraseTwoLargestShape T.eraseTwoLargestShape innerProjection))
          _ = _ := by
            simpa [inner, innerProjection] using
              (biproduct.ι_π
                (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
                  spechtModule T.eraseTwoLargestShape)
                T.largestTwoStepRemovalTo T.largestTwoStepRemovalTo)
      · simp [e, biproductBiproductIso, Category.assoc]
        have hsigma :
            (⟨T.eraseTwoLargestShape, T.largestTwoStepRemovalTo⟩ :
              Σ nu : YoungDiagramOfSize n,
                {p : TwoStepRemoval mu // p.2.val = nu}) ≠
              ⟨T.eraseTwoLargestShape, p⟩ := by
          intro h
          exact hp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        let inner := biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo
        let outer := biproduct.ι
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape
        let outerProjection := biproduct.π
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape
        let innerProjection := biproduct.π
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape) p
        have hleft :
            biproduct.ι
                (fun q : Σ nu : YoungDiagramOfSize n,
                  {p : TwoStepRemoval mu // p.2.val = nu} =>
                    spechtModule q.1)
                ⟨T.eraseTwoLargestShape, T.largestTwoStepRemovalTo⟩ ≫
              biproduct.π
                (fun q : Σ nu : YoungDiagramOfSize n,
                  {p : TwoStepRemoval mu // p.2.val = nu} =>
                    spechtModule q.1)
                ⟨T.eraseTwoLargestShape, p⟩ = 0 :=
          biproduct.ι_π_ne _ hsigma
        have hright :
            (inner ≫ outer) ≫ (outerProjection ≫ innerProjection) = 0 := by
          calc
            _ = inner ≫ (outer ≫ (outerProjection ≫ innerProjection)) :=
              Category.assoc _ _ _
            _ = inner ≫ innerProjection := congrArg (fun h => inner ≫ h)
              (by
                simpa [outer, outerProjection] using
                  (biproduct.ι_π_assoc
                    (fun nu : YoungDiagramOfSize n =>
                      ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
                    T.eraseTwoLargestShape T.eraseTwoLargestShape innerProjection))
            _ = 0 := by
              simpa [inner, innerProjection] using
                (biproduct.ι_π_ne
                  (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
                    spechtModule T.eraseTwoLargestShape) hp)
        exact hleft.trans hright.symm
    · simp [e, biproductBiproductIso, Category.assoc]
      symm
      let inner := biproduct.ι
        (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
          spechtModule T.eraseTwoLargestShape)
        T.largestTwoStepRemovalTo
      let outer := biproduct.ι
        (fun xi : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu xi => spechtModule xi)
        T.eraseTwoLargestShape
      let outerProjection := biproduct.π
        (fun xi : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu xi => spechtModule xi) nu
      let innerProjection := biproduct.π
        (fun _ : TwoStepRemovalTo mu nu => spechtModule nu) p
      have hsigma :
          (⟨T.eraseTwoLargestShape, T.largestTwoStepRemovalTo⟩ :
            Σ xi : YoungDiagramOfSize n,
              {q : TwoStepRemoval mu // q.2.val = xi}) ≠ ⟨nu, p⟩ := by
        intro h
        exact hnu (congrArg Sigma.fst h)
      rw [biproduct.ι_π_ne _ hsigma]
      change (inner ≫ outer) ≫ (outerProjection ≫ innerProjection) = 0
      calc
        _ = inner ≫ (outer ≫ (outerProjection ≫ innerProjection)) :=
          Category.assoc _ _ _
        _ = inner ≫ 0 := congrArg (fun h => inner ≫ h)
          (by
            simpa [outer, outerProjection] using
              (biproduct.ι_π_ne_assoc
                (fun xi : YoungDiagramOfSize n =>
                  ⨁ fun _ : TwoStepRemovalTo mu xi => spechtModule xi)
                hnu innerProjection))
        _ = 0 := by simp
  have hregroup :
      biproduct.ι (fun p : TwoStepRemoval mu => spechtModule p.2.val)
          T.largestTwoStepRemoval ≫
        (biproduct.reindex
          (Equiv.sigmaFiberEquiv
            (fun p : TwoStepRemoval mu => p.2.val)).symm
          (fun q : Σ nu : YoungDiagramOfSize n,
            {p : TwoStepRemoval mu // p.2.val = nu} =>
              spechtModule q.1)).hom ≫
        e.inv =
      biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo ≫
        biproduct.ι
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape := by
    calc
      _ = (biproduct.ι
            (fun q : Σ nu : YoungDiagramOfSize n,
              {p : TwoStepRemoval mu // p.2.val = nu} =>
                spechtModule q.1)
            ⟨T.eraseTwoLargestShape, T.largestTwoStepRemovalTo⟩) ≫ e.inv := by
          rw [← Category.assoc, hreindex]
          rfl
      _ = _ := hunflatten
  have happ := congrArg
    (fun h => h.hom.hom.hom
      (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest))
    hregroup
  simpa only [e, ConcreteCategory.comp_apply, ModuleCat.comp_apply] using happ

/-- The inclusion of the path selected by a tableau sends the lower tableau
basis vector back to the original tableau basis vector. -/
theorem twoStepBranchingInclusion_apply_spechtOrthogonalBasis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu) :
    (twoStepBranchingInclusion mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest) =
      spechtOrthogonalBasis mu T := by
  unfold twoStepBranchingInclusion
  change (spechtBranchingIso_twoSteps_byEndpoint mu).inv.hom.hom.hom
    ((biproduct.ι
      (fun nu : YoungDiagramOfSize n =>
        ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
      T.eraseTwoLargestShape).hom.hom.hom
        ((biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo).hom.hom.hom
            (spechtOrthogonalBasis T.eraseTwoLargestShape
              T.restrictTwoLargest))) = _
  rw [← spechtBranchingIso_twoSteps_byEndpoint_basis]
  simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv,
    ConcreteCategory.comp_apply, ModuleCat.comp_apply, ModuleCat.id_apply] using
    congrArg (fun f => f.hom.hom.hom (spechtOrthogonalBasis mu T))
      (spechtBranchingIso_twoSteps_byEndpoint mu).hom_inv_id

/-- Projecting a tableau basis vector onto its own two-step path recovers the
lower tableau basis vector. -/
theorem twoStepBranchingProjection_apply_spechtOrthogonalBasis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu) :
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        (spechtOrthogonalBasis mu T) =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest := by
  unfold twoStepBranchingProjection
  change (biproduct.π
    (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
      spechtModule T.eraseTwoLargestShape)
    T.largestTwoStepRemovalTo).hom.hom.hom
      ((biproduct.π
        (fun nu : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
        T.eraseTwoLargestShape).hom.hom.hom
          ((spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
            (spechtOrthogonalBasis mu T))) = _
  rw [show (spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
      (spechtOrthogonalBasis mu T) = _ by
    simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv] using
      spechtBranchingIso_twoSteps_byEndpoint_basis mu T]
  have houter :
      (biproduct.π
        (fun nu : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
        T.eraseTwoLargestShape).hom.hom.hom
          ((biproduct.ι
            (fun nu : YoungDiagramOfSize n =>
              ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
            T.eraseTwoLargestShape).hom.hom.hom
              ((biproduct.ι
                (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
                  spechtModule T.eraseTwoLargestShape)
                T.largestTwoStepRemovalTo).hom.hom.hom
                  (spechtOrthogonalBasis T.eraseTwoLargestShape
                    T.restrictTwoLargest))) =
        (biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo).hom.hom.hom
            (spechtOrthogonalBasis T.eraseTwoLargestShape
              T.restrictTwoLargest) := by
    simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply,
      ModuleCat.id_apply] using congrArg
        (fun f => f.hom.hom.hom
          ((biproduct.ι
            (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
              spechtModule T.eraseTwoLargestShape)
            T.largestTwoStepRemovalTo).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest)))
        (biproduct.ι_π
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape T.eraseTwoLargestShape)
  rw [houter]
  simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] using congrArg
      (fun f => f.hom.hom.hom
        (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest))
      (biproduct.ι_π
        (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
          spechtModule T.eraseTwoLargestShape)
        T.largestTwoStepRemovalTo T.largestTwoStepRemovalTo)

/-- Projection onto a different path with the same endpoint kills a tableau
basis vector. -/
theorem twoStepBranchingProjection_apply_eq_zero_of_path_ne {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (p : TwoStepRemovalTo mu T.eraseTwoLargestShape)
    (h : T.largestTwoStepRemovalTo ≠ p) :
    (twoStepBranchingProjection mu T.eraseTwoLargestShape p).hom.hom.hom
        (spechtOrthogonalBasis mu T) = 0 := by
  unfold twoStepBranchingProjection
  change (biproduct.π
    (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
      spechtModule T.eraseTwoLargestShape) p).hom.hom.hom
      ((biproduct.π
        (fun nu : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
        T.eraseTwoLargestShape).hom.hom.hom
          ((spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
            (spechtOrthogonalBasis mu T))) = 0
  rw [show (spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
      (spechtOrthogonalBasis mu T) = _ by
    simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv] using
      spechtBranchingIso_twoSteps_byEndpoint_basis mu T]
  have hmor :
      biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo ≫
        biproduct.ι
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape ≫
        biproduct.π
          (fun nu : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu nu => spechtModule nu)
          T.eraseTwoLargestShape ≫
        biproduct.π
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape) p = 0 := by
    simp [Category.assoc, h]
  have happ := congrArg
    (fun f => f.hom.hom.hom
      (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest)) hmor
  simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply,
    LinearMap.map_zero] using happ

/-- Projection onto a different endpoint kills a tableau basis vector. -/
theorem twoStepBranchingProjection_apply_eq_zero_of_endpoint_ne {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (nu : YoungDiagramOfSize n) (p : TwoStepRemovalTo mu nu)
    (h : T.eraseTwoLargestShape ≠ nu) :
    (twoStepBranchingProjection mu nu p).hom.hom.hom
        (spechtOrthogonalBasis mu T) = 0 := by
  unfold twoStepBranchingProjection
  change (biproduct.π
    (fun _ : TwoStepRemovalTo mu nu => spechtModule nu) p).hom.hom.hom
      ((biproduct.π
        (fun xi : YoungDiagramOfSize n =>
          ⨁ fun _ : TwoStepRemovalTo mu xi => spechtModule xi) nu).hom.hom.hom
          ((spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
            (spechtOrthogonalBasis mu T))) = 0
  rw [show (spechtBranchingIso_twoSteps_byEndpoint mu).hom.hom.hom
      (spechtOrthogonalBasis mu T) = _ by
    simpa only [FDRep.isoToLinearEquiv, FGModuleCat.isoToLinearEquiv] using
      spechtBranchingIso_twoSteps_byEndpoint_basis mu T]
  have hmor :
      biproduct.ι
          (fun _ : TwoStepRemovalTo mu T.eraseTwoLargestShape =>
            spechtModule T.eraseTwoLargestShape)
          T.largestTwoStepRemovalTo ≫
        biproduct.ι
          (fun xi : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu xi => spechtModule xi)
          T.eraseTwoLargestShape ≫
        biproduct.π
          (fun xi : YoungDiagramOfSize n =>
            ⨁ fun _ : TwoStepRemovalTo mu xi => spechtModule xi) nu ≫
        biproduct.π
          (fun _ : TwoStepRemovalTo mu nu => spechtModule nu) p = 0 := by
    simp [Category.assoc, h]
  have happ := congrArg
    (fun f => f.hom.hom.hom
      (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest)) hmor
  simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply,
    LinearMap.map_zero] using happ

/-- A path transporter sends a tableau basis vector along the chosen target
path while preserving its lower tableau. -/
theorem twoStepBranchingTransporter_apply_spechtOrthogonalBasis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (q : TwoStepRemovalTo mu T.eraseTwoLargestShape) :
    (twoStepBranchingTransporter mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo q).hom.hom.hom
        (spechtOrthogonalBasis mu T) =
      (twoStepBranchingInclusion mu T.eraseTwoLargestShape q).hom.hom.hom
        (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest) := by
  unfold twoStepBranchingTransporter
  change (twoStepBranchingInclusion mu T.eraseTwoLargestShape q).hom.hom.hom
    ((twoStepBranchingProjection mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        (spechtOrthogonalBasis mu T)) = _
  rw [twoStepBranchingProjection_apply_spechtOrthogonalBasis]

/-- The projector onto a tableau's own two-step path fixes its basis vector. -/
theorem twoStepBranchingProjector_apply_spechtOrthogonalBasis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu) :
    (twoStepBranchingProjector mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        (spechtOrthogonalBasis mu T) = spechtOrthogonalBasis mu T := by
  unfold twoStepBranchingProjector
  rw [twoStepBranchingTransporter_apply_spechtOrthogonalBasis,
    twoStepBranchingInclusion_apply_spechtOrthogonalBasis]

/-- The inclusion for the swapped path reconstructs the swapped tableau from
the common lower tableau. -/
theorem twoStepBranchingInclusion_apply_swapped_spechtOrthogonalBasis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (twoStepBranchingInclusion mu T.eraseTwoLargestShape
      (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
        (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest) =
      spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h) := by
  let U := T.swapAdjacent (Fin.last n) h
  let hs : U.eraseTwoLargestShape = T.eraseTwoLargestShape :=
    T.eraseTwoLargestShape_swapAdjacent_last h
  have hlower : hs ▸ U.restrictTwoLargest = T.restrictTwoLargest :=
    T.restrictTwoLargest_swapAdjacent_last h
  have hU := twoStepBranchingInclusion_apply_spechtOrthogonalBasis mu U
  have hpath : U.largestTwoStepRemovalTo.cast hs =
      T.swappedLargestTwoStepRemovalTo h := by
    apply Subtype.ext
    rw [TwoStepRemovalTo.cast_val]
    rfl
  calc
    _ = (twoStepBranchingInclusion mu T.eraseTwoLargestShape
          (U.largestTwoStepRemovalTo.cast hs)).hom.hom.hom
        (hs ▸ spechtOrthogonalBasis U.eraseTwoLargestShape
          U.restrictTwoLargest) := by
      rw [hpath, spechtOrthogonalBasis_cast, hlower]
    _ = (twoStepBranchingInclusion mu U.eraseTwoLargestShape
          U.largestTwoStepRemovalTo).hom.hom.hom
        (spechtOrthogonalBasis U.eraseTwoLargestShape U.restrictTwoLargest) :=
      twoStepBranchingInclusion_cast mu hs U.largestTwoStepRemovalTo _
    _ = _ := hU

/-- Projecting the swapped tableau onto its path recovers the common lower
tableau. -/
theorem twoStepBranchingProjection_apply_swapped_spechtOrthogonalBasis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
        (spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)) =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest := by
  let U := T.swapAdjacent (Fin.last n) h
  let hs : U.eraseTwoLargestShape = T.eraseTwoLargestShape :=
    T.eraseTwoLargestShape_swapAdjacent_last h
  have hlower : hs ▸ U.restrictTwoLargest = T.restrictTwoLargest :=
    T.restrictTwoLargest_swapAdjacent_last h
  have hU := twoStepBranchingProjection_apply_spechtOrthogonalBasis mu U
  have hcast := twoStepBranchingProjection_cast mu hs
    U.largestTwoStepRemovalTo (spechtOrthogonalBasis mu U)
  have hpath : U.largestTwoStepRemovalTo.cast hs =
      T.swappedLargestTwoStepRemovalTo h := by
    apply Subtype.ext
    rw [TwoStepRemovalTo.cast_val]
    rfl
  rw [hU, spechtOrthogonalBasis_cast, hlower, hpath] at hcast
  exact hcast.symm

/-- The original path projection kills the tableau on the swapped path. -/
theorem twoStepBranchingProjection_apply_swapped_eq_zero {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        (spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)) = 0 := by
  rw [← twoStepBranchingInclusion_apply_swapped_spechtOrthogonalBasis mu T h]
  have hne : T.swappedLargestTwoStepRemovalTo h ≠
      T.largestTwoStepRemovalTo :=
    (T.largestTwoStepRemovalTo_ne_swapped h).symm
  have hmor := twoStepBranchingInclusion_projection mu T.eraseTwoLargestShape
    (T.swappedLargestTwoStepRemovalTo h) T.largestTwoStepRemovalTo
  simp only [hne, if_false] at hmor
  have happ := congrArg
    (fun f => f.hom.hom.hom
      (spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest)) hmor
  simpa only [ConcreteCategory.comp_apply, ModuleCat.comp_apply,
    LinearMap.zero_apply] using happ

/-- Swapping the last two labels reverses their axial distance. -/
theorem StandardYoungTableau.axialDistance_swapAdjacent_last {n : ℕ}
    {mu : YoungDiagramOfSize (n + 2)} (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (T.swapAdjacent (Fin.last n) h).axialDistance (Fin.last n) =
      -T.axialDistance (Fin.last n) := by
  unfold StandardYoungTableau.axialDistance StandardYoungTableau.content
    StandardYoungTableau.position
  simp [StandardYoungTableau.swapAdjacent, StandardYoungTableau.swappedEntry]

/-- The last adjacent transposition has Young's two-term action on a tableau
whose two largest entries may be swapped. -/
theorem lastAdjacentTranspositionEndomorphism_apply_basis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
        (spechtOrthogonalBasis mu T) =
      ((T.axialDistance (Fin.last n) : ℂ)⁻¹) •
          spechtOrthogonalBasis mu T +
        Complex.sqrt
          (1 - ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) •
          spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h) := by
  rw [lastAdjacentTranspositionEndomorphism_hom]
  simpa [swappedOrthogonalBasisVector, h] using
    spechtOrthogonalBasis_adjacentTransposition mu T (Fin.last n)

/-- On the swapped tableau, the same transposition has diagonal coefficient
with the opposite sign and the same off-diagonal coefficient. -/
theorem lastAdjacentTranspositionEndomorphism_apply_swapped_basis {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    (lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
        (spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)) =
      (-((T.axialDistance (Fin.last n) : ℂ)⁻¹)) •
          spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h) +
        Complex.sqrt
          (1 - ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) •
          spechtOrthogonalBasis mu T := by
  let U := T.swapAdjacent (Fin.last n) h
  let hrev := T.isAdjacentSwapStandard_swapAdjacent (Fin.last n) h
  have haction := lastAdjacentTranspositionEndomorphism_apply_basis mu U hrev
  rw [T.axialDistance_swapAdjacent_last h,
    T.swapAdjacent_swapAdjacent (Fin.last n) h] at haction
  simpa using haction

/-- The diagonal `p,p` block of the last adjacent transposition is the Young
axial-distance coefficient. -/
theorem twoStepBranchingBlockEntry_lastAdjacent_pp {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
        (lastAdjacentTranspositionEndomorphism mu)
        T.largestTwoStepRemovalTo T.largestTwoStepRemovalTo =
      ((T.axialDistance (Fin.last n) : ℂ)⁻¹) •
        𝟙 (spechtModule T.eraseTwoLargestShape) := by
  apply spechtEndomorphism_eq_smul_id_of_apply_basis
    T.eraseTwoLargestShape T.restrictTwoLargest
  unfold twoStepBranchingBlockEntry
  change
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        ((lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
          ((twoStepBranchingInclusion mu T.eraseTwoLargestShape
            T.largestTwoStepRemovalTo).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest))) = _
  rw [twoStepBranchingInclusion_apply_spechtOrthogonalBasis,
    lastAdjacentTranspositionEndomorphism_apply_basis]
  let P := (twoStepBranchingProjection mu T.eraseTwoLargestShape
    T.largestTwoStepRemovalTo).hom.hom.hom
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  let eT := spechtOrthogonalBasis mu T
  let eU := spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)
  have hPT : P eT =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest := by
    exact twoStepBranchingProjection_apply_spechtOrthogonalBasis mu T
  have hPU : P eU = 0 := by
    exact twoStepBranchingProjection_apply_swapped_eq_zero mu T h
  change P (a • eT + b • eU) = a • _
  calc
    P (a • eT + b • eU) = P (a • eT) + P (b • eU) :=
      P.map_add (a • eT) (b • eU)
    _ =
        a • P eT + b • P eU :=
      congrArg₂ (· + ·) (P.map_smul a eT) (P.map_smul b eU)
    _ = _ := by
      rw [hPT, hPU]
      simp

/-- The `p,q` block of the last adjacent transposition is Young's
off-diagonal coefficient. -/
theorem twoStepBranchingBlockEntry_lastAdjacent_pq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
        (lastAdjacentTranspositionEndomorphism mu)
        T.largestTwoStepRemovalTo (T.swappedLargestTwoStepRemovalTo h) =
      Complex.sqrt
          (1 - ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) •
        𝟙 (spechtModule T.eraseTwoLargestShape) := by
  apply spechtEndomorphism_eq_smul_id_of_apply_basis
    T.eraseTwoLargestShape T.restrictTwoLargest
  unfold twoStepBranchingBlockEntry
  change
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
        ((lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
          ((twoStepBranchingInclusion mu T.eraseTwoLargestShape
            T.largestTwoStepRemovalTo).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest))) = _
  rw [twoStepBranchingInclusion_apply_spechtOrthogonalBasis,
    lastAdjacentTranspositionEndomorphism_apply_basis]
  let Q := (twoStepBranchingProjection mu T.eraseTwoLargestShape
    (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  let eT := spechtOrthogonalBasis mu T
  let eU := spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)
  have hQT : Q eT = 0 := by
    exact twoStepBranchingProjection_apply_eq_zero_of_path_ne mu T
      (T.swappedLargestTwoStepRemovalTo h)
      (T.largestTwoStepRemovalTo_ne_swapped h)
  have hQU : Q eU =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest := by
    exact twoStepBranchingProjection_apply_swapped_spechtOrthogonalBasis mu T h
  change Q (a • eT + b • eU) = b • _
  calc
    Q (a • eT + b • eU) = Q (a • eT) + Q (b • eU) :=
      Q.map_add (a • eT) (b • eU)
    _ = a • Q eT + b • Q eU :=
      congrArg₂ (· + ·) (Q.map_smul a eT) (Q.map_smul b eU)
    _ = _ := by
      rw [hQT, hQU]
      simp

/-- The `q,p` block has the same off-diagonal coefficient. -/
theorem twoStepBranchingBlockEntry_lastAdjacent_qp {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
        (lastAdjacentTranspositionEndomorphism mu)
        (T.swappedLargestTwoStepRemovalTo h) T.largestTwoStepRemovalTo =
      Complex.sqrt
          (1 - ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) •
        𝟙 (spechtModule T.eraseTwoLargestShape) := by
  apply spechtEndomorphism_eq_smul_id_of_apply_basis
    T.eraseTwoLargestShape T.restrictTwoLargest
  unfold twoStepBranchingBlockEntry
  change
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      T.largestTwoStepRemovalTo).hom.hom.hom
        ((lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
          ((twoStepBranchingInclusion mu T.eraseTwoLargestShape
            (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest))) = _
  rw [twoStepBranchingInclusion_apply_swapped_spechtOrthogonalBasis,
    lastAdjacentTranspositionEndomorphism_apply_swapped_basis]
  let P := (twoStepBranchingProjection mu T.eraseTwoLargestShape
    T.largestTwoStepRemovalTo).hom.hom.hom
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  let eT := spechtOrthogonalBasis mu T
  let eU := spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)
  have hPT : P eT =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest := by
    exact twoStepBranchingProjection_apply_spechtOrthogonalBasis mu T
  have hPU : P eU = 0 := by
    exact twoStepBranchingProjection_apply_swapped_eq_zero mu T h
  change P ((-a) • eU + b • eT) = b • _
  calc
    P ((-a) • eU + b • eT) = P ((-a) • eU) + P (b • eT) :=
      P.map_add ((-a) • eU) (b • eT)
    _ = (-a) • P eU + b • P eT :=
      congrArg₂ (· + ·) (P.map_smul (-a) eU) (P.map_smul b eT)
    _ = _ := by
      rw [hPU, hPT]
      simp

/-- The diagonal `q,q` block has the opposite Young coefficient. -/
theorem twoStepBranchingBlockEntry_lastAdjacent_qq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
        (lastAdjacentTranspositionEndomorphism mu)
        (T.swappedLargestTwoStepRemovalTo h)
        (T.swappedLargestTwoStepRemovalTo h) =
      (-((T.axialDistance (Fin.last n) : ℂ)⁻¹)) •
        𝟙 (spechtModule T.eraseTwoLargestShape) := by
  apply spechtEndomorphism_eq_smul_id_of_apply_basis
    T.eraseTwoLargestShape T.restrictTwoLargest
  unfold twoStepBranchingBlockEntry
  change
    (twoStepBranchingProjection mu T.eraseTwoLargestShape
      (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
        ((lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
          ((twoStepBranchingInclusion mu T.eraseTwoLargestShape
            (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
              (spechtOrthogonalBasis T.eraseTwoLargestShape
                T.restrictTwoLargest))) = _
  rw [twoStepBranchingInclusion_apply_swapped_spechtOrthogonalBasis,
    lastAdjacentTranspositionEndomorphism_apply_swapped_basis]
  let Q := (twoStepBranchingProjection mu T.eraseTwoLargestShape
    (T.swappedLargestTwoStepRemovalTo h)).hom.hom.hom
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  let eT := spechtOrthogonalBasis mu T
  let eU := spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)
  have hQT : Q eT = 0 := by
    exact twoStepBranchingProjection_apply_eq_zero_of_path_ne mu T
      (T.swappedLargestTwoStepRemovalTo h)
      (T.largestTwoStepRemovalTo_ne_swapped h)
  have hQU : Q eU =
      spechtOrthogonalBasis T.eraseTwoLargestShape T.restrictTwoLargest := by
    exact twoStepBranchingProjection_apply_swapped_spechtOrthogonalBasis mu T h
  change Q ((-a) • eU + b • eT) = (-a) • _
  calc
    Q ((-a) • eU + b • eT) = Q ((-a) • eU) + Q (b • eT) :=
      Q.map_add ((-a) • eU) (b • eT)
    _ = (-a) • Q eU + b • Q eT :=
      congrArg₂ (· + ·) (Q.map_smul (-a) eU) (Q.map_smul b eT)
    _ = _ := by
      rw [hQU, hQT]
      simp

/-- Endomorphisms of the twice-restricted Specht module are determined by all
of their branching matrix entries. -/
theorem twoStepBranchingBlockEntry_ext {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2))
    (A B :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj
            (spechtModule mu)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj
            (spechtModule mu)))
    (hentry : ∀ (nu xi : YoungDiagramOfSize n)
      (p : TwoStepRemovalTo mu nu) (q : TwoStepRemovalTo mu xi),
      twoStepBranchingInclusion mu nu p ≫ A ≫
          twoStepBranchingProjection mu xi q =
        twoStepBranchingInclusion mu nu p ≫ B ≫
          twoStepBranchingProjection mu xi q) :
    A = B := by
  let e := spechtBranchingIso_twoSteps_byEndpoint mu
  rw [← cancel_epi e.inv, ← cancel_mono e.hom]
  apply biproduct.hom_ext
  intro xi
  apply biproduct.hom_ext
  intro q
  apply biproduct.hom_ext'
  intro nu
  apply biproduct.hom_ext'
  intro p
  simpa only [e, twoStepBranchingInclusion, twoStepBranchingProjection,
    Category.assoc] using hentry nu xi p q

/-- The two Young coefficients satisfy the unit-circle relation forced by
the involutivity of the adjacent transposition. -/
theorem lastAdjacentTransposition_coefficients_sq_add {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2 +
        (Complex.sqrt
          (1 - ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2)) ^ 2 = 1 := by
  let V := (lastAdjacentTranspositionEndomorphism mu).hom.hom.hom
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  let eT := spechtOrthogonalBasis mu T
  let eU := spechtOrthogonalBasis mu (T.swapAdjacent (Fin.last n) h)
  have hVT : V eT = a • eT + b • eU := by
    exact lastAdjacentTranspositionEndomorphism_apply_basis mu T h
  have hVU : V eU = (-a) • eU + b • eT := by
    exact lastAdjacentTranspositionEndomorphism_apply_swapped_basis mu T h
  have hVV : V (V eT) = eT := by
    dsimp [V]
    change
      (spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n))
          ((spechtModule mu).ρ
            (SymmetricGroup.adjacentTransposition (Fin.last n)) eT) = eT
    change
      ((spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n)) *
        (spechtModule mu).ρ (SymmetricGroup.adjacentTransposition (Fin.last n)))
          eT = eT
    rw [← (spechtModule mu).ρ.map_mul]
    simp [SymmetricGroup.adjacentTransposition]
  have hexpand : V (V eT) = (a ^ 2 + b ^ 2) • eT := by
    rw [hVT]
    calc
      V (a • eT + b • eU) = V (a • eT) + V (b • eU) :=
        V.map_add (a • eT) (b • eU)
      _ = a • V eT + b • V eU :=
        congrArg₂ (· + ·) (V.map_smul a eT) (V.map_smul b eU)
      _ = a • (a • eT + b • eU) + b • ((-a) • eU + b • eT) := by
        exact congrArg₂ (· + ·)
          (congrArg (fun v => a • v) hVT)
          (congrArg (fun v => b • v) hVU)
      _ = (a ^ 2 + b ^ 2) • eT := by
        simp only [smul_add, smul_smul]
        rw [show b * -a = -(a * b) by ring, neg_smul]
        abel_nf
        rw [← add_smul]
        congr 1 <;> ring
  have hscalar : (a ^ 2 + b ^ 2) • eT = (1 : ℂ) • eT := by
    rw [← hexpand, hVV, one_smul]
  exact smul_left_injective ℂ (Module.Basis.ne_zero (spechtOrthogonalBasis mu) T)
    hscalar

/-- The two-path remainder left by the local (5.23) approximate mask. -/
noncomputable def twoStepBranchingProjectorRemainder {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (nu : YoungDiagramOfSize n)
    (p q : TwoStepRemovalTo mu nu) (a b : ℂ) :=
  a ^ 2 •
      (twoStepBranchingProjector mu nu p -
        twoStepBranchingProjector mu nu q) +
    (a * b) •
      (twoStepBranchingTransporter mu nu p q +
        twoStepBranchingTransporter mu nu q p)

/-- Remainders belonging to distinct low endpoints are orthogonal. -/
theorem twoStepBranchingProjectorRemainder_comp_eq_zero_of_endpoint_ne
    {n : ℕ} (mu : YoungDiagramOfSize (n + 2))
    {nu xi : YoungDiagramOfSize n} (h : nu ≠ xi)
    (p q : TwoStepRemovalTo mu nu) (r s : TwoStepRemovalTo mu xi)
    (a b c d : ℂ) :
    twoStepBranchingProjectorRemainder mu nu p q a b ≫
      twoStepBranchingProjectorRemainder mu xi r s c d = 0 := by
  have hzero (u : TwoStepRemovalTo mu nu) (v : TwoStepRemovalTo mu xi) :
      twoStepBranchingInclusion mu nu u ≫
        twoStepBranchingProjection mu xi v = 0 :=
    spechtHom_eq_zero_of_ne h
      (twoStepBranchingInclusion mu nu u ≫
        twoStepBranchingProjection mu xi v)
  have hunit (u v : TwoStepRemovalTo mu nu)
      (w z : TwoStepRemovalTo mu xi) :
      twoStepBranchingTransporter mu nu u v ≫
        twoStepBranchingTransporter mu xi w z = 0 := by
    simp only [twoStepBranchingTransporter, Category.assoc]
    rw [← Category.assoc (twoStepBranchingInclusion mu nu v), hzero v w]
    simp
  simp [twoStepBranchingProjectorRemainder, twoStepBranchingProjector, hunit]

/-- After the path projector discarded by the query mask is removed, the
remaining two-path term in (5.23) has this exact square. -/
theorem twoStepBranchingProjectorRemainder_sq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (nu : YoungDiagramOfSize n)
    (p q : TwoStepRemovalTo mu nu) (hpq : p ≠ q)
    (a b : ℂ) (hab : a ^ 2 + b ^ 2 = 1) :
    let R :=
      a ^ 2 •
          (twoStepBranchingProjector mu nu p -
            twoStepBranchingProjector mu nu q) +
        (a * b) •
          (twoStepBranchingTransporter mu nu p q +
            twoStepBranchingTransporter mu nu q p)
    R ≫ R =
      a ^ 2 •
        (twoStepBranchingProjector mu nu p +
          twoStepBranchingProjector mu nu q) := by
  dsimp only
  simp only [Preadditive.add_comp, Preadditive.comp_add]
  simp [twoStepBranchingProjector, hpq, hpq.symm, smul_smul]
  have hb : b ^ 2 = 1 - a ^ 2 := by
    linear_combination hab
  ring_nf
  rw [hb]
  module

theorem twoStepBranchingProjectorRemainder_sq' {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (nu : YoungDiagramOfSize n)
    (p q : TwoStepRemovalTo mu nu) (hpq : p ≠ q)
    (a b : ℂ) (hab : a ^ 2 + b ^ 2 = 1) :
    twoStepBranchingProjectorRemainder mu nu p q a b ≫
        twoStepBranchingProjectorRemainder mu nu p q a b =
      a ^ 2 •
        (twoStepBranchingProjector mu nu p +
          twoStepBranchingProjector mu nu q) := by
  unfold twoStepBranchingProjectorRemainder
  exact twoStepBranchingProjectorRemainder_sq mu nu p q hpq a b hab

/-- Squaring a sum over distinct low endpoints produces only the diagonal
terms. -/
theorem sum_twoStepBranchingProjectorRemainder_sq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2))
    {I : Type} [Fintype I] (nu : I → YoungDiagramOfSize n)
    (hnu : Function.Injective nu)
    (p q : ∀ i, TwoStepRemovalTo mu (nu i))
    (hpq : ∀ i, p i ≠ q i) (a b c : I → ℂ)
    (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1) :
    (∑ i, c i • twoStepBranchingProjectorRemainder mu (nu i)
          (p i) (q i) (a i) (b i)) ≫
        (∑ i, c i • twoStepBranchingProjectorRemainder mu (nu i)
          (p i) (q i) (a i) (b i)) =
      ∑ i, c i ^ 2 •
        ((a i) ^ 2 •
          (twoStepBranchingProjector mu (nu i) (p i) +
            twoStepBranchingProjector mu (nu i) (q i))) := by
  classical
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul,
      twoStepBranchingProjectorRemainder_sq' mu (nu i)
        (p i) (q i) (hpq i) (a i) (b i) (hab i)]
    congr 1
    ring
  · intro j hj hji
    rw [Linear.smul_comp, Linear.comp_smul,
      twoStepBranchingProjectorRemainder_comp_eq_zero_of_endpoint_ne
        mu (fun h => hji (hnu h))]
    simp
  · intro hnot
    exact (hnot hi).elim

/-- The matrix-unit expression on the right side of Rosmanis's local
projector identity (5.23). -/
noncomputable def lastAdjacentTranspositionProjectorRHS {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :=
  let p := T.largestTwoStepRemovalTo
  let q := T.swappedLargestTwoStepRemovalTo h
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  twoStepBranchingProjector mu T.eraseTwoLargestShape q +
    a ^ 2 •
      (twoStepBranchingProjector mu T.eraseTwoLargestShape p -
        twoStepBranchingProjector mu T.eraseTwoLargestShape q) +
    (a * b) •
      (twoStepBranchingTransporter mu T.eraseTwoLargestShape p q +
        twoStepBranchingTransporter mu T.eraseTwoLargestShape q p)

/-- Equation (5.23) holds on every matrix entry of the common two-step
endpoint block. -/
theorem lastAdjacentTransposition_projector_block {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n))
    (r s : TwoStepRemovalTo mu T.eraseTwoLargestShape) :
    twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
        (lastAdjacentTranspositionEndomorphism mu ≫
          twoStepBranchingProjector mu T.eraseTwoLargestShape
            T.largestTwoStepRemovalTo ≫
          lastAdjacentTranspositionEndomorphism mu) r s =
      twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
        (lastAdjacentTranspositionProjectorRHS mu T h) r s := by
  let p := T.largestTwoStepRemovalTo
  let q := T.swappedLargestTwoStepRemovalTo h
  let A := lastAdjacentTranspositionEndomorphism mu
  let P := twoStepBranchingProjector mu T.eraseTwoLargestShape p
  have hpq : p ≠ q := T.largestTwoStepRemovalTo_ne_swapped h
  have hqp : q ≠ p := hpq.symm
  have hconj (u v : TwoStepRemovalTo mu T.eraseTwoLargestShape) :
      twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
          (A ≫ P ≫ A) u v =
        twoStepBranchingBlockEntry mu T.eraseTwoLargestShape A u p ≫
          twoStepBranchingBlockEntry mu T.eraseTwoLargestShape A p v := by
    simp only [twoStepBranchingBlockEntry, P, twoStepBranchingProjector,
      twoStepBranchingTransporter, Category.assoc]
  rw [show lastAdjacentTranspositionEndomorphism mu ≫
      twoStepBranchingProjector mu T.eraseTwoLargestShape
        T.largestTwoStepRemovalTo ≫
      lastAdjacentTranspositionEndomorphism mu = A ≫ P ≫ A by rfl,
    hconj]
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  have ha_def : ((T.axialDistance (Fin.last n) : ℂ)⁻¹) = a := rfl
  have hb_norm : Complex.sqrt
      (1 - ((T.axialDistance (Fin.last n) : ℂ) ^ 2)⁻¹) = b := by
    rw [← inv_pow]
  have hab : a ^ 2 + b ^ 2 = 1 :=
    lastAdjacentTransposition_coefficients_sq_add mu T h
  have hb : b ^ 2 = 1 - a ^ 2 := by
    linear_combination hab
  rcases p.eq_or_eq_of_ne q hpq r with rfl | rfl <;>
    rcases p.eq_or_eq_of_ne q hpq s with rfl | rfl
  all_goals
    simp only [A, p, q,
      twoStepBranchingBlockEntry_lastAdjacent_pp mu T h,
      twoStepBranchingBlockEntry_lastAdjacent_pq mu T h,
      twoStepBranchingBlockEntry_lastAdjacent_qp mu T h]
    change _ = twoStepBranchingBlockEntry mu T.eraseTwoLargestShape
      (twoStepBranchingProjector mu T.eraseTwoLargestShape q +
        a ^ 2 •
          (twoStepBranchingProjector mu T.eraseTwoLargestShape p -
            twoStepBranchingProjector mu T.eraseTwoLargestShape q) +
        (a * b) •
          (twoStepBranchingTransporter mu T.eraseTwoLargestShape p q +
            twoStepBranchingTransporter mu T.eraseTwoLargestShape q p)) _ _
    simp [twoStepBranchingBlockEntry, twoStepBranchingProjector,
      twoStepBranchingTransporter, ← Category.assoc,
      p, q, hpq, hqp]
    simp only [ha_def, hb_norm]
    simp only [smul_smul] <;>
      (try rw [show b * b = b ^ 2 by ring, hb]) <;> module

/-- Equation (5.23) as an identity on the twice-restricted Specht module. -/
theorem lastAdjacentTransposition_conj_projector {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    lastAdjacentTranspositionEndomorphism mu ≫
        twoStepBranchingProjector mu T.eraseTwoLargestShape
          T.largestTwoStepRemovalTo ≫
        lastAdjacentTranspositionEndomorphism mu =
      lastAdjacentTranspositionProjectorRHS mu T h := by
  apply twoStepBranchingBlockEntry_ext
  intro nu xi r s
  by_cases hnu : nu = T.eraseTwoLargestShape
  · subst nu
    by_cases hxi : xi = T.eraseTwoLargestShape
    · subst xi
      exact lastAdjacentTransposition_projector_block mu T h r s
    · have htarget : T.eraseTwoLargestShape ≠ xi := Ne.symm hxi
      have hAp := twoStepBranching_crossEndpoint_eq_zero mu htarget
        (lastAdjacentTranspositionEndomorphism mu)
        T.largestTwoStepRemovalTo s
      have hp : twoStepBranchingInclusion mu T.eraseTwoLargestShape
          T.largestTwoStepRemovalTo ≫ twoStepBranchingProjection mu xi s = 0 :=
        spechtHom_eq_zero_of_ne htarget _
      have hq : twoStepBranchingInclusion mu T.eraseTwoLargestShape
          (T.swappedLargestTwoStepRemovalTo h) ≫
            twoStepBranchingProjection mu xi s = 0 :=
        spechtHom_eq_zero_of_ne htarget _
      simp [lastAdjacentTranspositionProjectorRHS,
        twoStepBranchingProjector, twoStepBranchingTransporter,
        Category.assoc, hAp, hp, hq]
  · have hAp := twoStepBranching_crossEndpoint_eq_zero mu hnu
      (lastAdjacentTranspositionEndomorphism mu) r
      T.largestTwoStepRemovalTo
    have hp : twoStepBranchingInclusion mu nu r ≫
        twoStepBranchingProjection mu T.eraseTwoLargestShape
          T.largestTwoStepRemovalTo = 0 :=
      spechtHom_eq_zero_of_ne hnu _
    have hq : twoStepBranchingInclusion mu nu r ≫
        twoStepBranchingProjection mu T.eraseTwoLargestShape
          (T.swappedLargestTwoStepRemovalTo h) = 0 :=
      spechtHom_eq_zero_of_ne hnu _
    simp [lastAdjacentTranspositionProjectorRHS,
      twoStepBranchingProjector, twoStepBranchingTransporter,
      ← Category.assoc, hAp, hp, hq]

/-- Equation (5.23) in Rosmanis's orientation: the original path projector is
expanded in the two paths for the coordinate chain conjugated by the adjacent
transposition. -/
theorem lastAdjacentTransposition_source_projector_identity {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    let V := lastAdjacentTranspositionEndomorphism mu
    let p := T.largestTwoStepRemovalTo
    let q := T.swappedLargestTwoStepRemovalTo h
    let P := twoStepBranchingProjector mu T.eraseTwoLargestShape p
    let Q := twoStepBranchingProjector mu T.eraseTwoLargestShape q
    let Epq := twoStepBranchingTransporter mu T.eraseTwoLargestShape p q
    let Eqp := twoStepBranchingTransporter mu T.eraseTwoLargestShape q p
    let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
    let b : ℂ := Complex.sqrt (1 - a ^ 2)
    P =
      V ≫ Q ≫ V +
        a ^ 2 • (V ≫ P ≫ V - V ≫ Q ≫ V) +
        (a * b) • (V ≫ Epq ≫ V + V ≫ Eqp ≫ V) := by
  dsimp only
  let V := lastAdjacentTranspositionEndomorphism mu
  have hV : V ≫ V = 𝟙 _ :=
    lastAdjacentTranspositionEndomorphism_sq mu
  have hconj := lastAdjacentTransposition_conj_projector mu T h
  calc
    twoStepBranchingProjector mu T.eraseTwoLargestShape
        T.largestTwoStepRemovalTo =
      V ≫ (V ≫ twoStepBranchingProjector mu T.eraseTwoLargestShape
        T.largestTwoStepRemovalTo ≫ V) ≫ V := by
          symm
          calc
            V ≫ (V ≫ twoStepBranchingProjector mu T.eraseTwoLargestShape
                T.largestTwoStepRemovalTo ≫ V) ≫ V =
              (V ≫ V) ≫ twoStepBranchingProjector mu
                T.eraseTwoLargestShape T.largestTwoStepRemovalTo ≫
                  (V ≫ V) := by simp only [Category.assoc]
            _ = _ := by rw [hV]; simp
    _ = V ≫ lastAdjacentTranspositionProjectorRHS mu T h ≫ V := by
      rw [hconj]
    _ = _ := by
      simp only [lastAdjacentTranspositionProjectorRHS,
        Preadditive.comp_add, Preadditive.add_comp,
        Preadditive.comp_sub, Preadditive.sub_comp,
        Linear.comp_smul, Linear.smul_comp]
      rfl

/-- The source-oriented survivor after removing the first term of (5.23). -/
noncomputable def lastAdjacentTranspositionSourceRemainder {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :=
  let V := lastAdjacentTranspositionEndomorphism mu
  let p := T.largestTwoStepRemovalTo
  let q := T.swappedLargestTwoStepRemovalTo h
  twoStepBranchingProjector mu T.eraseTwoLargestShape p -
    V ≫ twoStepBranchingProjector mu T.eraseTwoLargestShape q ≫ V

/-- The source survivor is the conjugate of the matrix-unit remainder. -/
theorem lastAdjacentTranspositionSourceRemainder_eq_conj {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    let V := lastAdjacentTranspositionEndomorphism mu
    let p := T.largestTwoStepRemovalTo
    let q := T.swappedLargestTwoStepRemovalTo h
    let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
    let b : ℂ := Complex.sqrt (1 - a ^ 2)
    lastAdjacentTranspositionSourceRemainder mu T h =
      V ≫ twoStepBranchingProjectorRemainder mu T.eraseTwoLargestShape
        p q a b ≫ V := by
  dsimp only
  let V := lastAdjacentTranspositionEndomorphism mu
  let p := T.largestTwoStepRemovalTo
  let q := T.swappedLargestTwoStepRemovalTo h
  let P := twoStepBranchingProjector mu T.eraseTwoLargestShape p
  let Q := twoStepBranchingProjector mu T.eraseTwoLargestShape q
  let R := lastAdjacentTranspositionProjectorRHS mu T h - Q
  have hV : V ≫ V = 𝟙 _ :=
    lastAdjacentTranspositionEndomorphism_sq mu
  have hconj : V ≫ P ≫ V = lastAdjacentTranspositionProjectorRHS mu T h :=
    lastAdjacentTransposition_conj_projector mu T h
  have hsource : P - V ≫ Q ≫ V = V ≫ R ≫ V := by
    dsimp [R]
    rw [← hconj]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
    rw [← Category.assoc V V, hV]
    simp
  rw [show lastAdjacentTranspositionSourceRemainder mu T h =
      P - V ≫ Q ≫ V by rfl, hsource]
  congr 2
  dsimp [R, lastAdjacentTranspositionProjectorRHS,
    twoStepBranchingProjectorRemainder, Q, q]
  module

/-- Source survivors with distinct low endpoints have zero cross product. -/
theorem lastAdjacentTranspositionSourceRemainder_comp_eq_zero_of_endpoint_ne
    {n : ℕ} (mu : YoungDiagramOfSize (n + 2))
    (T U : StandardYoungTableau mu)
    (hT : T.IsAdjacentSwapStandard (Fin.last n))
    (hU : U.IsAdjacentSwapStandard (Fin.last n))
    (hne : T.eraseTwoLargestShape ≠ U.eraseTwoLargestShape) :
    lastAdjacentTranspositionSourceRemainder mu T hT ≫
      lastAdjacentTranspositionSourceRemainder mu U hU = 0 := by
  rw [lastAdjacentTranspositionSourceRemainder_eq_conj,
    lastAdjacentTranspositionSourceRemainder_eq_conj]
  let V := lastAdjacentTranspositionEndomorphism mu
  have hV : V ≫ V = 𝟙 _ :=
    lastAdjacentTranspositionEndomorphism_sq mu
  let RT := twoStepBranchingProjectorRemainder mu T.eraseTwoLargestShape
    T.largestTwoStepRemovalTo (T.swappedLargestTwoStepRemovalTo hT)
    ((T.axialDistance (Fin.last n) : ℂ)⁻¹)
    (Complex.sqrt (1 - ((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2))
  let RU := twoStepBranchingProjectorRemainder mu U.eraseTwoLargestShape
    U.largestTwoStepRemovalTo (U.swappedLargestTwoStepRemovalTo hU)
    ((U.axialDistance (Fin.last n) : ℂ)⁻¹)
    (Complex.sqrt (1 - ((U.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2))
  change (V ≫ RT ≫ V) ≫ V ≫ RU ≫ V = 0
  calc
    (V ≫ RT ≫ V) ≫ V ≫ RU ≫ V =
        V ≫ RT ≫ (V ≫ V) ≫ RU ≫ V := by
      simp only [Category.assoc]
    _ = V ≫ (RT ≫ RU) ≫ V := by rw [hV]; simp
    _ = 0 := by
      rw [show RT ≫ RU = 0 by
        exact twoStepBranchingProjectorRemainder_comp_eq_zero_of_endpoint_ne
          mu hne _ _ _ _ _ _ _ _]
      simp

/-- The exact square after deleting the first, query-invisible projector in
Rosmanis's orientation of (5.23). -/
theorem lastAdjacentTransposition_source_remainder_sq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    let V := lastAdjacentTranspositionEndomorphism mu
    let p := T.largestTwoStepRemovalTo
    let q := T.swappedLargestTwoStepRemovalTo h
    let P := twoStepBranchingProjector mu T.eraseTwoLargestShape p
    let Q := twoStepBranchingProjector mu T.eraseTwoLargestShape q
    let S := P - V ≫ Q ≫ V
    S ≫ S =
      (((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) •
        (V ≫ P ≫ V + V ≫ Q ≫ V) := by
  dsimp only
  let V := lastAdjacentTranspositionEndomorphism mu
  let p := T.largestTwoStepRemovalTo
  let q := T.swappedLargestTwoStepRemovalTo h
  let P := twoStepBranchingProjector mu T.eraseTwoLargestShape p
  let Q := twoStepBranchingProjector mu T.eraseTwoLargestShape q
  let R := lastAdjacentTranspositionProjectorRHS mu T h - Q
  have hV : V ≫ V = 𝟙 _ :=
    lastAdjacentTranspositionEndomorphism_sq mu
  have hconj : V ≫ P ≫ V = lastAdjacentTranspositionProjectorRHS mu T h :=
    lastAdjacentTransposition_conj_projector mu T h
  have hS : P - V ≫ Q ≫ V = V ≫ R ≫ V := by
    dsimp [R]
    rw [← hconj]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
    rw [← Category.assoc V V, hV]
    simp
  rw [hS]
  let a : ℂ := (T.axialDistance (Fin.last n) : ℂ)⁻¹
  let b : ℂ := Complex.sqrt (1 - a ^ 2)
  have hremove : R = a ^ 2 • (P - Q) + (a * b) •
      (twoStepBranchingTransporter mu T.eraseTwoLargestShape p q +
        twoStepBranchingTransporter mu T.eraseTwoLargestShape q p) := by
    dsimp [R, P, Q, p, q, a, b]
    simp only [lastAdjacentTranspositionProjectorRHS]
    module
  have hR : R ≫ R = a ^ 2 • (P + Q) := by
    rw [hremove]
    exact twoStepBranchingProjectorRemainder_sq mu T.eraseTwoLargestShape
      p q (T.largestTwoStepRemovalTo_ne_swapped h) a b
      (lastAdjacentTransposition_coefficients_sq_add mu T h)
  calc
    (V ≫ R ≫ V) ≫ V ≫ R ≫ V =
        V ≫ R ≫ (V ≫ V) ≫ R ≫ V := by
      simp only [Category.assoc]
    _ = V ≫ (R ≫ R) ≫ V := by rw [hV]; simp
    _ = _ := by
      rw [hR]
      simp only [Linear.comp_smul, Linear.smul_comp,
        Preadditive.comp_add, Preadditive.add_comp]
      rfl

theorem lastAdjacentTranspositionSourceRemainder_sq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2)) (T : StandardYoungTableau mu)
    (h : T.IsAdjacentSwapStandard (Fin.last n)) :
    let V := lastAdjacentTranspositionEndomorphism mu
    let p := T.largestTwoStepRemovalTo
    let q := T.swappedLargestTwoStepRemovalTo h
    let P := twoStepBranchingProjector mu T.eraseTwoLargestShape p
    let Q := twoStepBranchingProjector mu T.eraseTwoLargestShape q
    lastAdjacentTranspositionSourceRemainder mu T h ≫
        lastAdjacentTranspositionSourceRemainder mu T h =
      (((T.axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2) •
        (V ≫ P ≫ V + V ≫ Q ≫ V) := by
  simpa only [lastAdjacentTranspositionSourceRemainder] using
    lastAdjacentTransposition_source_remainder_sq mu T h

/-- Point 5 of the local calculation: after summing distinct endpoint blocks,
all cross terms still vanish. -/
theorem sum_lastAdjacentTranspositionSourceRemainder_sq {n : ℕ}
    (mu : YoungDiagramOfSize (n + 2))
    {I : Type} [Fintype I] (T : I → StandardYoungTableau mu)
    (h : ∀ i, (T i).IsAdjacentSwapStandard (Fin.last n))
    (hendpoint : Function.Injective fun i => (T i).eraseTwoLargestShape)
    (c : I → ℂ) :
    (∑ i, c i • lastAdjacentTranspositionSourceRemainder mu (T i) (h i)) ≫
        (∑ i, c i • lastAdjacentTranspositionSourceRemainder mu (T i) (h i)) =
      ∑ i, c i ^ 2 •
        ((((T i).axialDistance (Fin.last n) : ℂ)⁻¹) ^ 2 •
          (let V := lastAdjacentTranspositionEndomorphism mu
           let p := (T i).largestTwoStepRemovalTo
           let q := (T i).swappedLargestTwoStepRemovalTo (h i)
           V ≫ twoStepBranchingProjector mu (T i).eraseTwoLargestShape p ≫ V +
             V ≫ twoStepBranchingProjector mu (T i).eraseTwoLargestShape q ≫ V)) := by
  classical
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul,
      lastAdjacentTranspositionSourceRemainder_sq mu (T i) (h i)]
    congr 1
    ring
  · intro j hj hji
    rw [Linear.smul_comp, Linear.comp_smul,
      lastAdjacentTranspositionSourceRemainder_comp_eq_zero_of_endpoint_ne
        mu (T j) (T i) (h j) (h i)
          (fun hij => hji (hendpoint hij))]
    simp
  · intro hnot
    exact (hnot hi).elim
