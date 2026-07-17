import SymmetricGroupRep.Pieri
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.LinearAlgebra.Finsupp.LSum

open CategoryTheory
open scoped MonoidalCategory

/-! # Tabloids and Young permutation modules

Tabloids are represented by the row containing each label.  This avoids a
quotient by row equivalence while retaining the usual permutation action.
-/

/-- A tabloid of shape `mu`, represented by the row containing each label. -/
@[ext]
structure Tabloid {n : ℕ} (mu : YoungDiagramOfSize n) where
  rowOf : Fin n → Fin n
  row_nonempty : ∀ i, 0 < mu.val.rowLen (rowOf i)
  content : ∀ row : ℕ,
    (Finset.univ.filter fun i => (rowOf i : ℕ) = row).card = mu.val.rowLen row

namespace Tabloid

noncomputable instance {n : ℕ} (mu : YoungDiagramOfSize n) : Finite (Tabloid mu) :=
  Finite.of_injective rowOf fun T U h => by
    apply Tabloid.ext
    exact h

/-- Every Young diagram admits a tabloid. -/
theorem nonempty {n : ℕ} (mu : YoungDiagramOfSize n) : Nonempty (Tabloid mu) := by
  let e : Fin n ≃ ↥mu.val.cells :=
    (mu.val.cells.equivFinOfCardEq mu.property).symm
  have cell_fst_lt (c : ↥mu.val.cells) : c.1.1 < n := by
    have hc : c.1.1 < mu.val.card :=
      (YoungDiagram.mem_iff_lt_colLen.mp c.2).trans_le <| by
        rw [YoungDiagram.colLen_eq_card]
        exact Finset.card_le_card (Finset.filter_subset _ _)
    simpa [mu.property] using hc
  let rowOf : Fin n → Fin n := fun i => ⟨(e i).1.1, cell_fst_lt (e i)⟩
  refine ⟨{
    rowOf := rowOf
    row_nonempty := fun i => by
      have hc := YoungDiagram.mem_iff_lt_rowLen.mp (e i).2
      change 0 < mu.val.rowLen (e i).1.1
      exact lt_of_le_of_lt (Nat.zero_le _) hc
    content := ?_ }⟩
  intro row
  let target := mu.val.cells.attach.filter fun c => c.1.1 = row
  calc
    (Finset.univ.filter fun i => (rowOf i : ℕ) = row).card = target.card := by
      apply Finset.card_bijective e e.bijective
      intro i
      simp [target, rowOf]
    _ = (mu.val.row row).card := by
      change (mu.val.cells.attach.filter fun c => c.1.1 = row).card =
        (mu.val.cells.filter fun c => c.1 = row).card
      rw [Finset.filter_attach (fun c : ℕ × ℕ => c.1 = row) mu.val.cells]
      simp
    _ = mu.val.rowLen row := (YoungDiagram.rowLen_eq_card mu.val).symm

end Tabloid

instance {n : ℕ} (mu : YoungDiagramOfSize n) :
    MulAction (SymmetricGroup n) (Tabloid mu) where
  smul sigma T := {
    rowOf := fun i => T.rowOf (sigma⁻¹ i)
    row_nonempty := fun i => T.row_nonempty _
    content := fun row => by
      rw [← T.content row]
      symm
      apply Finset.card_bijective sigma sigma.bijective
      intro i
      simp }
  one_smul T := by
    apply Tabloid.ext
    funext i
    change T.rowOf ((1 : SymmetricGroup n)⁻¹ i) = T.rowOf i
    rw [inv_one]
    rfl
  mul_smul sigma tau T := by
    apply Tabloid.ext
    funext i
    change T.rowOf ((sigma * tau)⁻¹ i) = T.rowOf (tau⁻¹ (sigma⁻¹ i))
    rw [mul_inv_rev]
    rfl

@[simp]
theorem Tabloid.smul_rowOf {n : ℕ} {mu : YoungDiagramOfSize n}
    (sigma : SymmetricGroup n) (T : Tabloid mu) (i : Fin n) :
    (sigma • T).rowOf i = T.rowOf (sigma⁻¹ i) :=
  rfl

/-- The Young permutation module with its tabloid basis. -/
noncomputable def youngPermutationModule {n : ℕ} (mu : YoungDiagramOfSize n) :
    SymmetricGroupRepresentation n :=
  FDRep.of (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu))

/-- The symmetric group permutes the tabloid basis in the usual way. -/
@[simp]
theorem youngPermutationModule_rho_single {n : ℕ} (mu : YoungDiagramOfSize n)
    (sigma : SymmetricGroup n) (T : Tabloid mu) (c : ℂ) :
    (youngPermutationModule mu).ρ sigma (Finsupp.single T c) =
      Finsupp.single (sigma • T) c :=
  Representation.ofMulAction_single sigma T c

namespace FDRep

/-- An equivariant equivalence of finite `G`-sets induces an isomorphism of their
permutation representations. -/
noncomputable def ofMulActionEquiv
    {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]
    [Finite X] [Finite Y]
    (e : X ≃ Y) (equivariant : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    FDRep.of (Representation.ofMulAction ℂ G X) ≅
      FDRep.of (Representation.ofMulAction ℂ G Y) := by
  let E : (Representation.ofMulAction ℂ G X).Equiv
      (Representation.ofMulAction ℂ G Y) :=
    Representation.Equiv.mk (Finsupp.domLCongr e) fun g => by
      ext x
      simp [equivariant]
  exact Action.mkIso E.toLinearEquiv.toFGModuleCatIso fun g => by
    apply FGModuleCat.hom_ext
    exact E.toIntertwiningMap.2 g

end FDRep

/-- The number of cells supplied by a list of row lengths is the sum of those
lengths. -/
theorem YoungDiagram.card_cellsOfRowLens (widths : List ℕ) :
    (YoungDiagram.cellsOfRowLens widths).card = widths.sum := by
  induction widths with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons width widths ih =>
      rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
      · simp [ih]
      · rw [Finset.disjoint_left]
        intro cell hfirst hrest
        simp only [Finset.mem_product, Finset.mem_singleton] at hfirst
        rw [Finset.mem_map] at hrest
        rcases hrest with ⟨other, _, rfl⟩
        simp at hfirst

/-- The two-row partition `(n - r, r)`. -/
def twoRowPartition (n r : ℕ) (h : 2 * r ≤ n) : YoungDiagramOfSize n := by
  have hordered : r ≤ n - r := by omega
  exact ⟨YoungDiagram.ofRowLens [n - r, r]
      (by simpa [List.sortedGE_iff_pairwise] using hordered),
    by
      change (YoungDiagram.cellsOfRowLens [n - r, r]).card = n
      rw [YoungDiagram.card_cellsOfRowLens]
      simp
      omega⟩

/-- The row lengths of `twoRowPartition`. -/
theorem twoRowPartition_rowLen (n r : ℕ) (h : 2 * r ≤ n) (row : ℕ) :
    (twoRowPartition n r h).val.rowLen row =
      if row = 0 then n - r else if row = 1 then r else 0 := by
  apply eq_of_forall_lt_iff
  intro column
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  simp only [twoRowPartition, YoungDiagram.mem_ofRowLens]
  rcases row with _ | row
  · simp
  rcases row with _ | row
  · simp
  simp

namespace Tabloid

/-- The labels in the second row of a two-row tabloid. -/
def secondRow {n r : ℕ} {h : 2 * r ≤ n}
    (T : Tabloid (twoRowPartition n r h)) : Set.powersetCard (Fin n) r :=
  ⟨Finset.univ.filter fun i => (T.rowOf i : ℕ) = 1, by
    simp [T.content 1, twoRowPartition_rowLen]⟩

@[simp]
theorem mem_secondRow {n r : ℕ} {h : 2 * r ≤ n}
    (T : Tabloid (twoRowPartition n r h)) (i : Fin n) :
    i ∈ secondRow T ↔ (T.rowOf i : ℕ) = 1 := by
  simp [secondRow]

private theorem rowOf_eq_zero_or_one {n r : ℕ} {h : 2 * r ≤ n}
    (T : Tabloid (twoRowPartition n r h)) (i : Fin n) :
    (T.rowOf i : ℕ) = 0 ∨ (T.rowOf i : ℕ) = 1 := by
  by_cases hzero : (T.rowOf i : ℕ) = 0
  · exact Or.inl hzero
  by_cases hone : (T.rowOf i : ℕ) = 1
  · exact Or.inr hone
  have hpositive := T.row_nonempty i
  rw [twoRowPartition_rowLen n r h] at hpositive
  simp [hzero, hone] at hpositive

private theorem secondRow_injective {n r : ℕ} {h : 2 * r ≤ n} :
    Function.Injective (secondRow (h := h)) := by
  intro T U hequal
  apply Tabloid.ext
  funext i
  have hforward : (T.rowOf i : ℕ) = 1 → (U.rowOf i : ℕ) = 1 := by
    intro hi
    have : i ∈ secondRow T := (mem_secondRow T i).2 hi
    rw [hequal] at this
    exact (mem_secondRow U i).1 this
  have hbackward : (U.rowOf i : ℕ) = 1 → (T.rowOf i : ℕ) = 1 := by
    intro hi
    have : i ∈ secondRow U := (mem_secondRow U i).2 hi
    rw [← hequal] at this
    exact (mem_secondRow T i).1 this
  rcases rowOf_eq_zero_or_one T i with hT | hT
  · rcases rowOf_eq_zero_or_one U i with hU | hU
    · apply Fin.ext
      omega
    · have := hbackward hU
      omega
  · rcases rowOf_eq_zero_or_one U i with hU | hU
    · have := hforward hT
      omega
    · apply Fin.ext
      omega

private theorem secondRow_surjective {n r : ℕ} {h : 2 * r ≤ n} :
    Function.Surjective (secondRow (h := h)) := by
  intro subset
  by_cases hr : r = 0
  · obtain ⟨T⟩ := Tabloid.nonempty (twoRowPartition n r h)
    refine ⟨T, Subtype.ext ?_⟩
    have hleft : (secondRow T).val = ∅ := Finset.card_eq_zero.mp <| by
      simp [hr]
    have hright : subset.val = ∅ := Finset.card_eq_zero.mp <| by
      simp [hr]
    rw [hleft, hright]
  · have hn : 0 < n := by omega
    have hone_lt : 1 < n := by omega
    let zero : Fin n := ⟨0, hn⟩
    let one : Fin n := ⟨1, hone_lt⟩
    let rowOf : Fin n → Fin n := fun i => if i ∈ subset.val then one else zero
    let T : Tabloid (twoRowPartition n r h) := {
      rowOf := rowOf
      row_nonempty := fun i => by
        by_cases hi : i ∈ subset.val
        · simp [rowOf, hi, one, twoRowPartition_rowLen]
          omega
        · simp [rowOf, hi, zero, twoRowPartition_rowLen]
          omega
      content := fun row => by
        by_cases hzero : row = 0
        · subst row
          have hfilter :
              Finset.univ.filter (fun i => (rowOf i : ℕ) = 0) = subset.valᶜ := by
            ext i
            by_cases hi : i ∈ subset.val <;> simp [rowOf, hi, zero, one]
          rw [hfilter, Finset.card_compl, subset.property,
            twoRowPartition_rowLen]
          simp
        by_cases hone : row = 1
        · subst row
          have hfilter :
              Finset.univ.filter (fun i => (rowOf i : ℕ) = 1) = subset.val := by
            ext i
            by_cases hi : i ∈ subset.val <;> simp [rowOf, hi, zero, one]
          rw [hfilter, subset.property, twoRowPartition_rowLen]
          simp
        · have hfilter :
              Finset.univ.filter (fun i => (rowOf i : ℕ) = row) = ∅ := by
            ext i
            by_cases hi : i ∈ subset.val <;>
              simp [rowOf, hi, zero, one] <;> omega
          rw [hfilter, twoRowPartition_rowLen]
          simp [hzero, hone] }
    refine ⟨T, Subtype.ext ?_⟩
    ext i
    by_cases hi : i ∈ subset.val <;> simp [T, secondRow, rowOf, hi, zero, one]

/-- Two-row tabloids are equivariantly equivalent to subsets of the size of the
second row. -/
noncomputable def twoRowEquiv {n r : ℕ} (h : 2 * r ≤ n) :
    Tabloid (twoRowPartition n r h) ≃ Set.powersetCard (Fin n) r :=
  Equiv.ofBijective secondRow ⟨secondRow_injective, secondRow_surjective⟩

@[simp]
theorem twoRowEquiv_apply {n r : ℕ} (h : 2 * r ≤ n)
    (T : Tabloid (twoRowPartition n r h)) :
    twoRowEquiv h T = secondRow T :=
  rfl

/-- The two-row tabloid equivalence respects the symmetric-group action. -/
theorem twoRowEquiv_smul {n r : ℕ} (h : 2 * r ≤ n)
    (sigma : SymmetricGroup n) (T : Tabloid (twoRowPartition n r h)) :
    twoRowEquiv h (sigma • T) = sigma • twoRowEquiv h T := by
  apply Subtype.ext
  ext i
  simp only [twoRowEquiv_apply, secondRow, Tabloid.smul_rowOf,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.powersetCard.coe_smul,
    Finset.mem_smul_finset]
  constructor
  · intro hi
    exact ⟨sigma⁻¹ i, hi, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    simpa using hj

end Tabloid

/-- The Young permutation module of shape `(a,b)` is induced from the trivial
representation of the standard Young subgroup `S_a x S_b`.

This is the two-row specialization of Tomczak, *Representation Theory of
Symmetric Groups* (2022 lecture notes), Lemma 2.1, which states
`M^lambda ≅ Ind_(S_lambda)^(S_n) 1`:
https://math.berkeley.edu/~ltomczak/notes/Mich2022/RepSn_Notes.pdf.
See also Sagan, *The Symmetric Group*, 2nd ed., Section 2.1,
https://doi.org/10.1007/978-1-4757-6804-6_2.  Mathlib's induced representation
uses right translation on coset generators, so the standard identification
sends the generator indexed by `g` to the tabloid `g⁻¹ • T_0`. -/
axiom youngPermutationModule_twoRow_induction (a b : ℕ) (h : b ≤ a) :
  Nonempty (youngPermutationModule (twoRowPartition (a + b) b (by omega)) ≅
    (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (𝟙_ (FDRep ℂ (SymmetricGroup a × SymmetricGroup b))))
