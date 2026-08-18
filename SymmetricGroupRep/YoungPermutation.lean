import SymmetricGroupRep.Tabloids
import SymmetricGroupRep.Pieri
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.LinearAlgebra.Finsupp.LSum

open CategoryTheory
open scoped MonoidalCategory

namespace Representation

variable {G H X : Type} [Group G] [Group H] [MulAction H X]

/-- The map out of the induced trivial representation sending the generator indexed by `h` to
the point `h⁻¹ • base`. -/
private noncomputable def indTrivialToFinsupp (φ : G →* H) (base : X)
    (fixesBase : ∀ g : G, φ g • base = base) :
    IndV φ (1 : Representation ℂ G ℂ) →ₗ[ℂ] MonoidAlgebra ℂ X :=
  Coinvariants.lift _
    (MonoidAlgebra.mapDomainLinearMap ℂ ℂ (fun h : H => h⁻¹ • base) ∘ₗ
      (_root_.TensorProduct.rid ℂ (MonoidAlgebra ℂ H)).toLinearMap)
    fun g => by
      ext h z
      simp [mul_smul, ← map_inv, fixesBase]

private theorem indTrivialToFinsupp_mk (φ : G →* H) (base : X)
    (fixesBase : ∀ g : G, φ g • base = base) (h : H) (z : ℂ) :
    indTrivialToFinsupp φ base fixesBase (IndV.mk φ _ h z) =
      MonoidAlgebra.single (h⁻¹ • base) z := by
  simp [indTrivialToFinsupp]

/-- The map into the induced trivial representation sending a point to a generator carrying the
base point to it. -/
private noncomputable def indTrivialOfFinsupp (φ : G →* H) (base : X)
    (transitive : ∀ x : X, ∃ h : H, h⁻¹ • base = x) :
    MonoidAlgebra ℂ X →ₗ[ℂ] IndV φ (1 : Representation ℂ G ℂ) :=
  (Finsupp.linearCombination ℂ fun x => IndV.mk φ _ (transitive x).choose 1).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem indTrivialOfFinsupp_single (φ : G →* H) (base : X)
    (transitive : ∀ x : X, ∃ h : H, h⁻¹ • base = x) (x : X) (z : ℂ) :
    indTrivialOfFinsupp φ base transitive (MonoidAlgebra.single x z) =
      IndV.mk φ _ (transitive x).choose z := by
  rw [indTrivialOfFinsupp, LinearMap.comp_apply]
  change (Finsupp.linearCombination ℂ fun x => IndV.mk φ _ (transitive x).choose 1)
      (Finsupp.single x z) = _
  rw [Finsupp.linearCombination_single, ← map_smul, smul_eq_mul, mul_one]

/-- Generators of the induced trivial representation indexed by the same coset agree. -/
private theorem indTrivialMk_mul (φ : G →* H) (g : G) (h : H) (z : ℂ) :
    IndV.mk φ (1 : Representation ℂ G ℂ) (φ g * h) z = IndV.mk φ _ h z := by
  have := Coinvariants.mk_self_apply
    (Representation.tprod ((leftRegular ℂ H).comp φ) (1 : Representation ℂ G ℂ)) g
    (MonoidAlgebra.single h (1 : ℂ) ⊗ₜ[ℂ] z)
  simpa using this

/-- On a transitive `H`-set whose base-point stabiliser is the image of `φ`, the induced trivial
representation is the permutation module on the set. -/
private noncomputable def indTrivialFinsuppEquiv (φ : G →* H) (base : X)
    (transitive : ∀ x : X, ∃ h : H, h⁻¹ • base = x)
    (stabilizer : ∀ h : H, h • base = base ↔ h ∈ φ.range) :
    IndV φ (1 : Representation ℂ G ℂ) ≃ₗ[ℂ] MonoidAlgebra ℂ X :=
  have fixesBase : ∀ g : G, φ g • base = base := fun g => (stabilizer (φ g)).2 ⟨g, rfl⟩
  LinearEquiv.ofLinear (indTrivialToFinsupp φ base fixesBase)
    (indTrivialOfFinsupp φ base transitive)
    (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring (by
      show indTrivialToFinsupp φ base fixesBase
          (indTrivialOfFinsupp φ base transitive (MonoidAlgebra.single x 1)) =
            MonoidAlgebra.single x 1
      rw [indTrivialOfFinsupp_single, indTrivialToFinsupp_mk, (transitive x).choose_spec]))
    (IndV.hom_ext _ _ fun h => LinearMap.ext fun z => by
      obtain ⟨g, hg⟩ := (stabilizer (h * (transitive (h⁻¹ • base)).choose⁻¹)).1 (by
        rw [mul_smul, (transitive (h⁻¹ • base)).choose_spec, smul_inv_smul])
      show indTrivialOfFinsupp φ base transitive
          (indTrivialToFinsupp φ base fixesBase (IndV.mk φ _ h z)) = IndV.mk φ _ h z
      rw [indTrivialToFinsupp_mk, indTrivialOfFinsupp_single,
        ← indTrivialMk_mul φ g (transitive (h⁻¹ • base)).choose z, hg, inv_mul_cancel_right])

end Representation

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
    Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ e) fun g => by
      ext x
      simp [equivariant]
  exact Action.mkIso E.toLinearEquiv.toFGModuleCatIso fun g => by
    apply FGModuleCat.hom_ext
    exact E.toIntertwiningMap.2 g

/-- A transitive permutation representation is induced from the trivial representation of a group
whose image is the stabiliser of a base point. -/
noncomputable def indTrivialIso {G H X : Type} [Group G] [Group H] [Finite H]
    [MulAction H X] [Finite X] (φ : G →* H) (base : X)
    (transitive : ∀ x : X, ∃ h : H, h⁻¹ • base = x)
    (stabilizer : ∀ h : H, h • base = base ↔ h ∈ φ.range) :
    FDRep.ind φ (𝟙_ (FDRep ℂ G)) ≅ FDRep.of (Representation.ofMulAction ℂ H X) := by
  have fixesBase : ∀ g : G, φ g • base = base := fun g => (stabilizer (φ g)).2 ⟨g, rfl⟩
  haveI : Module.Finite ℂ (Representation.IndV φ (1 : Representation ℂ G ℂ)) :=
    Module.Finite.equiv (Representation.indTrivialFinsuppEquiv φ base transitive stabilizer).symm
  refine Action.mkIso
    (Representation.indTrivialFinsuppEquiv φ base transitive stabilizer).toFGModuleCatIso ?_
  intro h
  apply FGModuleCat.hom_ext
  refine Representation.IndV.hom_ext φ _ fun h₂ => LinearMap.ext fun z => ?_
  show Representation.indTrivialToFinsupp φ base fixesBase
      (Representation.ind φ 1 h (Representation.IndV.mk φ _ h₂ z)) =
    Representation.ofMulAction ℂ H X h
      (Representation.indTrivialToFinsupp φ base fixesBase (Representation.IndV.mk φ _ h₂ z))
  rw [Representation.ind_mk, Representation.indTrivialToFinsupp_mk,
    Representation.indTrivialToFinsupp_mk, Representation.ofMulAction_single,
    mul_inv_rev, inv_inv, mul_smul]

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

/-- The cells of a two-row partition, split by row. -/
theorem twoRowPartition_cells (n r : ℕ) (h : 2 * r ≤ n) :
    (twoRowPartition n r h).val.cells =
      ({0} ×ˢ Finset.range (n - r)) ∪ ({1} ×ˢ Finset.range r) := by
  ext ⟨row, column⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, twoRowPartition_rowLen]
  match row with
  | 0 => simp
  | 1 => simp
  | (row + 2) => simp

/-- A fixed-size shape whose row lengths match a two-row partition is that partition. -/
theorem YoungDiagramOfSize.eq_twoRowPartition {n r : ℕ} (h : 2 * r ≤ n)
    (shape : YoungDiagramOfSize n)
    (h0 : shape.val.rowLen 0 = n - r) (h1 : shape.val.rowLen 1 = r)
    (h2 : ∀ row, 2 ≤ row → shape.val.rowLen row = 0) :
    shape = twoRowPartition n r h := by
  apply Subtype.ext
  apply YoungDiagram.ext_of_rowLen
  intro row
  rw [twoRowPartition_rowLen]
  match row with
  | 0 => simpa using h0
  | 1 => simpa using h1
  | (row + 2) => simpa using h2 (row + 2) (by omega)

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

/-- The two-row tabloid whose top row holds the first `a` labels. -/
private def twoRowBaseTabloid (a b : ℕ) (h : b ≤ a) :
    Tabloid (twoRowPartition (a + b) b (by omega)) where
  rowOf i := ⟨if (i : ℕ) < a then 0 else 1, by have := i.isLt; split <;> omega⟩
  row_nonempty i := by
    have := i.isLt
    rw [twoRowPartition_rowLen]
    split <;> simp <;> omega
  content row := by
    rw [Finset.card_filter, Fin.sum_univ_add, twoRowPartition_rowLen]
    simp
    split_ifs <;> omega

/-- The standard Young subgroup is the stabiliser of the base tabloid. -/
private theorem smul_twoRowBaseTabloid_eq_self_iff (a b : ℕ) (h : b ≤ a)
    (sigma : SymmetricGroup (a + b)) :
    sigma • twoRowBaseTabloid a b h = twoRowBaseTabloid a b h ↔
      sigma ∈ (SymmetricGroup.youngSubgroupInclusion a b).range := by
  have hrow : ∀ i j : Fin (a + b),
      (twoRowBaseTabloid a b h).rowOf i = (twoRowBaseTabloid a b h).rowOf j ↔
        ((i : ℕ) < a ↔ (j : ℕ) < a) := fun i j => by
    rw [Fin.ext_iff]
    simp only [twoRowBaseTabloid]
    split_ifs <;> simp <;> omega
  have hrows : sigma • twoRowBaseTabloid a b h = twoRowBaseTabloid a b h ↔
      ∀ i : Fin (a + b), ((sigma⁻¹ i : ℕ) < a ↔ (i : ℕ) < a) := by
    rw [Tabloid.ext_iff, funext_iff]
    exact forall_congr' fun i => by rw [Tabloid.smul_rowOf]; exact hrow _ i
  rw [hrows, SymmetricGroup.mem_youngSubgroupInclusion_range_iff]
  constructor
  · intro hfix i hi
    exact (hfix (sigma i)).mp (by simpa using hi)
  · intro hmaps i
    have hinv := (SymmetricGroup.mem_youngSubgroupInclusion_range_iff a b sigma⁻¹).mp
      (inv_mem ((SymmetricGroup.mem_youngSubgroupInclusion_range_iff a b sigma).mpr hmaps))
    exact ⟨fun hlt => by simpa using hmaps _ hlt, hinv i⟩

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
theorem youngPermutationModule_twoRow_induction (a b : ℕ) (h : b ≤ a) :
  Nonempty (youngPermutationModule (twoRowPartition (a + b) b (by omega)) ≅
    (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (𝟙_ (FDRep ℂ (SymmetricGroup a × SymmetricGroup b)))) :=
  ⟨(FDRep.indTrivialIso (SymmetricGroup.youngSubgroupInclusion a b) (twoRowBaseTabloid a b h)
      (fun T => by
        obtain ⟨sigma, hsigma⟩ :=
          MulAction.exists_smul_eq (SymmetricGroup (a + b)) (twoRowBaseTabloid a b h) T
        exact ⟨sigma⁻¹, by simpa using hsigma⟩)
      (smul_twoRowBaseTabloid_eq_self_iff a b h)).symm⟩
