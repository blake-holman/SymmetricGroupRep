import SymmetricGroupRep.Branching
import SymmetricGroupRep.Tableaux
import Mathlib.Logic.Equiv.Fin.Basic

/-! # A coherent Young branching basis -/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

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

/-- A globally coherent choice of tableau bases and one-step branching
isomorphisms. -/
structure SpechtBranchingBasisData where
  /-- The coherent basis indexed by standard tableaux. -/
  basis : ∀ {n : ℕ} (μ : YoungDiagramOfSize n),
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ)
  /-- The branching isomorphism compatible with those bases. -/
  branchingIso : ∀ {n : ℕ} (μ : YoungDiagramOfSize (n + 1)),
    (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
      ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val
  /-- Deleting the largest tableau entry selects the corresponding summand. -/
  branchingIso_basis : ∀ {n : ℕ} (μ : YoungDiagramOfSize (n + 1))
      (T : StandardYoungTableau μ),
    FDRep.isoToLinearEquiv (branchingIso μ) (basis μ T) =
      (biproduct.ι (fun ν : OneBoxRemoval μ => spechtModule ν.val)
        T.largestRemoval).hom.hom.hom
          (basis T.largestRemoval.val T.restrictLargest)

/-- The coherent branching data used throughout the package.

Vershik and Okounkov, *A New Approach to the Representation Theory of the
Symmetric Groups II*, Section 1 and Theorem 5.8, construct the path-indexed
Gelfand--Tsetlin basis for the Young graph. Geetha and Prasad, *Comparison of
Gelfand--Tsetlin Bases for Alternating and Symmetric Groups*, Section 2,
equations (1) and (3)--(4), give the corresponding coherent embeddings.
Rescaling each chosen path vector makes the displayed branching coefficient
equal to one. Lean labels tableaux by `Fin n`, so deleting the classical entry
`n` is `StandardYoungTableau.restrictLargest`. -/
axiom spechtBranchingBasisData : SpechtBranchingBasisData

/-- The coherent tableau basis selected by the branching data. -/
noncomputable def spechtCoherentBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ) :=
  spechtBranchingBasisData.basis μ

/-- Established API name for the coherent tableau basis used by the later
Young orthogonal-form development. -/
noncomputable def spechtOrthogonalBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ) :=
  spechtCoherentBasis μ

/-- The one coherent branching isomorphism used by all later constructions. -/
noncomputable def spechtBranchingIso {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
      ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val :=
  spechtBranchingBasisData.branchingIso μ

/-- The chosen branching isomorphism sends a tableau basis vector to the
summand selected by deleting its largest entry. -/
theorem spechtBranchingIso_basis {n : ℕ} (μ : YoungDiagramOfSize (n + 1))
    (T : StandardYoungTableau μ) :
    FDRep.isoToLinearEquiv (spechtBranchingIso μ) (spechtOrthogonalBasis μ T) =
      (biproduct.ι (fun ν : OneBoxRemoval μ => spechtModule ν.val)
        T.largestRemoval).hom.hom.hom
          (spechtOrthogonalBasis T.largestRemoval.val T.restrictLargest) :=
  spechtBranchingBasisData.branchingIso_basis μ T

/-- The coherent two-step branching isomorphism obtained by iterating the
chosen one-step isomorphism. -/
noncomputable def spechtBranchingIso_twoSteps {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ≅
      ⨁ fun p : TwoStepRemoval μ => spechtModule p.2.val :=
  (SymmetricGroupRepresentation.restriction n).mapIso (spechtBranchingIso μ) ≪≫
    (SymmetricGroupRepresentation.restriction n).mapBiproduct
      (fun ν : OneBoxRemoval μ => spechtModule ν.val) ≪≫
    biproduct.mapIso (fun ν : OneBoxRemoval μ => spechtBranchingIso ν.val) ≪≫
    biproductBiproductIso
      (fun ν : OneBoxRemoval μ => OneBoxRemoval ν.val)
      (fun _ ξ => spechtModule ξ.val)

/-- The coherent three-step branching isomorphism obtained by iterating the
chosen one-step isomorphism. -/
noncomputable def spechtBranchingIso_threeSteps {n : ℕ}
    (μ : YoungDiagramOfSize (n + 3)) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj
          ((SymmetricGroupRepresentation.restriction (n + 2)).obj (spechtModule μ))) ≅
      ⨁ fun p : ThreeStepRemoval μ => spechtModule p.2.2.val := by
  let F := SymmetricGroupRepresentation.restriction (n + 1) ⋙
    SymmetricGroupRepresentation.restriction n
  exact F.mapIso (spechtBranchingIso μ) ≪≫
    F.mapBiproduct (fun ν : OneBoxRemoval μ => spechtModule ν.val) ≪≫
    biproduct.mapIso (fun ν : OneBoxRemoval μ =>
      spechtBranchingIso_twoSteps ν.val) ≪≫
    biproductBiproductIso
      (fun ν : OneBoxRemoval μ => TwoStepRemoval ν.val)
      (fun _ p => spechtModule p.2.val)

/-- The coherent two-step branching isomorphism, regrouped by endpoint. -/
noncomputable def spechtBranchingIso_twoSteps_byEndpoint {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ≅
      ⨁ fun ν : YoungDiagramOfSize n =>
        ⨁ fun _ : TwoStepRemovalTo μ ν => spechtModule ν := by
  let endpoint := fun p : TwoStepRemoval μ => p.2.val
  let fibers := fun ν : YoungDiagramOfSize n =>
    {p : TwoStepRemoval μ // endpoint p = ν}
  let reindex :
      (⨁ fun p : TwoStepRemoval μ => spechtModule p.2.val) ≅
        ⨁ fun q : Σ ν, fibers ν => spechtModule q.1 :=
    biproduct.reindex (Equiv.sigmaFiberEquiv endpoint).symm
      (fun q : Σ ν, fibers ν => spechtModule q.1)
  exact spechtBranchingIso_twoSteps μ ≪≫ reindex ≪≫
    (biproductBiproductIso fibers (fun ν _ => spechtModule ν)).symm

/-- The coherent three-step branching isomorphism, regrouped by endpoint. -/
noncomputable def spechtBranchingIso_threeSteps_byEndpoint {n : ℕ}
    (μ : YoungDiagramOfSize (n + 3)) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj
          ((SymmetricGroupRepresentation.restriction (n + 2)).obj (spechtModule μ))) ≅
      ⨁ fun ν : YoungDiagramOfSize n =>
        ⨁ fun _ : ThreeStepRemovalTo μ ν => spechtModule ν := by
  let endpoint := fun p : ThreeStepRemoval μ => p.2.2.val
  let fibers := fun ν : YoungDiagramOfSize n =>
    {p : ThreeStepRemoval μ // endpoint p = ν}
  let reindex :
      (⨁ fun p : ThreeStepRemoval μ => spechtModule p.2.2.val) ≅
        ⨁ fun q : Σ ν, fibers ν => spechtModule q.1 :=
    biproduct.reindex (Equiv.sigmaFiberEquiv endpoint).symm
      (fun q : Σ ν, fibers ν => spechtModule q.1)
  exact spechtBranchingIso_threeSteps μ ≪≫ reindex ≪≫
    (biproductBiproductIso fibers (fun ν _ => spechtModule ν)).symm
