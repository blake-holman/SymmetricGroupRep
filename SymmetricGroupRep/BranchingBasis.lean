import SymmetricGroupRep.Branching
import SymmetricGroupRep.YoungBranching
import SymmetricGroupRep.Tableaux
import Mathlib.Logic.Equiv.Fin.Basic

/-! # A coherent Young branching basis -/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts


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
noncomputable def spechtBranchingBasisData : SpechtBranchingBasisData :=
  ⟨fun {_} μ => spechtYoungBasis μ, fun {_} μ => spechtYoungBranchingIso μ,
    fun {_} μ T => spechtYoungBranchingIso_basis μ T⟩

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
