import SymmetricGroupRep.Induction
import SymmetricGroupRep.Classification
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

/-- Restriction from representations of `S_(n+1)` to representations of `S_n`. -/
noncomputable abbrev SymmetricGroupRepresentation.restriction (n : ℕ) :
    SymmetricGroupRepresentation (n + 1) ⥤ SymmetricGroupRepresentation n :=
  Action.res (FGModuleCat ℂ) (SymmetricGroup.inclusion n)

/-- Induction from representations of `S_n` to representations of `S_(n+1)`. -/
noncomputable abbrev SymmetricGroupRepresentation.induction (n : ℕ) :
    SymmetricGroupRepresentation n ⥤ SymmetricGroupRepresentation (n + 1) :=
  FDRep.indFunctor ℂ (SymmetricGroup.inclusion n)

/-- Restricting `S^λ` from `S_(n+1)` to `S_n` gives the multiplicity-free direct sum of
the Specht modules obtained by removing one box from `λ`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.8.3. -/
axiom spechtModule_branching {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
  Nonempty ((SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val)

/-- Inducing `S^μ` from `S_n` to `S_(n+1)` gives the multiplicity-free direct sum of
the Specht modules obtained by adding one box to `μ`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.8.3. -/
axiom spechtModule_induction_branching {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty ((SymmetricGroupRepresentation.induction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxAddition μ => spechtModule ν.val)

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
