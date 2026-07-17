import SymmetricGroupRep.BranchingBasis

/-! # Operators on repeated branching summands -/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Classical

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- Inclusion of one path-indexed copy of `S^ν` in the coherent two-step
branching decomposition. -/
noncomputable def twoStepBranchingInclusion {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p : TwoStepRemovalTo μ ν) :
    spechtModule ν ⟶
      (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) :=
  biproduct.ι (fun _ : TwoStepRemovalTo μ ν => spechtModule ν) p ≫
    biproduct.ι
      (fun ξ : YoungDiagramOfSize n =>
        ⨁ fun _ : TwoStepRemovalTo μ ξ => spechtModule ξ) ν ≫
    (spechtBranchingIso_twoSteps_byEndpoint μ).inv

/-- Projection onto one path-indexed copy of `S^ν` in the coherent two-step
branching decomposition. -/
noncomputable def twoStepBranchingProjection {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p : TwoStepRemovalTo μ ν) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
      spechtModule ν :=
  (spechtBranchingIso_twoSteps_byEndpoint μ).hom ≫
    biproduct.π
      (fun ξ : YoungDiagramOfSize n =>
        ⨁ fun _ : TwoStepRemovalTo μ ξ => spechtModule ξ) ν ≫
    biproduct.π (fun _ : TwoStepRemovalTo μ ν => spechtModule ν) p

/-- A branching inclusion followed by a branching projection is the expected
Kronecker delta. -/
@[simp]
theorem twoStepBranchingInclusion_projection {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p q : TwoStepRemovalTo μ ν) :
    twoStepBranchingInclusion μ ν p ≫ twoStepBranchingProjection μ ν q =
      if p = q then 𝟙 (spechtModule ν) else 0 := by
  classical
  by_cases h : p = q
  · subst q
    simp [twoStepBranchingInclusion, twoStepBranchingProjection, Category.assoc]
  · simp [twoStepBranchingInclusion, twoStepBranchingProjection, Category.assoc, h]

/-- The matrix unit transporting the copy indexed by `p` to the copy indexed
by `q`. -/
noncomputable def twoStepBranchingTransporter {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p q : TwoStepRemovalTo μ ν) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
      (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) :=
  twoStepBranchingProjection μ ν p ≫ twoStepBranchingInclusion μ ν q

/-- The transporters satisfy the matrix-unit multiplication law. -/
@[simp]
theorem twoStepBranchingTransporter_comp {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p q r s : TwoStepRemovalTo μ ν) :
    twoStepBranchingTransporter μ ν p q ≫
        twoStepBranchingTransporter μ ν r s =
      if q = r then twoStepBranchingTransporter μ ν p s else 0 := by
  classical
  simp only [twoStepBranchingTransporter, Category.assoc]
  rw [← Category.assoc (twoStepBranchingInclusion μ ν q)]
  rw [twoStepBranchingInclusion_projection]
  by_cases h : q = r
  · simp [h]
  · simp [h]

/-- The projector onto one path-indexed branching summand. -/
noncomputable def twoStepBranchingProjector {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p : TwoStepRemovalTo μ ν) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
      (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) :=
  twoStepBranchingTransporter μ ν p p

@[simp]
theorem twoStepBranchingProjector_idempotent {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p : TwoStepRemovalTo μ ν) :
    twoStepBranchingProjector μ ν p ≫ twoStepBranchingProjector μ ν p =
      twoStepBranchingProjector μ ν p := by
  simp [twoStepBranchingProjector]

@[simp]
theorem twoStepBranchingProjector_orthogonal {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (p q : TwoStepRemovalTo μ ν) (h : p ≠ q) :
    twoStepBranchingProjector μ ν p ≫ twoStepBranchingProjector μ ν q = 0 := by
  simp [twoStepBranchingProjector, h]

/-- The projector onto the full `ν`-isotypical endpoint block. -/
noncomputable def twoStepEndpointProjector {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n) :
    (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
      (SymmetricGroupRepresentation.restriction n).obj
        ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) := by
  letI := Fintype.ofFinite (TwoStepRemovalTo μ ν)
  exact ∑ p, twoStepBranchingProjector μ ν p

@[simp]
theorem twoStepEndpointProjector_idempotent {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n) :
    twoStepEndpointProjector μ ν ≫ twoStepEndpointProjector μ ν =
      twoStepEndpointProjector μ ν := by
  classical
  letI := Fintype.ofFinite (TwoStepRemovalTo μ ν)
  simp [twoStepEndpointProjector, Preadditive.sum_comp, Preadditive.comp_sum,
    twoStepBranchingProjector]
