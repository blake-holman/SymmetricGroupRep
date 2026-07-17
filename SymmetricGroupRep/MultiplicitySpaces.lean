import SymmetricGroupRep.BranchingOperators
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Multiplicity spaces and Schur reductions -/

open CategoryTheory
open scoped Classical

/-- The multiplicity space of `S^μ` in a symmetric-group representation `V`. -/
abbrev SpechtMultiplicitySpace {n : ℕ} (μ : YoungDiagramOfSize n)
    (V : SymmetricGroupRepresentation n) :=
  spechtModule μ ⟶ V

/-- The multiplicity space between two Specht modules has dimension one for
equal labels and zero otherwise. -/
theorem spechtMultiplicitySpace_finrank {n : ℕ}
    (μ ν : YoungDiagramOfSize n) :
    Module.finrank ℂ (SpechtMultiplicitySpace μ (spechtModule ν)) =
      if μ = ν then 1 else 0 := by
  letI := spechtModule_irreducible μ
  letI := spechtModule_irreducible ν
  rw [CategoryTheory.finrank_hom_simple_simple]
  simp [spechtModule_iso_iff_eq]

/-- Schur's lemma makes every Specht endomorphism scalar. -/
theorem spechtEndomorphism_eq_smul_id {n : ℕ}
    (μ : YoungDiagramOfSize n) (f : spechtModule μ ⟶ spechtModule μ) :
    ∃ c : ℂ, f = c • 𝟙 (spechtModule μ) := by
  letI := spechtModule_irreducible μ
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
  exact ⟨c, hc.symm⟩

/-- A morphism between differently labeled Specht modules is zero. -/
theorem spechtHom_eq_zero_of_ne {n : ℕ}
    {μ ν : YoungDiagramOfSize n} (h : μ ≠ ν)
    (f : spechtModule μ ⟶ spechtModule ν) : f = 0 := by
  letI := spechtModule_irreducible μ
  letI := spechtModule_irreducible ν
  by_contra hf
  haveI := CategoryTheory.isIso_of_hom_simple hf
  exact h ((spechtModule_iso_iff_eq μ ν).mp ⟨asIso f⟩)

/-- A matrix entry of an endomorphism in a fixed two-step endpoint block. -/
noncomputable def twoStepBranchingBlockEntry {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)))
    (p q : TwoStepRemovalTo μ ν) : spechtModule ν ⟶ spechtModule ν :=
  twoStepBranchingInclusion μ ν p ≫ A ≫ twoStepBranchingProjection μ ν q

/-- Every entry within one endpoint block is a scalar. -/
theorem twoStepBranchingBlockEntry_eq_smul_id {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)))
    (p q : TwoStepRemovalTo μ ν) :
    ∃ c : ℂ, twoStepBranchingBlockEntry μ ν A p q =
      c • 𝟙 (spechtModule ν) :=
  spechtEndomorphism_eq_smul_id ν _

/-- The scalar matrix induced by an endomorphism on the multiplicity space of
one endpoint. -/
noncomputable def twoStepMultiplicityMatrix {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ))) :
    TwoStepRemovalTo μ ν → TwoStepRemovalTo μ ν → ℂ :=
  fun p q => Classical.choose (twoStepBranchingBlockEntry_eq_smul_id μ ν A p q)

@[simp]
theorem twoStepBranchingBlockEntry_eq_matrix_smul_id {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)))
    (p q : TwoStepRemovalTo μ ν) :
    twoStepBranchingBlockEntry μ ν A p q =
      twoStepMultiplicityMatrix μ ν A p q • 𝟙 (spechtModule ν) :=
  Classical.choose_spec (twoStepBranchingBlockEntry_eq_smul_id μ ν A p q)

/-- Any independently computed scalar for a block entry is the chosen matrix
coefficient. -/
theorem twoStepMultiplicityMatrix_eq_of_blockEntry_eq_smul_id {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) (ν : YoungDiagramOfSize n)
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)))
    (p q : TwoStepRemovalTo μ ν) (c : ℂ)
    (h : twoStepBranchingBlockEntry μ ν A p q = c • 𝟙 (spechtModule ν)) :
    twoStepMultiplicityMatrix μ ν A p q = c := by
  letI := spechtModule_irreducible ν
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (spechtModule ν))
  exact (twoStepBranchingBlockEntry_eq_matrix_smul_id μ ν A p q).symm.trans h

/-- Entries between distinct endpoint blocks vanish. -/
theorem twoStepBranching_crossEndpoint_eq_zero {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2))
    {ν ξ : YoungDiagramOfSize n} (h : ν ≠ ξ)
    (A :
      (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)) ⟶
        (SymmetricGroupRepresentation.restriction n).obj
          ((SymmetricGroupRepresentation.restriction (n + 1)).obj (spechtModule μ)))
    (p : TwoStepRemovalTo μ ν) (q : TwoStepRemovalTo μ ξ) :
    twoStepBranchingInclusion μ ν p ≫ A ≫
      twoStepBranchingProjection μ ξ q = 0 :=
  spechtHom_eq_zero_of_ne h _
