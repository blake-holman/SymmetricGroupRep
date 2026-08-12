import SymmetricGroupRep.BranchingBasis
import SymmetricGroupRep.TableauContent
import Mathlib.Analysis.RCLike.Sqrt

/-! # Young's orthogonal form -/

open scoped Classical

/-- The coherent tableau basis is Young's orthogonal basis. -/
theorem spechtOrthogonalBasis_apply {n : ℕ} (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ) : spechtOrthogonalBasis μ T = spechtYoungBasisVector μ T :=
  spechtYoungBasis_apply μ T

/-- The swapped orthogonal-basis vector, interpreted as zero when the adjacent
swap is not standard. -/
noncomputable def swappedOrthogonalBasisVector {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    spechtModule μ :=
  if h : T.IsAdjacentSwapStandard i then
    spechtOrthogonalBasis μ (T.swapAdjacent i h)
  else
    0

/-- Young's orthogonal action formula for an adjacent transposition.

Armon and Halverson, *Transition Matrices between Young's Natural and
Seminormal Representations*, EJC 28(3) (2021), Section 3.1, equations
(3.1)--(3.2), defines content and axial distance, and Section 3.3, equation
(3.4) (DOI `10.37236/10081`), gives this orthogonal action. The convention was
cross-checked against Geetha and Prasad, *Comparison of Gelfand--Tsetlin Bases
for Alternating and Symmetric Groups*, Section 2, equation (2)
(arXiv:1606.04424). Lean index `i` swaps zero-based labels `i,i+1`, which
correspond to classical labels `i+1,i+2` and the generator `s_(i+1)`. -/
theorem spechtOrthogonalBasis_adjacentTransposition {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
        (spechtOrthogonalBasis μ T) =
      ((T.axialDistance i : ℂ)⁻¹) • spechtOrthogonalBasis μ T +
        Complex.sqrt (1 - ((T.axialDistance i : ℂ)⁻¹) ^ 2) •
          swappedOrthogonalBasisVector μ T i := by
  have hswapped : swappedOrthogonalBasisVector μ T i =
      (if h : T.IsAdjacentSwapStandard i then spechtYoungBasisVector μ (T.swapAdjacent i h)
        else 0) := by
    rw [swappedOrthogonalBasisVector]
    by_cases h : T.IsAdjacentSwapStandard i
    · rw [dif_pos h, dif_pos h, spechtOrthogonalBasis_apply]
    · rw [dif_neg h, dif_neg h]
  rw [hswapped, spechtOrthogonalBasis_apply]
  exact rho_adjacentTransposition_spechtYoungBasisVector μ T i
