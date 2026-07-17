import SymmetricGroupRep.Classification

open CategoryTheory
open scoped MonoidalCategory

/-! # Self-duality of complex Specht modules -/

/-- Every complex Specht module is isomorphic to its rigid dual.

For a finite group, the dual character is `g ↦ χ(g⁻¹)`. In a symmetric group,
`g` and `g⁻¹` have the same cycle type and hence are conjugate, so every
character equals its dual character. The result follows from Etingof et al.,
*Introduction to Representation Theory*, Corollary 4.2.4, specialized under the
book's standing algebraically-closed-field convention to `ℂ`: finite-dimensional
complex representations of a finite group are determined by their characters.
Here `Vᘁ` is mathlib's right rigid dual, whose action is the linear dual of the
action of `g⁻¹`. -/
axiom spechtModule_selfDual {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (spechtModule μ ≅ (spechtModule μ)ᘁ)
