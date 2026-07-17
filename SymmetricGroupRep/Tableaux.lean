import SymmetricGroupRep.Classification
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Standard Young tableaux and Specht bases -/

/-- A standard tableau of shape `μ`, with labels `0, ..., n - 1` increasing
from left to right and from top to bottom. -/
@[ext]
structure StandardYoungTableau {n : ℕ} (μ : YoungDiagramOfSize n) where
  /-- The bijective labeling of the cells of `μ`. -/
  entry : ↥μ.val.cells ≃ Fin n
  /-- Labels increase strictly along rows. -/
  row_strict : ∀ {c d}, c.1.1 = d.1.1 → c.1.2 < d.1.2 → entry c < entry d
  /-- Labels increase strictly down columns. -/
  col_strict : ∀ {c d}, c.1.2 = d.1.2 → c.1.1 < d.1.1 → entry c < entry d

/-- There are finitely many standard tableaux of a fixed shape. -/
noncomputable instance {n : ℕ} (μ : YoungDiagramOfSize n) :
    Finite (StandardYoungTableau μ) :=
  Finite.of_injective StandardYoungTableau.entry fun T U h => by
    cases T
    cases U
    cases h
    rfl

/-- The standard tableaux of shape `μ` index a basis of the Specht module `S^μ`.

This is Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.5.2 (the Standard
Basis Theorem, DOI `10.1007/978-1-4757-6804-6_2`). Classical labels
`1, ..., n` are shifted to the order-isomorphic type `Fin n`; rows and columns
use mathlib's top-left, zero-based cell coordinates. The statement records only
existence because `spechtModule μ` is an abstract representative of its
isomorphism class. -/
axiom exists_spechtTableauBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ))

/-- A chosen standard-tableau basis of `S^μ`. -/
noncomputable def spechtTableauBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ) :=
  Classical.choice (exists_spechtTableauBasis μ)
