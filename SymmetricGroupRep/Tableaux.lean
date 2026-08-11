import SymmetricGroupRep.RegularDecomposition
import SymmetricGroupRep.StandardIndependence
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Standard Young tableaux and Specht bases -/

/-- The standard tableaux of shape `μ` index a basis of the Specht module `S^μ`.

This is Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.5.2 (the Standard
Basis Theorem, DOI `10.1007/978-1-4757-6804-6_2`). Classical labels
`1, ..., n` are shifted to the order-isomorphic type `Fin n`; rows and columns
use mathlib's top-left, zero-based cell coordinates. The statement records only
existence because `spechtModule μ` is an abstract representative of its
isomorphism class. -/
theorem exists_spechtTableauBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ)) := by
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  have hsum : ∑ ν : YoungDiagramOfSize n, Nat.card (StandardYoungTableau ν) ^ 2 =
      ∑ ν : YoungDiagramOfSize n, Module.finrank ℂ (spechtModule ν) ^ 2 := by
    rw [sum_card_standardYoungTableau_sq, sum_finrank_spechtModule_sq]
  have hsq := (Finset.sum_eq_sum_iff_of_le fun ν _ =>
    Nat.pow_le_pow_left (card_standardYoungTableau_le_finrank ν) 2).mp hsum μ (Finset.mem_univ μ)
  have hcard : Fintype.card (StandardYoungTableau μ) = Module.finrank ℂ (spechtModule μ) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.pow_left_injective (by norm_num) hsq
  haveI : Nontrivial (spechtModule μ : Type) :=
    Submodule.nontrivial_iff_ne_bot.mpr (spechtSubrepresentation_ne_bot μ)
  haveI : Nonempty (StandardYoungTableau μ) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; exact Module.finrank_pos)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_spechtStandardFamily μ) hcard⟩

/-- A chosen standard-tableau basis of `S^μ`. -/
noncomputable def spechtTableauBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ) :=
  Classical.choice (exists_spechtTableauBasis μ)

/-- Removing one box splits the dimension of a Specht module. This is the numerical content of
the branching rule, and it holds independently of it: both sides count standard tableaux. -/
theorem finrank_spechtModule_eq_sum_oneBoxRemovals {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    Module.finrank ℂ (spechtModule μ) =
      ∑ ν ∈ oneBoxRemovals μ, Module.finrank ℂ (spechtModule ν) := by
  rw [Module.finrank_eq_nat_card_basis (spechtTableauBasis μ), card_standardYoungTableau_succ]
  exact Finset.sum_congr rfl fun ν _ =>
    (Module.finrank_eq_nat_card_basis (spechtTableauBasis ν)).symm
