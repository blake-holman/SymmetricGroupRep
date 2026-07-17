import SymmetricGroupRep.YoungDiagrams
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.RepresentationTheory.FDRep

open CategoryTheory

/-- The symmetric group on `n` elements. -/
abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- A finite-dimensional complex representation of the symmetric group on `n` elements. -/
abbrev SymmetricGroupRepresentation (n : ℕ) := FDRep ℂ (SymmetricGroup n)

/-- An abstract choice of the complex Specht module `S^μ`.

See Sagan, *The Symmetric Group*, 2nd ed., Section 2.3. -/
axiom spechtModule {n : ℕ} (μ : YoungDiagramOfSize n) : SymmetricGroupRepresentation n

/-- Every complex Specht module is irreducible.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
axiom spechtModule_irreducible {n : ℕ} (μ : YoungDiagramOfSize n) : Simple (spechtModule μ)

/-- Complex Specht modules are isomorphic exactly when their Young diagrams agree.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
axiom spechtModule_iso_iff_eq {n : ℕ} (μ ν : YoungDiagramOfSize n) :
  Nonempty (spechtModule μ ≅ spechtModule ν) ↔ μ = ν

/-- Every irreducible complex representation of `S_n` is isomorphic to a Specht module.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
axiom exists_iso_spechtModule {n : ℕ} (V : SymmetricGroupRepresentation n) [Simple V] :
  ∃ μ : YoungDiagramOfSize n, Nonempty (V ≅ spechtModule μ)

/-- Every irreducible representation has a unique indexing Young diagram. -/
theorem existsUnique_iso_spechtModule {n : ℕ} (V : SymmetricGroupRepresentation n) [Simple V] :
    ∃! μ : YoungDiagramOfSize n, Nonempty (V ≅ spechtModule μ) := by
  obtain ⟨μ, hμ⟩ := exists_iso_spechtModule V
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  rcases hμ with ⟨eμ⟩
  rcases hν with ⟨eν⟩
  exact (spechtModule_iso_iff_eq ν μ).mp ⟨eν.symm ≪≫ eμ⟩
