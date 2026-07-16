import SymmetricGroupRep.Classification
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Embedding
import Mathlib.GroupTheory.Perm.ViaEmbedding

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- The standard inclusion `S_n → S_(n+1)`, which fixes the final point. -/
noncomputable def SymmetricGroup.inclusion (n : ℕ) :
    SymmetricGroup n →* SymmetricGroup (n + 1) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

/-- Restriction from representations of `S_(n+1)` to representations of `S_n`. -/
noncomputable abbrev SymmetricGroupRepresentation.restriction (n : ℕ) :
    SymmetricGroupRepresentation (n + 1) ⥤ SymmetricGroupRepresentation n :=
  Action.res (FGModuleCat ℂ) (SymmetricGroup.inclusion n)

/-- `μ` is obtained from `λ` by removing one box.

Because their sizes are already `n` and `n + 1`, containment is enough to express this. -/
def IsOneBoxRemoval {n : ℕ}
    (ν : YoungDiagramOfSize n) (μ : YoungDiagramOfSize (n + 1)) : Prop :=
  ν.val ≤ μ.val

/-- A Young diagram obtained from `λ` by removing one box. -/
abbrev OneBoxRemoval {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :=
  { ν : YoungDiagramOfSize n // IsOneBoxRemoval ν μ }

noncomputable instance {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
    Finite (OneBoxRemoval μ) := by
  let cells : OneBoxRemoval μ → ↥μ.val.cells.powerset := fun ν =>
    ⟨ν.val.val.cells, Finset.mem_powerset.mpr
      (YoungDiagram.cells_subset_iff.mpr ν.property)⟩
  exact Finite.of_injective cells fun ν ξ h => by
    apply Subtype.ext
    apply Subtype.ext
    exact YoungDiagram.ext (congrArg Subtype.val h)

/-- Restricting `S^λ` from `S_(n+1)` to `S_n` gives the multiplicity-free direct sum of
the Specht modules obtained by removing one box from `λ`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.8.3. -/
axiom spechtModule_branching {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) :
  Nonempty ((SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
    ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val)
