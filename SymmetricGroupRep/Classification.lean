import SymmetricGroupRep.Decomposition
import SymmetricGroupRep.Distinctness
import SymmetricGroupRep.Partitions
import SymmetricGroupRep.SimpleCount
import SymmetricGroupRep.SubmoduleTheorem
import Mathlib.CategoryTheory.Preadditive.Schur

open CategoryTheory

/-- The complex Specht module `S^μ`.

See Sagan, *The Symmetric Group*, 2nd ed., Section 2.3. -/
noncomputable def spechtModule {n : ℕ} (μ : YoungDiagramOfSize n) : SymmetricGroupRepresentation n :=
  FDRep.of (spechtSubrepresentation μ).toRepresentation

/-- Every complex Specht module is irreducible.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
theorem spechtModule_irreducible {n : ℕ} (μ : YoungDiagramOfSize n) : Simple (spechtModule μ) :=
  FDRep.simple_of_isIrreducible _

/-- Schur's lemma makes every Specht endomorphism scalar. -/
theorem spechtEndomorphism_eq_smul_id {n : ℕ}
    (μ : YoungDiagramOfSize n) (f : spechtModule μ ⟶ spechtModule μ) :
    ∃ c : ℂ, f = c • 𝟙 (spechtModule μ) := by
  letI := spechtModule_irreducible μ
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
  exact ⟨c, hc.symm⟩

/-- Complex Specht modules are isomorphic exactly when their Young diagrams agree.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
theorem spechtModule_iso_iff_eq {n : ℕ} (μ ν : YoungDiagramOfSize n) :
  Nonempty (spechtModule μ ≅ spechtModule ν) ↔ μ = ν :=
  ⟨fun ⟨f⟩ => Subtype.ext ((dominates_of_iso_spechtSubrepresentation μ ν f).antisymm
      (dominates_of_iso_spechtSubrepresentation ν μ f.symm)),
    fun h => h ▸ ⟨Iso.refl _⟩⟩

/-- A morphism between differently labeled Specht modules is zero. -/
theorem spechtHom_eq_zero_of_ne {n : ℕ}
    {μ ν : YoungDiagramOfSize n} (h : μ ≠ ν)
    (f : spechtModule μ ⟶ spechtModule ν) : f = 0 := by
  letI := spechtModule_irreducible μ
  letI := spechtModule_irreducible ν
  by_contra hf
  haveI := CategoryTheory.isIso_of_hom_simple hf
  exact h ((spechtModule_iso_iff_eq μ ν).mp ⟨asIso f⟩)

/-- Every irreducible complex representation of `S_n` is isomorphic to a Specht module.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.4.6. -/
theorem exists_iso_spechtModule {n : ℕ} (V : SymmetricGroupRepresentation n) [Simple V] :
  ∃ μ : YoungDiagramOfSize n, Nonempty (V ≅ spechtModule μ) := by
  -- Were `V` isomorphic to no Specht module, adjoining it to the Specht family would give more
  -- pairwise non-isomorphic simples than `S_n` has conjugacy classes.
  by_contra hV
  rw [not_exists] at hV
  have hcard : Nat.card (Option (YoungDiagramOfSize n)) ≤
      Nat.card (ConjClasses (SymmetricGroup n)) := by
    refine FDRep.card_le_card_conjClasses (fun i => i.elim V spechtModule) ?_ ?_
    · rintro (_ | μ)
      · exact ‹Simple V›
      · exact spechtModule_irreducible μ
    · rintro (_ | μ) (_ | ν) h
      · rfl
      · exact absurd h (hV ν)
      · exact absurd (h.map Iso.symm) (hV μ)
      · exact congrArg some ((spechtModule_iso_iff_eq μ ν).mp h)
  rw [Finite.card_option, Nat.card_congr (SymmetricGroup.conjClassesEquivPartition n),
    ← Nat.card_congr (YoungDiagramOfSize.equivPartition n)] at hcard
  omega

/-- The Specht modules are a complete family of pairwise non-isomorphic simples, so a complex
representation of `S_n` is determined up to isomorphism by its character.

This is the converse of mathlib's `FDRep.char_iso`, which mathlib does not have. -/
theorem SymmetricGroupRepresentation.nonempty_iso_of_character_eq {n : ℕ}
    {V W : SymmetricGroupRepresentation n} (h : V.character = W.character) :
    Nonempty (V ≅ W) :=
  FDRep.nonempty_iso_of_character_eq_of_complete spechtModule
    spechtModule_irreducible (fun μ ν => (spechtModule_iso_iff_eq μ ν).mp)
    (fun T hT => @exists_iso_spechtModule n T hT) h

/-- Every irreducible representation has a unique indexing Young diagram. -/
theorem existsUnique_iso_spechtModule {n : ℕ} (V : SymmetricGroupRepresentation n) [Simple V] :
    ∃! μ : YoungDiagramOfSize n, Nonempty (V ≅ spechtModule μ) := by
  obtain ⟨μ, hμ⟩ := exists_iso_spechtModule V
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  rcases hμ with ⟨eμ⟩
  rcases hν with ⟨eν⟩
  exact (spechtModule_iso_iff_eq ν μ).mp ⟨eν.symm ≪≫ eμ⟩
