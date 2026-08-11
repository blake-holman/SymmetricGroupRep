import SymmetricGroupRep.Semisimple
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Counting pairwise non-isomorphic simples

Mathlib proves the characters of simple complex representations of a finite group orthonormal
(`FDRep.char_orthonormal`) but does not draw the classical consequence. A character is constant
on conjugacy classes, so orthonormality makes the characters of pairwise non-isomorphic simples
a linearly independent family in the functions on `ConjClasses G`, a space of dimension
`Nat.card (ConjClasses G)`.

The resulting bound is what turns a supply of pairwise non-isomorphic simples into a
classification: once a supply has as many members as `G` has conjugacy classes, no further
simple can be adjoined to it.
-/

open CategoryTheory

attribute [local instance] IsConj.setoid

/-- The character of a finite-dimensional complex representation, read on conjugacy classes. -/
noncomputable def FDRep.classCharacter {G : Type} [Group G] (V : FDRep ℂ G) :
    ConjClasses G → ℂ :=
  Quotient.lift V.character fun a c h => by
    obtain ⟨b, rfl⟩ := isConj_iff.mp h
    exact (V.char_conj a b).symm

@[simp]
theorem FDRep.classCharacter_mk {G : Type} [Group G] (V : FDRep ℂ G) (g : G) :
    V.classCharacter (ConjClasses.mk g) = V.character g := rfl

/-- A family of pairwise non-isomorphic simple complex representations of a finite group has at
most as many members as the group has conjugacy classes. -/
theorem FDRep.card_le_card_conjClasses {G ι : Type} [Group G] [Finite G] [Finite ι]
    (S : ι → FDRep ℂ G) (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j) :
    Nat.card ι ≤ Nat.card (ConjClasses G) := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite (ConjClasses G)
  have hli : LinearIndependent ℂ fun i => (S i).classCharacter := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpt : ∀ g : G, ∑ i, c i * (S i).character g = 0 := fun g => by
      simpa using congrFun hc (ConjClasses.mk g)
    have horth : ∀ i, ⅟(Fintype.card G : ℂ) *
        ∑ g : G, (S i).character g * (S j).character g⁻¹ = if i = j then 1 else 0 := by
      intro i
      haveI := hsimple i
      haveI := hsimple j
      rw [← smul_eq_mul, FDRep.char_orthonormal]
      by_cases hij : i = j
      · subst hij
        rw [if_pos ⟨Iso.refl _⟩, if_pos rfl]
      · rw [if_neg hij, if_neg fun h => hij (hdistinct i j h)]
    have expand : ∑ g : G, (∑ i, c i * (S i).character g) * (S j).character g⁻¹
        = ∑ i, c i * ∑ g : G, (S i).character g * (S j).character g⁻¹ := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    calc c j = ∑ i, c i * (if i = j then (1 : ℂ) else 0) := by simp
      _ = ⅟(Fintype.card G : ℂ) *
            ∑ g : G, (∑ i, c i * (S i).character g) * (S j).character g⁻¹ := by
          rw [expand, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [← horth i]; ring
      _ = 0 := by simp [hpt]
  calc Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
    _ ≤ Module.finrank ℂ (ConjClasses G → ℂ) := hli.fintype_card_le_finrank
    _ = Fintype.card (ConjClasses G) := Module.finrank_pi ℂ
    _ = Nat.card (ConjClasses G) := Nat.card_eq_fintype_card.symm
