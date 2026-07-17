import SymmetricGroupRep.Classification
import SymmetricGroupRep.OuterTensor

open CategoryTheory

/-! # Irreducible representations of products of symmetric groups -/

/-- The outer tensor product `S^μ ⊠ S^ν`. -/
noncomputable abbrev spechtOuterTensor {m n : ℕ}
    (μ : YoungDiagramOfSize m) (ν : YoungDiagramOfSize n) :
    FDRep ℂ (SymmetricGroup m × SymmetricGroup n) :=
  FDRep.outerTensor (spechtModule μ) (spechtModule ν)

/-- An outer tensor product of complex Specht modules is irreducible. -/
theorem spechtOuterTensor_irreducible {m n : ℕ}
    (μ : YoungDiagramOfSize m) (ν : YoungDiagramOfSize n) :
    Simple (spechtOuterTensor μ ν) := by
  letI : Simple (spechtModule μ) := spechtModule_irreducible μ
  letI : Simple (spechtModule ν) := spechtModule_irreducible ν
  exact FDRep.simple_outerTensor (spechtModule μ) (spechtModule ν)

/-- Every irreducible complex representation of `S_m × S_n` has a unique pair of
Specht labels.

This is Kowalski, *Representation Theory*, Proposition 2.3.23, specialized to
`G₁ = S_m`, `G₂ = S_n`, and `k = ℂ`, together with the Specht classification.
It also follows from Etingof et al., *Introduction to Representation Theory*,
Theorem 3.10.2, applied to the two complex group algebras. -/
axiom existsUnique_iso_spechtOuterTensor {m n : ℕ}
    (V : FDRep ℂ (SymmetricGroup m × SymmetricGroup n)) [Simple V] :
    ∃! p : YoungDiagramOfSize m × YoungDiagramOfSize n,
      Nonempty (V ≅ spechtOuterTensor p.1 p.2)

/-- Every irreducible complex representation of `S_m × S_n` is an outer tensor
product of Specht modules. -/
theorem exists_iso_spechtOuterTensor {m n : ℕ}
    (V : FDRep ℂ (SymmetricGroup m × SymmetricGroup n)) [Simple V] :
    ∃ μ : YoungDiagramOfSize m, ∃ ν : YoungDiagramOfSize n,
      Nonempty (V ≅ spechtOuterTensor μ ν) := by
  obtain ⟨⟨μ, ν⟩, h, _⟩ := existsUnique_iso_spechtOuterTensor V
  exact ⟨μ, ν, h⟩

/-- Outer tensor products of Specht modules are isomorphic exactly when both
Young-diagram labels agree. -/
theorem spechtOuterTensor_iso_iff_eq {m n : ℕ}
    (μ μ' : YoungDiagramOfSize m) (ν ν' : YoungDiagramOfSize n) :
    Nonempty (spechtOuterTensor μ ν ≅ spechtOuterTensor μ' ν') ↔
      μ = μ' ∧ ν = ν' := by
  constructor
  · intro e
    letI : Simple (spechtOuterTensor μ ν) := spechtOuterTensor_irreducible μ ν
    obtain ⟨p, _, hp⟩ := existsUnique_iso_spechtOuterTensor (spechtOuterTensor μ ν)
    have h₁ : (μ, ν) = p := hp (μ, ν) ⟨Iso.refl _⟩
    have h₂ : (μ', ν') = p := hp (μ', ν') e
    have h : (μ, ν) = (μ', ν') := h₁.trans h₂.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Iso.refl _⟩
