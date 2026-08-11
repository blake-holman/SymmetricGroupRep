import SymmetricGroupRep.Classification
import SymmetricGroupRep.OuterTensor

open CategoryTheory

/-! # Irreducible representations of products of symmetric groups

The outer tensor products of Specht modules are simple, pairwise non-isomorphic, and as numerous
as the conjugacy classes of `S_m × S_n`, so they exhaust the simples exactly as the Specht modules
themselves do for a single symmetric group. Both counts are read through
`FDRep.card_le_card_conjClasses`, which is why the conjugacy classes of a product group are
identified with pairs of conjugacy classes here.
-/

attribute [local instance] IsConj.setoid

/-- Two elements of a product group are conjugate exactly when their components are. -/
theorem isConj_prod_iff {G H : Type} [Group G] [Group H] (a b : G × H) :
    IsConj a b ↔ IsConj a.1 b.1 ∧ IsConj a.2 b.2 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact ⟨isConj_iff.mpr ⟨c.1, congrArg Prod.fst hc⟩,
      isConj_iff.mpr ⟨c.2, congrArg Prod.snd hc⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨c₁, hc₁⟩ := isConj_iff.mp h₁
    obtain ⟨c₂, hc₂⟩ := isConj_iff.mp h₂
    exact isConj_iff.mpr ⟨(c₁, c₂), Prod.ext hc₁ hc₂⟩

/-- The conjugacy classes of a product group are the pairs of conjugacy classes. -/
def ConjClasses.prodEquiv {G H : Type} [Group G] [Group H] :
    ConjClasses (G × H) ≃ ConjClasses G × ConjClasses H where
  toFun := Quotient.lift (fun a => (ConjClasses.mk a.1, ConjClasses.mk a.2)) fun a b h =>
    Prod.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr ((isConj_prod_iff a b).mp h).1)
      (ConjClasses.mk_eq_mk_iff_isConj.mpr ((isConj_prod_iff a b).mp h).2)
  invFun p := Quotient.liftOn₂ p.1 p.2 (fun a b => ConjClasses.mk (a, b)) fun a b a' b' ha hb =>
    ConjClasses.mk_eq_mk_iff_isConj.mpr ((isConj_prod_iff (a, b) (a', b')).mpr ⟨ha, hb⟩)
  left_inv := by rintro ⟨a⟩; rfl
  right_inv := by rintro ⟨⟨a⟩, ⟨b⟩⟩; rfl

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

/-- Outer tensor products of Specht modules are isomorphic exactly when both
Young-diagram labels agree.

Schur's lemma reads an isomorphism as a one-dimensional Hom space, and
`FDRep.finrank_hom_outerTensor` splits that dimension into the product of the two factorwise Hom
dimensions, each of which is therefore one. -/
theorem spechtOuterTensor_iso_iff_eq {m n : ℕ}
    (μ μ' : YoungDiagramOfSize m) (ν ν' : YoungDiagramOfSize n) :
    Nonempty (spechtOuterTensor μ ν ≅ spechtOuterTensor μ' ν') ↔
      μ = μ' ∧ ν = ν' := by
  refine ⟨fun e => ?_, by rintro ⟨rfl, rfl⟩; exact ⟨Iso.refl _⟩⟩
  letI := spechtOuterTensor_irreducible μ ν
  letI := spechtOuterTensor_irreducible μ' ν'
  letI := spechtModule_irreducible μ
  letI := spechtModule_irreducible μ'
  letI := spechtModule_irreducible ν
  letI := spechtModule_irreducible ν'
  have hone : Module.finrank ℂ (spechtModule μ ⟶ spechtModule μ') *
      Module.finrank ℂ (spechtModule ν ⟶ spechtModule ν') = 1 := by
    rw [← FDRep.finrank_hom_outerTensor]
    simp [FDRep.finrank_hom_simple_simple, e]
  have hμ := Nat.eq_one_of_mul_eq_one_right hone
  have hν := Nat.eq_one_of_mul_eq_one_left hone
  refine ⟨(spechtModule_iso_iff_eq μ μ').mp ?_, (spechtModule_iso_iff_eq ν ν').mp ?_⟩
  · by_contra hc
    rw [FDRep.finrank_hom_simple_simple, if_neg hc] at hμ
    exact absurd hμ (by norm_num)
  · by_contra hc
    rw [FDRep.finrank_hom_simple_simple, if_neg hc] at hν
    exact absurd hν (by norm_num)

/-- Every irreducible complex representation of `S_m × S_n` has a unique pair of
Specht labels.

This is Kowalski, *Representation Theory*, Proposition 2.3.23, specialized to
`G₁ = S_m`, `G₂ = S_n`, and `k = ℂ`, together with the Specht classification.
It also follows from Etingof et al., *Introduction to Representation Theory*,
Theorem 3.10.2, applied to the two complex group algebras. -/
theorem existsUnique_iso_spechtOuterTensor {m n : ℕ}
    (V : FDRep ℂ (SymmetricGroup m × SymmetricGroup n)) [Simple V] :
    ∃! p : YoungDiagramOfSize m × YoungDiagramOfSize n,
      Nonempty (V ≅ spechtOuterTensor p.1 p.2) := by
  -- The pairs of Specht modules already exhaust the conjugacy-class count of `S_m × S_n`, so no
  -- further simple can be adjoined to them.
  have hcount : Nat.card (YoungDiagramOfSize m × YoungDiagramOfSize n) =
      Nat.card (ConjClasses (SymmetricGroup m × SymmetricGroup n)) := by
    rw [Nat.card_congr ConjClasses.prodEquiv, Nat.card_prod, Nat.card_prod,
      Nat.card_congr (SymmetricGroup.conjClassesEquivPartition m),
      Nat.card_congr (SymmetricGroup.conjClassesEquivPartition n),
      Nat.card_congr (YoungDiagramOfSize.equivPartition m),
      Nat.card_congr (YoungDiagramOfSize.equivPartition n)]
  have hexists : ∃ p : YoungDiagramOfSize m × YoungDiagramOfSize n,
      Nonempty (V ≅ spechtOuterTensor p.1 p.2) := by
    by_contra hV
    rw [not_exists] at hV
    have hcard : Nat.card (Option (YoungDiagramOfSize m × YoungDiagramOfSize n)) ≤
        Nat.card (ConjClasses (SymmetricGroup m × SymmetricGroup n)) := by
      refine FDRep.card_le_card_conjClasses
        (fun i => i.elim V fun p => spechtOuterTensor p.1 p.2) ?_ ?_
      · rintro (_ | p)
        · exact ‹Simple V›
        · exact spechtOuterTensor_irreducible p.1 p.2
      · rintro (_ | p) (_ | q) h
        · rfl
        · exact absurd h (hV q)
        · exact absurd (h.map Iso.symm) (hV p)
        · obtain ⟨h₁, h₂⟩ := (spechtOuterTensor_iso_iff_eq p.1 q.1 p.2 q.2).mp h
          exact congrArg some (Prod.ext h₁ h₂)
    rw [Finite.card_option, hcount] at hcard
    omega
  obtain ⟨p, hp⟩ := hexists
  refine ⟨p, hp, fun q hq => ?_⟩
  rcases hp with ⟨ep⟩
  rcases hq with ⟨eq⟩
  obtain ⟨h₁, h₂⟩ := (spechtOuterTensor_iso_iff_eq q.1 p.1 q.2 p.2).mp ⟨eq.symm ≪≫ ep⟩
  exact Prod.ext h₁ h₂

/-- Every irreducible complex representation of `S_m × S_n` is an outer tensor
product of Specht modules. -/
theorem exists_iso_spechtOuterTensor {m n : ℕ}
    (V : FDRep ℂ (SymmetricGroup m × SymmetricGroup n)) [Simple V] :
    ∃ μ : YoungDiagramOfSize m, ∃ ν : YoungDiagramOfSize n,
      Nonempty (V ≅ spechtOuterTensor μ ν) := by
  obtain ⟨⟨μ, ν⟩, h, _⟩ := existsUnique_iso_spechtOuterTensor V
  exact ⟨μ, ν, h⟩
