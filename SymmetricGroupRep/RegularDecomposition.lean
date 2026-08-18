import SymmetricGroupRep.Regular
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # The left-regular Specht decomposition -/

/-- The left-regular representation of `S_n` contains `dim S^μ` copies of each
Specht module `S^μ`.

This is Etingof et al., *Introduction to Representation Theory*, Theorem
4.1.1(ii), specialized to `ℂ[S_n]`, with the irreducibles indexed by the Specht
classification. The inner finite biproduct is indexed by a `Fin` type of cardinal
`finrank ℂ (S^μ)`, so its number of copies records the stated multiplicity
literally. -/
theorem symmetricGroupLeftRegular_decomposition (n : ℕ) :
  Nonempty
    (symmetricGroupLeftRegular n ≅
      ⨁ fun μ : YoungDiagramOfSize n =>
        ⨁ fun _ : Fin (Module.finrank ℂ (spechtModule μ)) => spechtModule μ) := by
  obtain ⟨e⟩ := FDRep.exists_iso_biproduct_multiplicity spechtModule
    spechtModule_irreducible (fun α β => (spechtModule_iso_iff_eq α β).mp)
    (fun T hT => @exists_iso_spechtModule n T hT) (symmetricGroupLeftRegular n)
  exact ⟨e ≪≫ biproduct.mapIso fun μ =>
    biproduct.reindex (finCongr (finrank_hom_symmetricGroupLeftRegular n (spechtModule μ)))
      fun _ => spechtModule μ⟩

/-- The squared Specht dimensions sum to the order of the symmetric group. -/
theorem sum_finrank_spechtModule_sq (n : ℕ) :
    ∑ μ : YoungDiagramOfSize n, Module.finrank ℂ (spechtModule μ) ^ 2 = n.factorial := by
  let e := Classical.choice (symmetricGroupLeftRegular_decomposition n)
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  rw [FDRep.finrank_biproduct] at h
  have h2 : ∑ μ : YoungDiagramOfSize n,
      Module.finrank ℂ ((⨁ fun _ : Fin (Module.finrank ℂ (spechtModule μ)) => spechtModule μ :
        SymmetricGroupRepresentation n) : Type) =
      ∑ μ : YoungDiagramOfSize n, Module.finrank ℂ (spechtModule μ) ^ 2 :=
    Finset.sum_congr rfl fun μ _ => by
      rw [FDRep.finrank_biproduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin, sq]
      simp
  rw [← h2, ← h]
  show Module.finrank ℂ (MonoidAlgebra ℂ (SymmetricGroup n)) = n.factorial
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (SymmetricGroup n) ℂ),
    Fintype.card_perm, Fintype.card_fin]
