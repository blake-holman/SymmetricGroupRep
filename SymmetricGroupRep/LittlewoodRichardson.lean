import SymmetricGroupRep.KostkaConvolution
import SymmetricGroupRep.KostkaInverse
import SymmetricGroupRep.LittlewoodRichardsonCoefficient
import SymmetricGroupRep.LittlewoodRichardsonRepresentation
import SymmetricGroupRep.Pieri
import SymmetricGroupRep.ProductClassification

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # The Littlewood-Richardson rule

The multiplicity of `S^ξ` in the induced outer product `S^μ ⊠ S^ν` and the
Littlewood-Richardson coefficient satisfy the same Kostka convolution
identity against every pair of Young weights, so inverting the two
unitriangular Kostka matrices identifies them.
-/

/-- The multiplicity of `S^ξ` in `Ind (S^μ ⊠ S^ν)` is the
Littlewood-Richardson coefficient. -/
private theorem finrank_hom_ind_spechtOuterTensor_eq_lr {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) :
    Module.finrank ℂ
      (spechtModule ξ ⟶
        (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
          (spechtOuterTensor μ ν)) =
      littlewoodRichardsonCoefficient μ ν ξ := by
  classical
  have hdiff : ∀ (α : YoungDiagramOfSize a) (β : YoungDiagramOfSize b),
      ∑ μ' : YoungDiagramOfSize a, (kostkaNumber μ' α : ℤ) *
        ∑ ν' : YoungDiagramOfSize b, (kostkaNumber ν' β : ℤ) *
          ((Module.finrank ℂ (spechtModule ξ ⟶
              (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
                (spechtOuterTensor μ' ν')) : ℤ) -
            (littlewoodRichardsonCoefficient μ' ν' ξ : ℤ)) = 0 := by
    intro α β
    have hB := congrArg (Nat.cast (R := ℤ)) (sum_kostka_mul_finrank_hom_ind α β ξ)
    have hC := congrArg (Nat.cast (R := ℤ)) (sum_kostka_mul_littlewoodRichardson α β ξ)
    push_cast at hB hC
    calc ∑ μ' : YoungDiagramOfSize a, (kostkaNumber μ' α : ℤ) *
          ∑ ν' : YoungDiagramOfSize b, (kostkaNumber ν' β : ℤ) *
            ((Module.finrank ℂ (spechtModule ξ ⟶
                (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
                  (spechtOuterTensor μ' ν')) : ℤ) -
              (littlewoodRichardsonCoefficient μ' ν' ξ : ℤ))
        = (∑ μ' : YoungDiagramOfSize a, ∑ ν' : YoungDiagramOfSize b,
              (kostkaNumber μ' α : ℤ) * (kostkaNumber ν' β : ℤ) *
                (Module.finrank ℂ (spechtModule ξ ⟶
                  (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
                    (spechtOuterTensor μ' ν')) : ℤ)) -
            ∑ μ' : YoungDiagramOfSize a, ∑ ν' : YoungDiagramOfSize b,
              (kostkaNumber μ' α : ℤ) * (kostkaNumber ν' β : ℤ) *
                (littlewoodRichardsonCoefficient μ' ν' ξ : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun μ' _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun ν' _ => ?_
          ring
      _ = 0 := by rw [hB, hC, sub_self]
  have hcol : ∀ β : YoungDiagramOfSize b,
      ∑ ν' : YoungDiagramOfSize b, (kostkaNumber ν' β : ℤ) *
        ((Module.finrank ℂ (spechtModule ξ ⟶
            (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
              (spechtOuterTensor μ ν')) : ℤ) -
          (littlewoodRichardsonCoefficient μ ν' ξ : ℤ)) = 0 :=
    fun β => kostka_convolution_cancel _ (fun α => hdiff α β) μ
  have hfinal := kostka_convolution_cancel _ hcol ν
  have := sub_eq_zero.mp hfinal
  exact_mod_cast this

/-- Littlewood-Richardson decomposition for induction from a Young subgroup.

Sagan, *The Symmetric Group*, 2nd ed., Section 4.9, equation (4.26) and
Theorem 4.9.4 (DOI `10.1007/978-1-4757-6804-6_4`), identify the multiplicity
of `S^ξ` in `Ind_{S_a × S_b}^{S_{a+b}} (S^μ ⊠ S^ν)` with the number of
Littlewood-Richardson tableaux of shape `ξ / μ` and content `ν`. Lean uses the
package's standard first-block/second-block Young-subgroup inclusion and
zero-based tableau entries. -/
theorem spechtModule_littlewoodRichardson {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b) :
  Nonempty
    ((SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (spechtOuterTensor μ ν) ≅
        ⨁ fun ξ : YoungDiagramOfSize (a + b) =>
          ⨁ fun _ : Fin (littlewoodRichardsonCoefficient μ ν ξ) =>
            spechtModule ξ) := by
  obtain ⟨e⟩ := FDRep.exists_iso_biproduct_multiplicity
    spechtModule spechtModule_irreducible
    (fun ξ ξ' h => (spechtModule_iso_iff_eq ξ ξ').mp h)
    (fun T hT => @exists_iso_spechtModule (a + b) T hT)
    ((SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (spechtOuterTensor μ ν))
  exact ⟨e ≪≫ biproduct.mapIso fun ξ =>
    biproduct.reindex
      (finCongr (finrank_hom_ind_spechtOuterTensor_eq_lr μ ν ξ))
      fun _ => spechtModule ξ⟩
