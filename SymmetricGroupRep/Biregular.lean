import SymmetricGroupRep.OuterTensor
import SymmetricGroupRep.ProductClassification
import SymmetricGroupRep.Regular
import SymmetricGroupRep.SelfDuality
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # The biregular representation of a symmetric group

The decomposition is read off multiplicities rather than characters. The simples of `S_n × S_n`
are the `S^μ ⊠ S^ν`, and both sides of the statement contain each of them
`if μ = ν then 1 else 0` times: on the left because the biregular character counts conjugators,
so summing over the second factor collapses to a single Specht character pairing; on the right
because `S^α ⊠ (S^α)ᘁ` meets `S^μ ⊠ S^ν` only when `α` is both `μ` and `ν`.
-/

/-- The action of `S_n × S_n` on `S_n` by `(g, h) • x = g * x * h⁻¹`. -/
@[reducible]
def symmetricGroupBiregularAction (n : ℕ) :
    MulAction (SymmetricGroup n × SymmetricGroup n) (SymmetricGroup n) where
  smul gh x := gh.1 * x * gh.2⁻¹
  one_smul x := show (1 : SymmetricGroup n) * x * (1 : SymmetricGroup n)⁻¹ = x by simp
  mul_smul gh kl x := by
    show (gh.1 * kl.1) * x * (gh.2 * kl.2)⁻¹ =
      gh.1 * (kl.1 * x * kl.2⁻¹) * gh.2⁻¹
    simp only [mul_inv_rev]
    simp only [mul_assoc]

/-- The complex permutation representation associated to the biregular action. -/
noncomputable def symmetricGroupBiregular (n : ℕ) :
    FDRep ℂ (SymmetricGroup n × SymmetricGroup n) := by
  letI := symmetricGroupBiregularAction n
  exact FDRep.of (Representation.ofMulAction ℂ
    (SymmetricGroup n × SymmetricGroup n) (SymmetricGroup n))

/-- The biregular action on the standard group-algebra basis. -/
@[simp]
theorem symmetricGroupBiregular_ρ_single (n : ℕ)
    (g h x : SymmetricGroup n) (c : ℂ) :
    (symmetricGroupBiregular n).ρ (g, h) (MonoidAlgebra.single x c) =
      MonoidAlgebra.single (g * x * h⁻¹) c := by
  letI := symmetricGroupBiregularAction n
  exact Representation.ofMulAction_single (g, h) x c

/-- The biregular character counts the conjugators taking `g` to `h`: the basis vector at `x` is
fixed by `(g, h)` exactly when `x⁻¹ * g * x = h`. -/
theorem symmetricGroupBiregular_character (n : ℕ) (g h : SymmetricGroup n) :
    (symmetricGroupBiregular n).character (g, h) =
      ∑ x : SymmetricGroup n, if x⁻¹ * g * x = h then (1 : ℂ) else 0 := by
  letI := symmetricGroupBiregularAction n
  have hsingle : ∀ x : SymmetricGroup n,
      Representation.ofMulAction ℂ (SymmetricGroup n × SymmetricGroup n) (SymmetricGroup n)
        (g, h) (MonoidAlgebra.single x 1) =
          MonoidAlgebra.single (g * x * h⁻¹) (1 : ℂ) :=
    fun x => Representation.ofMulAction_single (g, h) x 1
  have htrace : (symmetricGroupBiregular n).character (g, h) =
      Matrix.trace (LinearMap.toMatrix (MonoidAlgebra.basis (SymmetricGroup n) ℂ)
        (MonoidAlgebra.basis (SymmetricGroup n) ℂ)
        (Representation.ofMulAction ℂ (SymmetricGroup n × SymmetricGroup n) (SymmetricGroup n)
          (g, h))) :=
    LinearMap.trace_eq_matrix_trace ℂ _ _
  rw [htrace]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    MonoidAlgebra.basis_apply, hsingle]
  change (∑ x : SymmetricGroup n,
    (MonoidAlgebra.single (g * x * h⁻¹) (1 : ℂ)).coeff x) = _
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_apply]
  congr 1
  apply propext
  constructor
  · intro hx
    calc x⁻¹ * g * x = x⁻¹ * (g * x * h⁻¹) * h := by group
      _ = x⁻¹ * x * h := by rw [hx]
      _ = h := by group
  · intro hx
    calc g * x * h⁻¹ = x * (x⁻¹ * g * x) * h⁻¹ := by group
      _ = x * h * h⁻¹ := by rw [hx]
      _ = x := by group

open scoped Classical in
/-- `S^μ ⊠ S^ν` occurs in the biregular representation once when `μ = ν` and never otherwise.

Summing the biregular character over the second factor replaces `h` by `x⁻¹ * g * x` for each
conjugator `x`, and the Specht character is constant on conjugacy classes, so the double pairing
collapses to `Nat.card (S_n)` copies of the ordinary pairing of `χ_μ` with `χ_ν`. -/
theorem finrank_hom_symmetricGroupBiregular (n : ℕ) (μ ν : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtOuterTensor μ ν ⟶ symmetricGroupBiregular n) =
      if μ = ν then 1 else 0 := by
  classical
  letI := spechtModule_irreducible μ
  letI := spechtModule_irreducible ν
  have hN : (Fintype.card (SymmetricGroup n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hschur : ∑ g : SymmetricGroup n,
      (spechtModule μ).character g * (spechtModule ν).character g⁻¹ =
        (Fintype.card (SymmetricGroup n) : ℂ) * ((if μ = ν then 1 else 0 : ℕ) : ℂ) := by
    have h := FDRep.scalar_product_char_eq_finrank_equivariant (spechtModule ν) (spechtModule μ)
    rw [FDRep.finrank_hom_simple_simple] at h
    have hif : (if Nonempty (spechtModule ν ≅ spechtModule μ) then (1 : ℕ) else 0)
        = if μ = ν then 1 else 0 := by
      by_cases hμν : μ = ν
      · subst hμν; simp
      · rw [if_neg fun e => hμν ((spechtModule_iso_iff_eq ν μ).mp e).symm, if_neg hμν]
    rw [hif] at h
    have h' : ⅟(Fintype.card (SymmetricGroup n) : ℂ) •
        ∑ g : SymmetricGroup n,
          (spechtModule μ).character g * (spechtModule ν).character g⁻¹ =
          ((if μ = ν then 1 else 0 : ℕ) : ℂ) := by
      rw [invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card]
      exact h
    calc ∑ g : SymmetricGroup n, (spechtModule μ).character g * (spechtModule ν).character g⁻¹
        = (Fintype.card (SymmetricGroup n) : ℂ) *
            (⅟(Fintype.card (SymmetricGroup n) : ℂ) •
              ∑ g : SymmetricGroup n,
                (spechtModule μ).character g * (spechtModule ν).character g⁻¹) := by
          rw [smul_eq_mul, ← mul_assoc, mul_invOf_self, one_mul]
      _ = _ := by rw [h']
  have hsum : ∑ p : SymmetricGroup n × SymmetricGroup n,
      (symmetricGroupBiregular n).character p * (spechtOuterTensor μ ν).character p⁻¹ =
        (Fintype.card (SymmetricGroup n) : ℂ) *
          ∑ g : SymmetricGroup n,
            (spechtModule μ).character g * (spechtModule ν).character g⁻¹ := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    calc ∑ h : SymmetricGroup n,
          (symmetricGroupBiregular n).character (g, h) *
            (spechtOuterTensor μ ν).character (g, h)⁻¹
        = ∑ h : SymmetricGroup n, ∑ x : SymmetricGroup n,
            if x⁻¹ * g * x = h then
              (spechtModule μ).character g⁻¹ * (spechtModule ν).character h⁻¹ else 0 := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [symmetricGroupBiregular_character,
            show ((g, h) : SymmetricGroup n × SymmetricGroup n)⁻¹ = (g⁻¹, h⁻¹) from rfl,
            FDRep.outerTensor_character, Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by rw [ite_mul, one_mul, zero_mul]
      _ = ∑ x : SymmetricGroup n,
            (spechtModule μ).character g⁻¹ * (spechtModule ν).character (x⁻¹ * g * x)⁻¹ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => by
            rw [Finset.sum_ite_eq Finset.univ (x⁻¹ * g * x)
              fun h => (spechtModule μ).character g⁻¹ * (spechtModule ν).character h⁻¹,
              if_pos (Finset.mem_univ _)]
      _ = (Fintype.card (SymmetricGroup n) : ℂ) *
            ((spechtModule μ).character g * (spechtModule ν).character g⁻¹) := by
          rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => by
            rw [show (x⁻¹ * g * x)⁻¹ = x⁻¹ * g⁻¹ * (x⁻¹)⁻¹ by group,
              FDRep.char_conj, symmetricGroup_character_inv]]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.cast_inj (R := ℂ), ← FDRep.scalar_product_char_eq_finrank_equivariant, hsum, hschur]
  rw [Nat.card_prod, Nat.cast_mul, ← Fintype.card_eq_nat_card]
  field_simp [hN]

open scoped Classical in
/-- `S^μ ⊠ S^ν` occurs in `⨁ S^α ⊠ (S^α)ᘁ` once when `μ = ν` and never otherwise: the summand at
`α` contributes only when `α` is both `μ` and `ν`. -/
theorem finrank_hom_spechtDualBiproduct (n : ℕ) (μ ν : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtOuterTensor μ ν ⟶
        ⨁ fun α : YoungDiagramOfSize n =>
          FDRep.outerTensor (spechtModule α) ((spechtModule α)ᘁ)) =
      if μ = ν then 1 else 0 := by
  haveI := Fintype.ofFinite (YoungDiagramOfSize n)
  have hterm : ∀ α : YoungDiagramOfSize n,
      Module.finrank ℂ (spechtOuterTensor μ ν ⟶
          FDRep.outerTensor (spechtModule α) ((spechtModule α)ᘁ)) =
        (if μ = α then 1 else 0) * (if ν = α then 1 else 0) := by
    intro α
    letI := spechtModule_irreducible μ
    letI := spechtModule_irreducible ν
    letI := spechtModule_irreducible α
    letI := simple_spechtModule_rightDual α
    rw [FDRep.finrank_hom_outerTensor, FDRep.finrank_hom_simple_simple,
      FDRep.finrank_hom_simple_simple]
    congr 1
    · by_cases h : μ = α
      · rw [if_pos h, if_pos (h ▸ ⟨Iso.refl _⟩)]
      · rw [if_neg h, if_neg fun e => h ((spechtModule_iso_iff_eq μ α).mp e)]
    · by_cases h : ν = α
      · rw [if_pos h, if_pos (h ▸ spechtModule_selfDual ν)]
      · rw [if_neg h, if_neg fun e => h ((spechtModule_iso_iff_eq ν α).mp
          (e.map fun i => i ≪≫ (Classical.choice (spechtModule_selfDual α)).symm))]
  have hbip := FDRep.homFinrank_biproduct (spechtOuterTensor μ ν)
    (fun α : YoungDiagramOfSize n => FDRep.outerTensor (spechtModule α) ((spechtModule α)ᘁ))
  unfold FDRep.homFinrank at hbip
  rw [hbip, Finset.sum_congr rfl fun α _ => hterm α]
  by_cases hμν : μ = ν
  · subst hμν
    rw [if_pos rfl, Finset.sum_eq_single μ
      (fun α _ hα => by rw [if_neg (Ne.symm hα), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_one]
  · rw [if_neg hμν]
    refine Finset.sum_eq_zero fun α _ => ?_
    by_cases h : μ = α
    · rw [if_neg (show ¬ν = α from fun hν => hμν (h.trans hν.symm)), mul_zero]
    · rw [if_neg h, zero_mul]

/-- As an `S_n × S_n`-representation, `ℂ[S_n]` is the multiplicity-free sum of
`S^μ ⊠ (S^μ)ᘁ`.

This is the finite-group Peter-Weyl decomposition. Under the book's standing
algebraically-closed-field convention, Etingof et al., *Introduction to
Representation Theory*, Theorem 4.1.1(ii), identifies `k[G]` with the direct
sum of `End(V)` over irreducible `V`; the proof of Theorem 4.5.4 records the
`G × G` action `x ↦ g x h⁻¹`. Under `End(V) ≅ V ⊗ V*`, this is the outer tensor
product of `V` with its dual. We specialize to `k = ℂ`, `G = S_n`, and use the
Specht classification. -/
theorem symmetricGroupBiregular_decomposition (n : ℕ) :
  Nonempty
    (symmetricGroupBiregular n ≅
      ⨁ fun μ : YoungDiagramOfSize n =>
        FDRep.outerTensor (spechtModule μ) ((spechtModule μ)ᘁ)) :=
  FDRep.nonempty_iso_of_finrank_hom_eq
    (fun p : YoungDiagramOfSize n × YoungDiagramOfSize n => spechtOuterTensor p.1 p.2)
    (fun p => spechtOuterTensor_irreducible p.1 p.2)
    (fun p q h => Prod.ext ((spechtOuterTensor_iso_iff_eq p.1 q.1 p.2 q.2).mp h).1
      ((spechtOuterTensor_iso_iff_eq p.1 q.1 p.2 q.2).mp h).2)
    (fun T hT => by
      obtain ⟨p, hp, -⟩ := @existsUnique_iso_spechtOuterTensor n n T hT
      exact ⟨p, hp⟩)
    (fun p => by
      rw [finrank_hom_symmetricGroupBiregular, finrank_hom_spechtDualBiproduct])
