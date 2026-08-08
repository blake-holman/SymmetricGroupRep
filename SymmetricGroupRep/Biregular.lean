import SymmetricGroupRep.OuterTensor
import SymmetricGroupRep.Regular
import SymmetricGroupRep.SelfDuality
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # The biregular representation of a symmetric group -/

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

/-- As an `S_n × S_n`-representation, `ℂ[S_n]` is the multiplicity-free sum of
`S^μ ⊠ (S^μ)ᘁ`.

This is the finite-group Peter-Weyl decomposition. Under the book's standing
algebraically-closed-field convention, Etingof et al., *Introduction to
Representation Theory*, Theorem 4.1.1(ii), identifies `k[G]` with the direct
sum of `End(V)` over irreducible `V`; the proof of Theorem 4.5.4 records the
`G × G` action `x ↦ g x h⁻¹`. Under `End(V) ≅ V ⊗ V*`, this is the outer tensor
product of `V` with its dual. We specialize to `k = ℂ`, `G = S_n`, and use the
Specht classification. -/
axiom symmetricGroupBiregular_decomposition (n : ℕ) :
  Nonempty
    (symmetricGroupBiregular n ≅
      ⨁ fun μ : YoungDiagramOfSize n =>
        FDRep.outerTensor (spechtModule μ) ((spechtModule μ)ᘁ))
