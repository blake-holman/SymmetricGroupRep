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
axiom symmetricGroupLeftRegular_decomposition (n : ℕ) :
  Nonempty
    (symmetricGroupLeftRegular n ≅
      ⨁ fun μ : YoungDiagramOfSize n =>
        ⨁ fun _ : Fin (Module.finrank ℂ (spechtModule μ)) => spechtModule μ)
