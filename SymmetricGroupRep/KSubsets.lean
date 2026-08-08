import SymmetricGroupRep.Kostka
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # Representations on fixed-size subsets

The symmetric group acts on fixed-cardinality subsets of `Fin n`.  Mathlib
provides both this action and its equivariant complement map.
-/

/-- The `k`-element subsets of `Fin n`. -/
abbrev KSubsets (n k : ℕ) := Set.powersetCard (Fin n) k

/-- The permutation representation of `S_n` on `k`-element subsets. -/
noncomputable def kSubsetRepresentation (n k : ℕ) : SymmetricGroupRepresentation n :=
  FDRep.of (Representation.ofMulAction ℂ (SymmetricGroup n) (KSubsets n k))

/-- The two-row Young permutation module is the permutation representation on
subsets of the size of its second row. -/
noncomputable def youngPermutationModuleTwoRowIso {n r : ℕ} (h : 2 * r ≤ n) :
    youngPermutationModule (twoRowPartition n r h) ≅ kSubsetRepresentation n r :=
  FDRep.ofMulActionEquiv (Tabloid.twoRowEquiv h) (Tabloid.twoRowEquiv_smul h)

/-- The symmetric group permutes the fixed-size subset basis. -/
@[simp]
theorem kSubsetRepresentation_rho_single (n k : ℕ) (sigma : SymmetricGroup n)
    (subset : KSubsets n k) (c : ℂ) :
    (kSubsetRepresentation n k).ρ sigma (MonoidAlgebra.single subset c) =
      MonoidAlgebra.single (sigma • subset) c :=
  Representation.ofMulAction_single sigma subset c

/-- Taking complements gives an equivariant isomorphism between the `k`-subset
and `(n-k)`-subset representations. -/
noncomputable def kSubsetComplementIso (n k : ℕ) (hk : k ≤ n) :
    kSubsetRepresentation n k ≅ kSubsetRepresentation n (n - k) := by
  have hcard : (n - k) + k = Fintype.card (Fin n) := by
    simp
    omega
  let complementMap :=
    Set.powersetCard.mulActionHom_compl (SymmetricGroup n) (Fin n) hcard
  let complementEquiv : KSubsets n k ≃ KSubsets n (n - k) :=
    Equiv.ofBijective complementMap
      (Set.powersetCard.mulActionHom_compl_bijective
        (SymmetricGroup n) (Fin n) hcard)
  exact FDRep.ofMulActionEquiv complementEquiv fun sigma subset =>
    complementMap.map_smul sigma subset

/-- Replace a subset size by the smaller of it and its complement. -/
noncomputable def kSubsetToMinIso (n k : ℕ) (hk : k ≤ n) :
    kSubsetRepresentation n k ≅
      kSubsetRepresentation n (min k (n - k)) := by
  by_cases hsmall : k ≤ n - k
  · simpa [min_eq_left hsmall] using Iso.refl (kSubsetRepresentation n k)
  · have hlarge : n - k ≤ k := by omega
    simpa [min_eq_right hlarge] using kSubsetComplementIso n k hk

/-- The `k`-subset representation is multiplicity-free, with constituents
indexed by the two-row shapes `(n-i,i)` for
`0 <= i <= min(k,n-k)`.

The proof is local: take complements when necessary, identify subsets with
two-row tabloids, and apply the two-row consequence of Young's rule. -/
theorem kSubsetRepresentation_decomposition (n k : ℕ) (hk : k ≤ n) :
    Nonempty (kSubsetRepresentation n k ≅
      ⨁ fun i : Fin (min k (n - k) + 1) =>
        spechtModule (twoRowShape n k hk i)) := by
  let toMin := kSubsetToMinIso n k hk
  have htwo : 2 * min k (n - k) ≤ n := by omega
  let toTabloids :
      kSubsetRepresentation n (min k (n - k)) ≅
        youngPermutationModule (twoRowWeight n k hk) := by
    simpa [twoRowWeight] using
      (youngPermutationModuleTwoRowIso htwo).symm
  let decompose :=
    Classical.choice (youngPermutationModule_twoRow_decomposition n k hk)
  exact ⟨toMin ≪≫ toTabloids ≪≫ decompose⟩
