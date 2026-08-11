import SymmetricGroupRep.LittlewoodRichardson
import SymmetricGroupRep.YoungPermutation

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # Internal tensor products and Kronecker coefficients -/

/-- The internal tensor product of two Specht modules for the same symmetric
group. -/
noncomputable abbrev spechtInnerTensor {n : ℕ}
    (μ ν : YoungDiagramOfSize n) : SymmetricGroupRepresentation n :=
  spechtModule μ ⊗ spechtModule ν

/-- The Kronecker coefficient `g(μ, ν, ξ)`, defined as the multiplicity of
`S^ξ` in `S^μ ⊗ S^ν`. -/
noncomputable def kroneckerCoefficient {n : ℕ}
    (μ ν ξ : YoungDiagramOfSize n) : ℕ :=
  Module.finrank ℂ (spechtModule ξ ⟶ spechtInnerTensor μ ν)

/-- The Kronecker decomposition of the internal tensor product of two complex
Specht modules.

The unnumbered display in Section 1.2 on page 3 of Bowman, De Visscher, and
Orellana, *The Partition Algebra and the Kronecker Coefficients*
([arXiv:1210.5579](https://arxiv.org/abs/1210.5579)), gives this decomposition
and names its multiplicities the Kronecker coefficients. The Hom formula on
page 4 computes the same multiplicity with the opposite Hom orientation;
Schur's lemma identifies it with the source-first convention used here. -/
axiom spechtModule_kronecker {n : ℕ} (μ ν : YoungDiagramOfSize n) :
  Nonempty (spechtInnerTensor μ ν ≅
    ⨁ fun ξ : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (kroneckerCoefficient μ ν ξ) => spechtModule ξ)

/-- The one-row Young diagram `(n)`. -/
def singleRowPartition (n : ℕ) : YoungDiagramOfSize n :=
  twoRowPartition n 0 (by omega)

/-- The Specht module indexed by `(n)` is the trivial representation.

The first bullet in the one-dimensional-representations paragraph of Section
1.4.2 on page 24 of Rosmanis states explicitly that `S^(n)` is the trivial
representation. -/
axiom spechtModule_singleRow (n : ℕ) :
  Nonempty (spechtModule (singleRowPartition n) ≅
    𝟙_ (SymmetricGroupRepresentation n))

/-- Transpose a fixed-size Young diagram. -/
def YoungDiagramOfSize.transpose {n : ℕ}
    (μ : YoungDiagramOfSize n) : YoungDiagramOfSize n :=
  ⟨μ.val.transpose, by
    rw [YoungDiagram.card]
    simpa [YoungDiagram.transpose] using μ.property⟩

/-- Tensoring a Specht module with the sign representation transposes its
Young diagram.

James, *The Representation Theory of the Symmetric Groups*, Lecture Notes in
Mathematics 682 (1978), equation (6.6) and Theorem 6.7 on page 25, gives the
conjugate-partition identity after base change to `ℂ`; the self-duality remark
following the theorem removes the displayed dual. The source is indexed in
`refs/README.md`. -/
axiom spechtModule_tensor_sign {n : ℕ} (μ : YoungDiagramOfSize n) :
  Nonempty (spechtModule (YoungDiagramOfSize.transpose μ) ≅
    spechtModule μ ⊗ SymmetricGroupRepresentation.sign n)

/-- Transport a Young diagram across an equality of its size. -/
def YoungDiagramOfSize.cast {m n : ℕ} (h : m = n)
    (μ : YoungDiagramOfSize m) : YoungDiagramOfSize n :=
  h ▸ μ

/-- The multiplicity obtained by restricting `S^μ` and `S^ν` to the standard
Young subgroup `S_(n-k) × S_k` and pairing equal constituents. By Frobenius
reciprocity, this is also the relevant restrict-then-induce multiplicity. -/
noncomputable def youngSubgroupRoundTripMultiplicity {n : ℕ}
    (k : ℕ) (hk : k ≤ n) (μ ν : YoungDiagramOfSize n) : ℕ :=
  ∑ α : YoungDiagramOfSize (n - k),
    ∑ β : YoungDiagramOfSize k,
      littlewoodRichardsonCoefficient α β
          (YoungDiagramOfSize.cast (Nat.sub_add_cancel hk).symm μ) *
        littlewoodRichardsonCoefficient α β
          (YoungDiagramOfSize.cast (Nat.sub_add_cancel hk).symm ν)

/-- Rosmanis's two-row reduction of a Kronecker coefficient to two
restrict-then-induce multiplicities.

This is Lemma 1.12 on page 30 of Rosmanis, *Lower Bounds on Quantum Query and
Learning Graph Complexities* (2014 thesis). The strict hypotheses match the
statement there, and the natural-number subtraction is exact under that
identity. -/
axiom twoRowKroneckerCoefficient_eq_roundTrip_sub
    (n i j : ℕ) (hi : 1 < i) (hj : 1 < j)
    (hin : 2 * i < n) (hjn : 2 * j < n)
    (ν : YoungDiagramOfSize n) :
  kroneckerCoefficient
      (twoRowPartition n i (by omega))
      (twoRowPartition n j (by omega)) ν =
    youngSubgroupRoundTripMultiplicity i (by omega)
        (twoRowPartition n j (by omega)) ν -
      youngSubgroupRoundTripMultiplicity (i - 1) (by omega)
        (twoRowPartition n j (by omega)) ν
