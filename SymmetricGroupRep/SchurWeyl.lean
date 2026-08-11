import SymmetricGroupRep.HookLength
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Combinatorics.Young.SemistandardTableau

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # The symmetric-group side of Schur-Weyl duality -/

/-- A semistandard tableau whose zero-based entries lie in `Fin q`. -/
structure BoundedSemistandardTableau {n : ℕ}
    (q : ℕ) (shape : YoungDiagramOfSize n) where
  tableau : SemistandardYoungTableau shape.val
  entry_lt : ∀ cell ∈ shape.val.cells, tableau cell.1 cell.2 < q

namespace BoundedSemistandardTableau

/-- The entries of a bounded semistandard tableau, restricted to its cells. -/
def entries {n q : ℕ} {shape : YoungDiagramOfSize n}
    (T : BoundedSemistandardTableau q shape) :
    (cell : ↥shape.val.cells) → Fin q :=
  fun cell => ⟨T.tableau cell.1.1 cell.1.2, T.entry_lt cell.1 cell.2⟩

private theorem entries_injective {n q : ℕ} {shape : YoungDiagramOfSize n} :
    Function.Injective
      (entries : BoundedSemistandardTableau q shape →
        ((cell : ↥shape.val.cells) → Fin q)) := by
  intro T U hequal
  cases T with
  | mk T hT =>
    cases U with
    | mk U hU =>
      congr 1
      apply SemistandardYoungTableau.ext
      intro row column
      by_cases hcell : (row, column) ∈ shape.val.cells
      · have hentry := congrFun hequal ⟨(row, column), hcell⟩
        exact congrArg Fin.val hentry
      · rw [T.zeros (by simpa using hcell), U.zeros (by simpa using hcell)]

noncomputable instance {n q : ℕ} (shape : YoungDiagramOfSize n) :
    Finite (BoundedSemistandardTableau q shape) :=
  Finite.of_injective entries entries_injective

end BoundedSemistandardTableau

/-- The Schur-Weyl multiplicity of `S^shape` in `(ℂ^q)^{⊗ n}`. -/
noncomputable def schurWeylMultiplicity {n : ℕ}
    (q : ℕ) (shape : YoungDiagramOfSize n) : ℕ :=
  Nat.card (BoundedSemistandardTableau q shape)

/-- Coordinate permutations act on words by precomposition with the inverse
permutation. -/
instance symmetricGroupWordAction (q n : ℕ) :
    MulAction (SymmetricGroup n) (Fin n → Fin q) :=
  arrowAction

/-- The permutation representation of `S_n` on words of length `n` over a
`q`-letter alphabet. This is the coordinate basis of `(ℂ^q)^{⊗ n}`. -/
noncomputable def tensorPowerPermutationRepresentation (q n : ℕ) :
    SymmetricGroupRepresentation n :=
  FDRep.of (Representation.ofMulAction ℂ (SymmetricGroup n) (Fin n → Fin q))

/-- Schur-Weyl duality, restricted to the symmetric-group action on tensor
space.

Magee, *Random Unitary Representations of Surface Groups I: Asymptotic
Expansions*, Proposition 2.4 on page 133, gives the full commuting
`U(q) × S_n` decomposition. The Gelfand--Tsetlin construction on page 134
indexes a basis of its `U(q)` factor by semistandard tableaux with entries in
`1, ..., q`. Shifting these entries down to `Fin q` and forgetting the `U(q)`
action gives the displayed multiplicity. When `q = 0`, `hn` makes both the word
basis and every bounded-tableau index set empty. The source is bundled as
`refs/magee-2022-random-unitary-representations.pdf`. -/
axiom tensorPower_schurWeyl (q n : ℕ) (hn : 0 < n) :
  Nonempty (tensorPowerPermutationRepresentation q n ≅
    ⨁ fun shape : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (schurWeylMultiplicity q shape) => spechtModule shape)

/-- The numerator in the hook-content formula, using zero-based cell
coordinates. -/
def YoungDiagram.schurContentProduct (q : ℕ) (μ : YoungDiagram) : ℤ :=
  μ.cells.prod fun cell => (q : ℤ) + cell.2 - cell.1

/-- The hook-content dimension formula in multiplicative form.

Magee, *Random Unitary Representations of Surface Groups I: Asymptotic
Expansions*, equation (2.5) on page 131, gives the hook-content formula for the
dimension of the `U(q)` factor. Its Gelfand--Tsetlin basis on page 134 identifies
that dimension with bounded semistandard tableaux. Clearing the hook-product
denominator gives this statement; the paper's one-based content `j - i` equals
the zero-based `cell.2 - cell.1` used here. For `q = 0`, the empty shape gives
`1 = 1`, while every nonempty shape has no bounded tableaux and its top-left
cell makes the content product zero. The source is bundled as
`refs/magee-2022-random-unitary-representations.pdf`. -/
axiom schurWeylMultiplicity_mul_hookProduct {n : ℕ}
    (q : ℕ) (shape : YoungDiagramOfSize n) :
  (schurWeylMultiplicity q shape : ℤ) * shape.val.hookProduct =
    shape.val.schurContentProduct q
