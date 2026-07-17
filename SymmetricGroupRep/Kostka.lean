import SymmetricGroupRep.YoungPermutation
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Combinatorics.Young.SemistandardTableau

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! # Kostka numbers and Young's rule

Mathlib supplies semistandard Young tableaux with natural-number entries.  We
add a finite content condition and use these tableaux to index Kostka numbers.
-/

/-- A semistandard tableau of a fixed shape and weight.

Mathlib's tableau entries are zero-based: entry `i` here corresponds to entry
`i + 1` in the usual positive-integer convention. -/
structure WeightedSemistandardTableau {n : ℕ}
    (shape weight : YoungDiagramOfSize n) where
  tableau : SemistandardYoungTableau shape.val
  entry_lt : ∀ cell ∈ shape.val.cells, tableau cell.1 cell.2 < n
  content : ∀ entry : Fin n,
    (shape.val.cells.filter fun cell => tableau cell.1 cell.2 = entry).card =
      weight.val.rowLen entry

namespace WeightedSemistandardTableau

/-- The bounded entries of a weighted semistandard tableau. -/
def entries {n : ℕ} {shape weight : YoungDiagramOfSize n}
    (T : WeightedSemistandardTableau shape weight) :
    (cell : ↥shape.val.cells) → Fin n :=
  fun cell => ⟨T.tableau cell.1.1 cell.1.2, T.entry_lt cell.1 cell.2⟩

private theorem entries_injective {n : ℕ} {shape weight : YoungDiagramOfSize n} :
    Function.Injective
      (entries : WeightedSemistandardTableau shape weight →
        ((cell : ↥shape.val.cells) → Fin n)) := by
  intro T U hequal
  cases T with
  | mk T hT wT =>
    cases U with
    | mk U hU wU =>
      congr 1
      apply SemistandardYoungTableau.ext
      intro row column
      by_cases hcell : (row, column) ∈ shape.val.cells
      · have hentry := congrFun hequal ⟨(row, column), hcell⟩
        exact congrArg Fin.val hentry
      · rw [T.zeros (by simpa using hcell), U.zeros (by simpa using hcell)]

noncomputable instance {n : ℕ} (shape weight : YoungDiagramOfSize n) :
    Finite (WeightedSemistandardTableau shape weight) :=
  Finite.of_injective entries entries_injective

end WeightedSemistandardTableau

/-- The Kostka number `K_(shape,weight)`. -/
noncomputable def kostkaNumber {n : ℕ}
    (shape weight : YoungDiagramOfSize n) : ℕ :=
  Nat.card (WeightedSemistandardTableau shape weight)

/-- Young's rule: the Young permutation module of weight `weight` contains
`S^shape` with multiplicity `K_(shape,weight)`.

See Sagan, *The Symmetric Group*, 2nd ed., Theorem 2.11.2,
https://doi.org/10.1007/978-1-4757-6804-6_2.  The conventions are cross-checked
against Tomczak, *Representation Theory of Symmetric Groups* (2022 lecture
notes), Corollary 3.19,
https://math.berkeley.edu/~ltomczak/notes/Mich2022/RepSn_Notes.pdf: rows are
weakly increasing, columns are strictly increasing, and the first Kostka index
is the shape.  Tomczak uses positive entries, while
`WeightedSemistandardTableau` shifts them down by one. -/
axiom youngsRule {n : ℕ} (weight : YoungDiagramOfSize n) :
  Nonempty (youngPermutationModule weight ≅
    ⨁ fun shape : YoungDiagramOfSize n =>
      ⨁ fun _ : Fin (kostkaNumber shape weight) => spechtModule shape)

/-- The balanced two-row weight associated to a `k`-subset of an `n`-element
set.  Complementary subset sizes give the same weight. -/
def twoRowWeight (n k : ℕ) (hk : k ≤ n) : YoungDiagramOfSize n :=
  twoRowPartition n (min k (n - k)) (by omega)

/-- The two-row shapes occurring in the `k`-subset representation. -/
def twoRowShape (n k : ℕ) (hk : k ≤ n)
    (i : Fin (min k (n - k) + 1)) : YoungDiagramOfSize n :=
  twoRowPartition n i (by
    have hi : i.val ≤ min k (n - k) := by omega
    omega)

/-- For a two-row weight, the nonzero Kostka copies are indexed once by the
possible second-row lengths.

This is the two-letter specialization of Sagan, *The Symmetric Group*, 2nd ed.,
Definition 2.11.1 and Theorem 2.11.2,
https://doi.org/10.1007/978-1-4757-6804-6_2.  In a semistandard tableau of weight
`(n-r,r)`, strict columns force at most two rows; the bottom row is all `1`, and
the remaining top row is uniquely weakly increasing.  The same conventions are
independently stated in Tomczak, *Representation Theory of Symmetric Groups*
(2022 lecture notes), Corollary 3.19,
https://math.berkeley.edu/~ltomczak/notes/Mich2022/RepSn_Notes.pdf. -/
axiom twoRowKostkaIndexEquiv (n k : ℕ) (hk : k ≤ n) :
  (Σ shape : YoungDiagramOfSize n,
    Fin (kostkaNumber shape (twoRowWeight n k hk))) ≃
      Fin (min k (n - k) + 1)

/-- The Kostka copy selected by `twoRowKostkaIndexEquiv` has the corresponding
two-row shape.  This records the shape component of the sourced two-row Kostka
calculation above. -/
axiom twoRowKostkaIndexEquiv_shape (n k : ℕ) (hk : k ≤ n)
    (copy : Σ shape : YoungDiagramOfSize n,
      Fin (kostkaNumber shape (twoRowWeight n k hk))) :
    copy.1 = twoRowShape n k hk (twoRowKostkaIndexEquiv n k hk copy)

/-- Young's rule for a two-row weight, regrouped into its multiplicity-free
form. -/
theorem youngPermutationModule_twoRow_decomposition (n k : ℕ) (hk : k ≤ n) :
    Nonempty (youngPermutationModule (twoRowWeight n k hk) ≅
      ⨁ fun i : Fin (min k (n - k) + 1) => spechtModule (twoRowShape n k hk i)) := by
  let youngIso := Classical.choice (youngsRule (twoRowWeight n k hk))
  let copies := Σ shape : YoungDiagramOfSize n,
    Fin (kostkaNumber shape (twoRowWeight n k hk))
  let indexEquiv : copies ≃ Fin (min k (n - k) + 1) :=
    twoRowKostkaIndexEquiv n k hk
  let flatten :
      (⨁ fun shape : YoungDiagramOfSize n =>
        ⨁ fun _ : Fin (kostkaNumber shape (twoRowWeight n k hk)) => spechtModule shape) ≅
      ⨁ fun copy : copies => spechtModule copy.1 :=
    biproductBiproductIso
      (fun shape => Fin (kostkaNumber shape (twoRowWeight n k hk)))
      (fun shape _ => spechtModule shape)
  let changeShape :
      (⨁ fun copy : copies => spechtModule copy.1) ≅
      ⨁ fun copy : copies => spechtModule (twoRowShape n k hk (indexEquiv copy)) :=
    biproduct.mapIso fun copy =>
      eqToIso (congrArg spechtModule (twoRowKostkaIndexEquiv_shape n k hk copy))
  exact ⟨youngIso ≪≫ flatten ≪≫ changeShape ≪≫
    biproduct.reindex indexEquiv
      (fun i => spechtModule (twoRowShape n k hk i))⟩
