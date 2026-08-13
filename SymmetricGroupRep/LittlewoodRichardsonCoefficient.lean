import SymmetricGroupRep.YoungDiagrams
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-! # Littlewood-Richardson tableaux and coefficients

The combinatorial definitions live below the whole Littlewood-Richardson
development: the symmetric-function bridge consumes them, and the
representation-theoretic rule in `LittlewoodRichardson.lean` sits on top of
both.
-/

namespace LittlewoodRichardson

/-- `c` occurs no later than `d` when a skew tableau is read from top to
bottom, and from right to left within each row. -/
abbrev readingLE (c d : ℕ × ℕ) : Prop :=
  c.1 < d.1 ∨ (c.1 = d.1 ∧ d.2 ≤ c.2)

end LittlewoodRichardson

/-- A Littlewood-Richardson tableau of skew shape `ξ / μ` and content `ν`.

Entries are zero-based. Rows are weakly increasing, columns are strictly
increasing, and every prefix of the top-to-bottom, right-to-left reading word
has at least as many `i` entries as `i + 1` entries. -/
@[ext]
structure LittlewoodRichardsonTableau {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) where
  /-- The inner diagram is contained in the outer diagram. -/
  shape : μ.val ≤ ξ.val
  /-- The entries of the skew cells. -/
  entry : ↥(ξ.val.cells \ μ.val.cells) → Fin b
  /-- Entries weakly increase along rows. -/
  row_weak : ∀ {c d}, c.1.1 = d.1.1 → c.1.2 < d.1.2 → entry c ≤ entry d
  /-- Entries strictly increase down columns. -/
  col_strict : ∀ {c d}, c.1.2 = d.1.2 → c.1.1 < d.1.1 → entry c < entry d
  /-- Entry `i` occurs `ν_i` times. -/
  content : ∀ i : Fin b,
    (Finset.univ.filter fun c => entry c = i).card = ν.val.rowLen i.1
  /-- The reverse reading word is a lattice word. -/
  lattice : ∀ (d : ↥(ξ.val.cells \ μ.val.cells)) (i : Fin (b - 1)),
    (Finset.univ.filter fun c : ↥(ξ.val.cells \ μ.val.cells) =>
      LittlewoodRichardson.readingLE c.1 d.1 ∧ (entry c).1 = i.1).card ≥
    (Finset.univ.filter fun c : ↥(ξ.val.cells \ μ.val.cells) =>
      LittlewoodRichardson.readingLE c.1 d.1 ∧ (entry c).1 = i.1 + 1).card

/-- Littlewood-Richardson tableaux of fixed shape and content form a finite
type. -/
noncomputable instance {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) :
    Finite (LittlewoodRichardsonTableau μ ν ξ) :=
  Finite.of_injective LittlewoodRichardsonTableau.entry fun T U h => by
    cases T
    cases U
    cases h
    rfl

/-- The Littlewood-Richardson coefficient `c^ξ_{μ,ν}`. -/
noncomputable def littlewoodRichardsonCoefficient {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) : ℕ :=
  Nat.card (LittlewoodRichardsonTableau μ ν ξ)
