import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.RepresentationTheory.FDRep

/-- The symmetric group on `n` elements. -/
abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- A finite-dimensional complex representation of the symmetric group on `n` elements. -/
abbrev SymmetricGroupRepresentation (n : ℕ) := FDRep ℂ (SymmetricGroup n)
