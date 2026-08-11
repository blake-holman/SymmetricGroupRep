import SymmetricGroupRep.Kostka
import SymmetricGroupRep.Classification

/-! # Axiom-closure audit for converted targets

Every declaration that used to be an `axiom` in this package is recorded here
together with its `#print axioms` closure. `#guard_msgs` turns each record into
a build-time check, so a proof that starts depending on a project axiom, on a
new assumption, or on `sorryAx` fails `lake build` instead of passing silently.

Only `propext`, `Classical.choice`, and `Quot.sound` are acceptable: these are
the standard kernel principles mathlib itself already relies on.
-/

/-- info: 'spechtModule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule

/-- info: 'twoRowKostkaIndexEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoRowKostkaIndexEquiv

/-- info: 'twoRowKostkaIndexEquiv_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoRowKostkaIndexEquiv_shape
