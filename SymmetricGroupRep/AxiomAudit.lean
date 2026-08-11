import SymmetricGroupRep.Biregular
import SymmetricGroupRep.Kostka
import SymmetricGroupRep.Classification
import SymmetricGroupRep.Kronecker
import SymmetricGroupRep.Decomposition
import SymmetricGroupRep.ProductClassification
import SymmetricGroupRep.RegularDecomposition
import SymmetricGroupRep.SelfDuality
import SymmetricGroupRep.Tableaux

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

/-- info: 'spechtModule_singleRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule_singleRow

/-- info: 'spechtModule_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule_irreducible

/-- info: 'spechtModule_iso_iff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule_iso_iff_eq

/-- info: 'exists_iso_spechtModule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_iso_spechtModule

/-- info: 'spechtModule_selfDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule_selfDual

/-- info: 'spechtModule_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule_kronecker

/-- info: 'spechtModule_tensor_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spechtModule_tensor_sign

/--
info: 'existsUnique_iso_spechtOuterTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms existsUnique_iso_spechtOuterTensor

/--
info: 'symmetricGroupLeftRegular_decomposition' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms symmetricGroupLeftRegular_decomposition

/--
info: 'symmetricGroupBiregular_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms symmetricGroupBiregular_decomposition

/-! The shared infrastructure the remaining targets are built on is guarded here
too, so that a regression in it fails the build rather than surfacing later as a
mysteriously unprovable target. -/

/-- info: 'FDRep.char_rightDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FDRep.char_rightDual

/-- info: 'FDRep.simple_of_isIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FDRep.simple_of_isIrreducible

/--
info: 'FDRep.exists_iso_biproduct_simples' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FDRep.exists_iso_biproduct_simples

/--
info: 'FDRep.exists_iso_biproduct_multiplicity' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms FDRep.exists_iso_biproduct_multiplicity

/--
info: 'SymmetricGroupRepresentation.nonempty_iso_of_character_eq' depends on axioms: [propext,
Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms SymmetricGroupRepresentation.nonempty_iso_of_character_eq

/--
info: 'FDRep.finrank_hom_outerTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FDRep.finrank_hom_outerTensor

/-- info: 'exists_spechtTableauBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_spechtTableauBasis

/--
info: 'youngPermutationModule_twoRow_induction' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms youngPermutationModule_twoRow_induction
