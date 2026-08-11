import SymmetricGroupRep.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Decomposing a symmetric-group representation into simples

Mathlib decomposes a semisimple module over a ring into finitely many simple submodules
(`IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`), and Maschke makes every
`Representation ℂ (S_n) V` semisimple as a module over the group algebra. What is missing is the
translation back into `FDRep ℂ (S_n)`, where this package states its results. Mathlib does
compare `FDRep` morphisms with intertwining maps, via `FDRep.forget₂HomLinearEquiv` and
`Rep.homLinearEquiv`; what it does not have is a bridge from `Representation.IsIrreducible` to
`CategoryTheory.Simple`, or between the `ℂ[S_n]`-module of a subrepresentation and the submodule
it comes from. The declarations below supply those, and `exists_iso_biproduct_simples` assembles
the module-level decomposition into a biproduct in `FDRep ℂ (S_n)`.

Statements about `Representation.asModule` need
`set_option backward.isDefEq.respectTransparency false`, as they do throughout mathlib's own
representation theory files: the `AddCommMonoid` carried by `ρ.asModule` and the one obtained from
its `AddCommGroup` are equal but not reducibly so.
-/

open CategoryTheory Limits Representation

section Bridge

variable {k G : Type} [Field k] [Monoid G]

/-- A morphism of finite-dimensional representations is an intertwining map.

Mathlib already supplies both halves, so this is just their composite, named here
so the decomposition below reads clearly. -/
noncomputable def FDRep.homEquivIntertwiningMap (V W : FDRep k G) :
    (V ⟶ W) ≃ₗ[k] IntertwiningMap V.ρ W.ρ :=
  (FDRep.forget₂HomLinearEquiv V W).symm ≪≫ₗ Rep.homLinearEquiv _ _

end Bridge

section Simple

variable {k G V : Type} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [NeZero (Nat.card G : k)] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- An irreducible representation is a simple object of `FDRep`. -/
theorem FDRep.simple_of_isIrreducible (ρ : Representation k G V) [IsIrreducible ρ] :
    Simple (FDRep.of ρ) := by
  rw [FDRep.simple_iff_end_is_rank_one,
    LinearEquiv.finrank_eq (FDRep.homEquivIntertwiningMap (FDRep.of ρ) (FDRep.of ρ))]
  exact IsIrreducible.finrank_intertwiningMap_self ρ

end Simple

section AsModule

variable {k G V : Type} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

open scoped MonoidAlgebra

/-- The `k[G]`-module of the subrepresentation cut out by a `k[G]`-submodule `P` of `ρ.asModule`
is `P` itself. -/
def Subrepresentation.asModuleEquivOfSubmodule {ρ : Representation k G V}
    (P : Submodule k[G] ρ.asModule) :
    (Subrepresentation.ofSubmodule' P).toRepresentation.asModule ≃ₗ[k[G]] P where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => rfl
    | add c d hc hd =>
        simp only [RingHom.id_apply] at hc hd ⊢
        rw [add_smul, add_smul]
        exact congrArg₂ (· + ·) hc hd
    | single g a =>
        refine Subtype.ext ?_
        rw [Representation.single_smul]
        exact (Representation.single_smul ρ a g x.1).symm
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

end AsModule

section Decomposition

open scoped MonoidAlgebra

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option backward.isDefEq.respectTransparency false in
/-- Complete reducibility: every finite-dimensional complex representation of a symmetric group
is isomorphic to a finite biproduct of simple representations. -/
theorem SymmetricGroupRepresentation.exists_iso_biproduct_simples {n : ℕ}
    (V : SymmetricGroupRepresentation n) :
    ∃ (k : ℕ) (S : Fin k → SymmetricGroupRepresentation n),
      (∀ i, Simple (S i)) ∧ Nonempty (V ≅ ⨁ S) := by
  classical
  let ρ : Representation ℂ (SymmetricGroup n) V := V.ρ
  haveI : Module.Finite ℂ[SymmetricGroup n] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  obtain ⟨k, N, e, hN⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[SymmetricGroup n] ρ.asModule
  -- `N` is a family of simple `ℂ[S_n]`-submodules with `ρ.asModule ≃ ⨁ N i`; read it back as a
  -- family of subrepresentations, and take the summands to be those subrepresentations.
  let W : Fin k → Subrepresentation ρ := fun i => Subrepresentation.ofSubmodule' (N i)
  let S : Fin k → SymmetricGroupRepresentation n := fun i => FDRep.of (W i).toRepresentation
  let toSubmodule : ∀ i, (W i).toRepresentation.asModule ≃ₗ[ℂ[SymmetricGroup n]] N i :=
    fun i => Subrepresentation.asModuleEquivOfSubmodule (N i)
  let toSummand : ∀ i, ρ.asModule →ₗ[ℂ[SymmetricGroup n]] (W i).toRepresentation.asModule :=
    fun i => (toSubmodule i).symm.toLinearMap ∘ₗ DFinsupp.lapply i ∘ₗ e.toLinearMap
  let fromSummand : ∀ i, (W i).toRepresentation.asModule →ₗ[ℂ[SymmetricGroup n]] ρ.asModule :=
    fun i => e.symm.toLinearMap ∘ₗ DFinsupp.lsingle i ∘ₗ (toSubmodule i).toLinearMap
  let π : ∀ i, V ⟶ S i := fun i =>
    (FDRep.homEquivIntertwiningMap V (S i)).symm
      ((IntertwiningMap.equivLinearMapAsModule ρ (W i).toRepresentation).symm (toSummand i))
  let ι : ∀ i, S i ⟶ V := fun i =>
    (FDRep.homEquivIntertwiningMap (S i) V).symm
      ((IntertwiningMap.equivLinearMapAsModule (W i).toRepresentation ρ).symm (fromSummand i))
  have hsimple : ∀ i, Simple (S i) := by
    intro i
    haveI := hN i
    haveI : IsSimpleModule ℂ[SymmetricGroup n] ((W i).toRepresentation.asModule) :=
      IsSimpleModule.congr (toSubmodule i)
    haveI : IsIrreducible (W i).toRepresentation :=
      (irreducible_iff_isSimpleModule_asModule _).mpr this
    exact FDRep.simple_of_isIrreducible _
  let b : Bicone S :=
    { pt := V
      π := π
      ι := ι
      ι_π := by
        intro i j
        rcases eq_or_ne i j with rfl | hij
        · rw [dif_pos rfl]
          apply Action.hom_ext
          apply FGModuleCat.hom_ext
          refine LinearMap.ext fun x => ?_
          show toSummand i (fromSummand i x) = x
          simp [toSummand, fromSummand]
        · rw [dif_neg hij]
          apply Action.hom_ext
          apply FGModuleCat.hom_ext
          refine LinearMap.ext fun x => ?_
          show toSummand j (fromSummand i x) = 0
          simp [toSummand, fromSummand, hij] }
  have htotal : ∑ i, b.π i ≫ b.ι i = 𝟙 b.pt := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    have hsum : ∀ s : Finset (Fin k), (∑ i ∈ s, b.π i ≫ b.ι i).hom.hom.hom x =
        ∑ i ∈ s, fromSummand i (toSummand i x) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
    have hsingle : ∀ y : Π₀ i : Fin k, ↥(N i), ∑ i, DFinsupp.single i (y i) = y := fun y =>
      (DFinsupp.sum_eq_sum_fintype y fun i => by simp).symm.trans DFinsupp.sum_single
    rw [hsum]
    simp only [toSummand, fromSummand, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, DFinsupp.lapply_apply, DFinsupp.lsingle_apply]
    rw [← map_sum, hsingle, LinearEquiv.symm_apply_apply]
    rfl
  exact ⟨k, S, hsimple, ⟨biproduct.uniqueUpToIso S (isBilimitOfTotal b htotal)⟩⟩

end Decomposition
