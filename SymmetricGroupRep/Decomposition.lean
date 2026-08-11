import SymmetricGroupRep.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Decomposing a representation of a finite group into simples

Mathlib decomposes a semisimple module over a ring into finitely many simple submodules
(`IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`), and Maschke makes every
`Representation ℂ G V` semisimple as a module over the group algebra. What is missing is the
translation back into `FDRep ℂ G`, where this package states its results. Mathlib does
compare `FDRep` morphisms with intertwining maps, via `FDRep.forget₂HomLinearEquiv` and
`Rep.homLinearEquiv`; what it does not have is a bridge from `Representation.IsIrreducible` to
`CategoryTheory.Simple`, or between the `ℂ[G]`-module of a subrepresentation and the submodule
it comes from. The declarations below supply those, and `exists_iso_biproduct_simples` assembles
the module-level decomposition into a biproduct in `FDRep ℂ G`.

That biproduct lists its simple summands with repetitions, whereas every consumer wants them
grouped: `exists_iso_biproduct_multiplicity` regroups them along a fixed family of pairwise
non-isomorphic simples, with each member repeated as often as its Hom-space dimension records.
Two representations with the same multiplicities are then isomorphic, and equal characters are
one way to know that they are.

Everything here is stated for an arbitrary finite group rather than for a symmetric group, since
the classification of the simples of `S_m × S_n` and the biregular decomposition both need it over
a product.

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

namespace FDRep

/-- Postcomposition with an isomorphism identifies equivariant Hom spaces. -/
noncomputable def homCongrTarget {G : Type} [Monoid G] (W : FDRep ℂ G)
    {V V' : FDRep ℂ G} (e : V ≅ V') :
    (W ⟶ V) ≃ₗ[ℂ] (W ⟶ V') where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Maps into a finite biproduct are freely specified componentwise. -/
noncomputable def homBiproductLinearEquiv {G ι : Type} [Monoid G] [Fintype ι]
    (W : FDRep ℂ G) (V : ι → FDRep ℂ G) :
    (W ⟶ ⨁ V) ≃ₗ[ℂ] (∀ i, W ⟶ V i) where
  toFun f i := f ≫ biproduct.π V i
  invFun f := biproduct.lift f
  left_inv f := by
    ext i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp
  map_smul' c f := by
    funext i
    simp

/-- Dimension of an equivariant Hom space, kept local to the representation package. -/
noncomputable def homFinrank {G : Type} [Monoid G] (W V : FDRep ℂ G) : Nat :=
  Module.finrank ℂ (W ⟶ V)

theorem homFinrank_iso_target {G : Type} [Monoid G]
    (W : FDRep ℂ G) {V V' : FDRep ℂ G} (e : V ≅ V') :
    homFinrank W V = homFinrank W V' := by
  exact (homCongrTarget W e).finrank_eq

theorem homFinrank_biproduct {G ι : Type}
    [Group G] [Fintype ι] (W : FDRep ℂ G) (V : ι → FDRep ℂ G) :
    homFinrank W (⨁ V) = ∑ i, homFinrank W (V i) := by
  unfold homFinrank
  rw [(homBiproductLinearEquiv W V).finrank_eq, Module.finrank_pi_fintype]

end FDRep

set_option backward.isDefEq.respectTransparency false in
/-- Complete reducibility: every finite-dimensional complex representation of a finite group
is isomorphic to a finite biproduct of simple representations. -/
theorem FDRep.exists_iso_biproduct_simples {G : Type} [Group G] [Finite G]
    [NeZero (Nat.card G : ℂ)] (V : FDRep ℂ G) :
    ∃ (k : ℕ) (S : Fin k → FDRep ℂ G),
      (∀ i, Simple (S i)) ∧ Nonempty (V ≅ ⨁ S) := by
  classical
  let ρ : Representation ℂ G V := V.ρ
  haveI : Module.Finite ℂ[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  obtain ⟨k, N, e, hN⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G] ρ.asModule
  -- `N` is a family of simple `ℂ[G]`-submodules with `ρ.asModule ≃ ⨁ N i`; read it back as a
  -- family of subrepresentations, and take the summands to be those subrepresentations.
  let W : Fin k → Subrepresentation ρ := fun i => Subrepresentation.ofSubmodule' (N i)
  let S : Fin k → FDRep ℂ G := fun i => FDRep.of (W i).toRepresentation
  let toSubmodule : ∀ i, (W i).toRepresentation.asModule ≃ₗ[ℂ[G]] N i :=
    fun i => Subrepresentation.asModuleEquivOfSubmodule (N i)
  let toSummand : ∀ i, ρ.asModule →ₗ[ℂ[G]] (W i).toRepresentation.asModule :=
    fun i => (toSubmodule i).symm.toLinearMap ∘ₗ DFinsupp.lapply i ∘ₗ e.toLinearMap
  let fromSummand : ∀ i, (W i).toRepresentation.asModule →ₗ[ℂ[G]] ρ.asModule :=
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
    haveI : IsSimpleModule ℂ[G] ((W i).toRepresentation.asModule) :=
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

/-- Complete reducibility in multiplicity form: if the `S i` are pairwise non-isomorphic simples
and every simple is isomorphic to one of them, then each `V` is the biproduct of
`finrank ℂ (S i ⟶ V)` copies of `S i`.

`exists_iso_biproduct_simples` gives a biproduct of simples listed with repetitions; classifying
each summand by the member of `S` it is isomorphic to regroups that list, and Schur's lemma
counts each fibre as a Hom-space dimension. -/
theorem FDRep.exists_iso_biproduct_multiplicity {G ι : Type} [Group G] [Finite G]
    [NeZero (Nat.card G : ℂ)]
    [Finite ι] (S : ι → FDRep ℂ G) (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ T : FDRep ℂ G, Simple T → ∃ i, Nonempty (T ≅ S i))
    (V : FDRep ℂ G) :
    Nonempty (V ≅ ⨁ fun i => ⨁ fun _ : Fin (Module.finrank ℂ (S i ⟶ V)) => S i) := by
  classical
  obtain ⟨k, T, hT, ⟨e⟩⟩ := FDRep.exists_iso_biproduct_simples V
  choose c hc using fun j => hcomplete (T j) (hT j)
  have hiff : ∀ i j, Nonempty (S i ≅ T j) ↔ c j = i := by
    intro i j
    refine ⟨fun ⟨f⟩ => hdistinct (c j) i ⟨(Classical.choice (hc j)).symm ≪≫ f.symm⟩, ?_⟩
    rintro rfl
    exact ⟨(Classical.choice (hc j)).symm⟩
  have hcard : ∀ i, Nat.card {j // c j = i} = Module.finrank ℂ (S i ⟶ V) := by
    intro i
    haveI := hsimple i
    rw [(FDRep.homCongrTarget (S i) e).finrank_eq,
      (FDRep.homBiproductLinearEquiv (S i) T).finrank_eq, Module.finrank_pi_fintype]
    have hterm : ∀ j, Module.finrank ℂ (S i ⟶ T j) = if c j = i then 1 else 0 := by
      intro j
      haveI := hT j
      rw [FDRep.finrank_hom_simple_simple, if_congr (hiff i j) rfl rfl]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_boole]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let fiber : ι → Type := fun i => {j // c j = i}
  let reindex : (⨁ fun j => S (c j)) ≅ ⨁ fun q : Σ i, fiber i => S q.1 :=
    biproduct.reindex (Equiv.sigmaFiberEquiv c).symm fun q : Σ i, fiber i => S q.1
  let regroup : (⨁ fun i => ⨁ fun _ : fiber i => S i) ≅ ⨁ fun q : Σ i, fiber i => S q.1 :=
    biproductBiproductIso fiber fun i _ => S i
  let resize : ∀ i, (⨁ fun _ : fiber i => S i) ≅
      ⨁ fun _ : Fin (Module.finrank ℂ (S i ⟶ V)) => S i :=
    fun i => biproduct.reindex (Finite.equivFinOfCardEq (hcard i)) fun _ => S i
  exact ⟨e ≪≫ biproduct.mapIso (fun j => Classical.choice (hc j)) ≪≫ reindex ≪≫ regroup.symm ≪≫
    biproduct.mapIso resize⟩

/-- Representations that contain each simple equally often are isomorphic: the multiplicity
decomposition writes both as the same biproduct. -/
theorem FDRep.nonempty_iso_of_finrank_hom_eq {G ι : Type} [Group G] [Finite G]
    [NeZero (Nat.card G : ℂ)]
    [Finite ι] (S : ι → FDRep ℂ G) (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ T : FDRep ℂ G, Simple T → ∃ i, Nonempty (T ≅ S i))
    {V W : FDRep ℂ G}
    (hmult : ∀ i, Module.finrank ℂ (S i ⟶ V) = Module.finrank ℂ (S i ⟶ W)) :
    Nonempty (V ≅ W) := by
  obtain ⟨eV⟩ := FDRep.exists_iso_biproduct_multiplicity S hsimple hdistinct hcomplete V
  obtain ⟨eW⟩ := FDRep.exists_iso_biproduct_multiplicity S hsimple hdistinct hcomplete W
  exact ⟨eV ≪≫ biproduct.mapIso
    (fun i => biproduct.reindex (finCongr (hmult i)) fun _ => S i) ≪≫ eW.symm⟩

/-- Representations with equal characters are isomorphic.

Mathlib has only the forward direction, `FDRep.char_iso`. The converse reads the multiplicities
through the character pairing: `scalar_product_char_eq_finrank_equivariant` computes each
multiplicity as a scalar product of characters, so equal characters give equal multiplicities. -/
theorem FDRep.nonempty_iso_of_character_eq_of_complete {G ι : Type} [Group G] [Finite G]
    [NeZero (Nat.card G : ℂ)]
    [Finite ι] (S : ι → FDRep ℂ G) (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ T : FDRep ℂ G, Simple T → ∃ i, Nonempty (T ≅ S i))
    {V W : FDRep ℂ G} (h : V.character = W.character) :
    Nonempty (V ≅ W) := by
  haveI := Fintype.ofFinite G
  refine FDRep.nonempty_iso_of_finrank_hom_eq S hsimple hdistinct hcomplete fun i => ?_
  have hV := FDRep.scalar_product_char_eq_finrank_equivariant (S i) V
  rw [h] at hV
  exact_mod_cast hV.symm.trans (FDRep.scalar_product_char_eq_finrank_equivariant (S i) W)

end Decomposition
