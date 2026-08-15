import SymmetricGroupRep.Biregular
import SymmetricGroupRep.Dimensions
import SymmetricGroupRep.ProductClassification
import SymmetricGroupRep.YoungSubgroup
import Mathlib.GroupTheory.Perm.Finite

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] Fintype.ofFinite

noncomputable section

namespace FDRep

/-- Outer tensor products carry isomorphisms in both factors. -/
def outerTensorIso {G H : Type} [Monoid G] [Monoid H]
    {V V' : FDRep ℂ G} {W W' : FDRep ℂ H}
    (eV : V ≅ V') (eW : W ≅ W') :
    outerTensor V W ≅ outerTensor V' W' := by
  let eV' := FDRep.isoToLinearEquiv eV
  let eW' := FDRep.isoToLinearEquiv eW
  let E : Representation.Equiv (outerTensor V W).ρ (outerTensor V' W').ρ :=
    Representation.Equiv.mk (TensorProduct.congr eV' eW') fun gh => by
      obtain ⟨g, h⟩ := gh
      apply TensorProduct.ext'
      intro v w
      have hV := LinearMap.congr_fun (FDRep.Iso.conj_ρ eV g) (eV' v)
      have hW := LinearMap.congr_fun (FDRep.Iso.conj_ρ eW h) (eW' w)
      have htmul := congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) hV.symm hW.symm
      simp only [eV', eW', LinearEquiv.conj_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at htmul
      exact htmul
  exact Action.mkIso E.toLinearEquiv.toFGModuleCatIso fun gh => by
    apply FGModuleCat.hom_ext
    exact E.toIntertwiningMap.2 gh

end FDRep

/-- A permutation preserving the initial `a`-point block belongs to the
standard Young subgroup `S_a x S_b`. -/
theorem exists_youngSubgroup_eq_of_mapsTo_castAdd
    {a b : Nat} (sigma : SymmetricGroup (a + b))
    (h : Set.MapsTo sigma (Set.range (Fin.castAdd b))
      (Set.range (Fin.castAdd b))) :
    exists p : SymmetricGroup a × SymmetricGroup b,
      SymmetricGroup.youngSubgroupInclusion a b p = sigma := by
  let sigma' : Equiv.Perm (Fin a ⊕ Fin b) :=
    finSumFinEquiv.symm.permCongr sigma
  have h' : Set.MapsTo sigma' (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := h ⟨i, rfl⟩
    refine ⟨j, ?_⟩
    apply finSumFinEquiv.injective
    simpa [sigma'] using hj
  obtain ⟨p, hp⟩ :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl h'
  refine ⟨p, ?_⟩
  have hp' : Equiv.Perm.sumCongr p.1 p.2 = sigma' := hp
  change finSumFinEquiv.permCongr (Equiv.Perm.sumCongr p.1 p.2) = sigma
  rw [hp']
  change finSumFinEquiv.permCongr (finSumFinEquiv.permCongr.symm sigma) = sigma
  exact finSumFinEquiv.permCongr.apply_symm_apply sigma

/-- Peter-Weyl for `S_n`, with self-duality used to put both Specht labels in
the same convention. -/
theorem symmetricGroupBiregular_diagonal_decomposition (n : Nat) :
    Nonempty (symmetricGroupBiregular n ≅
      ⨁ fun mu : YoungDiagramOfSize n => spechtOuterTensor mu mu) := by
  let decompose := Classical.choice (symmetricGroupBiregular_decomposition n)
  let selfDualize := biproduct.mapIso fun mu : YoungDiagramOfSize n =>
    FDRep.outerTensorIso (Iso.refl (spechtModule mu))
      (Classical.choice (spechtModule_selfDual mu)).symm
  exact ⟨decompose ≪≫ selfDualize⟩

open scoped Classical in
/-- The biregular module contains the diagonal product Specht modules once and
contains every off-diagonal product Specht module zero times. -/
theorem symmetricGroupBiregular_homFinrank (n : Nat)
    (lambda mu : YoungDiagramOfSize n) :
    FDRep.homFinrank (spechtOuterTensor lambda mu)
        (symmetricGroupBiregular n) =
      if lambda = mu then 1 else 0 := by
  classical
  letI : Simple (spechtOuterTensor lambda mu) :=
    spechtOuterTensor_irreducible lambda mu
  let diagonal := fun nu : YoungDiagramOfSize n => spechtOuterTensor nu nu
  have hterm (nu : YoungDiagramOfSize n) :
      FDRep.homFinrank (spechtOuterTensor lambda mu) (diagonal nu) =
        if lambda = nu ∧ mu = nu then 1 else 0 := by
    letI : Simple (diagonal nu) := spechtOuterTensor_irreducible nu nu
    unfold FDRep.homFinrank
    rw [FDRep.finrank_hom_simple_simple]
    rw [spechtOuterTensor_iso_iff_eq lambda nu mu nu]
    by_cases h : lambda = nu ∧ mu = nu <;> simp [h]
  calc
    FDRep.homFinrank (spechtOuterTensor lambda mu)
        (symmetricGroupBiregular n) =
        FDRep.homFinrank (spechtOuterTensor lambda mu) (⨁ diagonal) :=
      FDRep.homFinrank_iso_target _
        (Classical.choice (symmetricGroupBiregular_diagonal_decomposition n))
    _ = ∑ nu, FDRep.homFinrank
          (spechtOuterTensor lambda mu) (diagonal nu) :=
      FDRep.homFinrank_biproduct _ diagonal
    _ = ∑ nu : YoungDiagramOfSize n,
          if lambda = nu ∧ mu = nu then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro nu _
      exact hterm nu
    _ = if lambda = mu then 1 else 0 := by
      by_cases h : lambda = mu
      · subst mu
        simp
      · have h' : mu ≠ lambda := Ne.symm h
        simp [h, h']
