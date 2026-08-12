import SymmetricGroupRep.SpechtForm
import Mathlib.Tactic.Module

/-! # The joint eigenbasis of the Jucys–Murphy operators

Pushing an eigenvector through a branching summand raises the eigenvalue tuple
by the content of the removed cell, so induction on the size produces, for every
standard tableau, a nonzero joint eigenvector of the Jucys–Murphy operators with
eigenvalues the contents of that tableau. Distinct tableaux give distinct
tuples, hence orthogonal vectors, and there are as many of them as the dimension
of the Specht module: they form a basis.

The adjacent transposition then acts on such an eigenvector by a diagonal term
`d⁻¹` plus a vector in the line of the tableau with `i` and `i + 1` exchanged,
which vanishes when that exchange is not standard.

See Vershik and Okounkov, *A New Approach to the Representation Theory of the
Symmetric Groups II*, Section 1.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- **The key algebraic step.** Correcting `ρ(s_i) v` by `d⁻¹ v` turns a joint
eigenvector into a joint eigenvector for the tuple with `i` and `i + 1`
exchanged. -/
theorem jucysMurphy_swap_eigenvector {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (i : Fin n)
    {v : spechtModule μ} {α : Fin (n + 1) → ℤ} {d : ℂ}
    (hv : ∀ k, jucysMurphy (spechtModule μ) k v = (α k : ℂ) • v)
    (hdeq : ((α i.succ : ℂ)) - ((α (Fin.castSucc i) : ℂ)) = d) (hd : d ≠ 0) (k : Fin (n + 1)) :
    jucysMurphy (spechtModule μ) k
        ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v - d⁻¹ • v) =
      (α (Equiv.swap (Fin.castSucc i) i.succ k) : ℂ) •
        ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v - d⁻¹ • v) := by
  rcases eq_or_ne k (Fin.castSucc i) with rfl | hka
  · have hstep : jucysMurphy (spechtModule μ) (Fin.castSucc i)
        ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v) =
          (α i.succ : ℂ) • (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v - v := by
      rw [jucysMurphy_castSucc_adjacent, hv i.succ, map_smul]
    rw [Equiv.swap_apply_left, map_sub, map_smul, hstep, hv (Fin.castSucc i)]
    match_scalars
    · ring
    · field_simp
      linear_combination hdeq
  · rcases eq_or_ne k i.succ with rfl | hkb
    · have hstep : jucysMurphy (spechtModule μ) i.succ
          ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v) =
            (α (Fin.castSucc i) : ℂ) •
              (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v + v := by
        rw [jucysMurphy_succ_adjacent, hv (Fin.castSucc i), map_smul]
      rw [Equiv.swap_apply_right, map_sub, map_smul, hstep, hv i.succ]
      match_scalars
      · ring
      · field_simp
        linear_combination -hdeq
    · have hstep : jucysMurphy (spechtModule μ) k
          ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v) =
            (α k : ℂ) • (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) v := by
        rw [jucysMurphy_adjacent_comm _ _ hka hkb, hv k, map_smul]
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb, map_sub, map_smul, hstep, hv k]
      module

/-- **Existence of the joint eigenvectors.** Induction on the size, pushing an
eigenvector of the smaller Specht module through a branching summand. -/
theorem exists_jucysMurphy_eigenvector : ∀ (n : ℕ) (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ), ∃ v : spechtModule μ, v ≠ 0 ∧
      ∀ k, jucysMurphy (spechtModule μ) k v = (T.content k : ℂ) • v := by
  intro n
  induction n with
  | zero =>
    intro μ T
    haveI : Nontrivial (spechtModule μ : Type) :=
      Submodule.nontrivial_iff_ne_bot.mpr (spechtSubrepresentation_ne_bot μ)
    obtain ⟨v, hv⟩ := exists_ne (0 : spechtModule μ)
    exact ⟨v, hv, fun k => k.elim0⟩
  | succ n ih =>
    intro μ T
    obtain ⟨u, hu, hueigen⟩ := ih T.largestRemoval.val T.restrictLargest
    let e := Classical.choice (spechtModule_branching μ)
    let φ : spechtModule T.largestRemoval.val ⟶
        (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) :=
      biproduct.ι (fun ν : OneBoxRemoval μ => spechtModule ν.val) T.largestRemoval ≫ e.inv
    have hsplit : φ ≫ (e.hom ≫
        biproduct.π (fun ν : OneBoxRemoval μ => spechtModule ν.val) T.largestRemoval) =
          𝟙 (spechtModule T.largestRemoval.val) := by
      simp [φ]
    have hleft : ∀ w : spechtModule T.largestRemoval.val,
        (e.hom ≫ biproduct.π (fun ν : OneBoxRemoval μ => spechtModule ν.val)
          T.largestRemoval).hom.hom.hom (φ.hom.hom.hom w) = w := by
      intro w
      have h := congrArg (fun f : spechtModule T.largestRemoval.val ⟶
        spechtModule T.largestRemoval.val => f.hom.hom.hom w) hsplit
      simpa using h
    have hinj : Function.Injective
        (fun w : spechtModule T.largestRemoval.val => φ.hom.hom.hom w) := fun a b hab =>
      (hleft a).symm.trans ((congrArg _ hab).trans (hleft b))
    refine ⟨φ.hom.hom.hom u, ?_, fun k => ?_⟩
    · intro hzero
      refine hu (hinj ?_)
      show φ.hom.hom.hom u = φ.hom.hom.hom 0
      rw [hzero, map_zero]
      rfl
    refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [T.content_last]
      exact jucysMurphy_last_hom T.largestRemoval φ u
    · rw [jucysMurphy_castSucc_hom_apply (spechtModule μ) φ j u, hueigen j, map_smul]
      exact congrArg (fun z : ℤ => (z : ℂ) • φ.hom.hom.hom u) (T.content_restrictLargest j)

/-- A chosen joint eigenvector of the Jucys–Murphy operators. -/
noncomputable def spechtSpectralVector {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : spechtModule μ :=
  Classical.choose (exists_jucysMurphy_eigenvector n μ T)

theorem spechtSpectralVector_ne_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : spechtSpectralVector T ≠ 0 :=
  (Classical.choose_spec (exists_jucysMurphy_eigenvector n μ T)).1

theorem jucysMurphy_spechtSpectralVector {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) (k : Fin n) :
    jucysMurphy (spechtModule μ) k (spechtSpectralVector T) =
      (T.content k : ℂ) • spechtSpectralVector T :=
  (Classical.choose_spec (exists_jucysMurphy_eigenvector n μ T)).2 k

/-- Eigenvectors for distinct tableaux are orthogonal. -/
theorem spechtForm_spechtSpectralVector_eq_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    {T U : StandardYoungTableau μ} (h : T ≠ U) :
    spechtForm (spechtSpectralVector T) (spechtSpectralVector U) = 0 :=
  spechtForm_eq_zero_of_jucysMurphy_ne (jucysMurphy_spechtSpectralVector T)
    (jucysMurphy_spechtSpectralVector U) fun hcontent =>
      h (StandardYoungTableau.content_injective μ hcontent)

theorem linearIndependent_spechtSpectralVector {n : ℕ} (μ : YoungDiagramOfSize n) :
    LinearIndependent ℂ (fun T : StandardYoungTableau μ => spechtSpectralVector T) := by
  classical
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  refine Fintype.linearIndependent_iff.mpr fun c hc U => ?_
  have hpair : spechtForm (∑ T, c T • spechtSpectralVector T) (spechtSpectralVector U) = 0 := by
    rw [hc]
    exact spechtForm.zero_left _
  rw [spechtForm.sum_left, Finset.sum_eq_single U] at hpair
  · have hself : spechtForm (spechtSpectralVector U) (spechtSpectralVector U) ≠ 0 := fun hzero =>
      spechtSpectralVector_ne_zero U (spechtForm.eq_zero_of_self_eq_zero hzero)
    rw [spechtForm.smul_left] at hpair
    exact (mul_eq_zero.mp hpair).resolve_right hself
  · intro T _ hne
    rw [spechtForm.smul_left, spechtForm_spechtSpectralVector_eq_zero hne, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ U) hmem

/-- **The joint eigenbasis.** -/
noncomputable def spechtSpectralBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ) := by
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  haveI : Nonempty (StandardYoungTableau μ) := ⟨readingTableau μ⟩
  refine basisOfLinearIndependentOfCardEqFinrank (linearIndependent_spechtSpectralVector μ) ?_
  rw [Module.finrank_eq_nat_card_basis (spechtTableauBasis μ), Nat.card_eq_fintype_card]

@[simp]
theorem spechtSpectralBasis_apply {n : ℕ} (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ) : spechtSpectralBasis μ T = spechtSpectralVector T := by
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  haveI : Nonempty (StandardYoungTableau μ) := ⟨readingTableau μ⟩
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) T

theorem repr_spechtSpectralVector {n : ℕ} (μ : YoungDiagramOfSize n)
    (T U : StandardYoungTableau μ) [Decidable (T = U)] :
    (spechtSpectralBasis μ).repr (spechtSpectralVector T) U = if T = U then 1 else 0 := by
  classical
  rw [← spechtSpectralBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- **Spectral coordinates.** A joint eigenvector is supported on the tableaux
whose content tuple is its eigenvalue tuple. -/
theorem repr_spechtSpectralBasis_eq_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    {v : spechtModule μ} {α : Fin n → ℤ}
    (hv : ∀ k, jucysMurphy (spechtModule μ) k v = (α k : ℂ) • v)
    {T : StandardYoungTableau μ} (hT : T.content ≠ α) :
    (spechtSpectralBasis μ).repr v T = 0 := by
  classical
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hT
  set c : StandardYoungTableau μ → ℂ := fun U => (spechtSpectralBasis μ).repr v U with hcdef
  have hexpand : ∑ U, c U • spechtSpectralVector U = v := by
    simpa using (spechtSpectralBasis μ).sum_repr v
  have hleft : jucysMurphy (spechtModule μ) k v =
      ∑ U, (c U * (U.content k : ℂ)) • spechtSpectralVector U := by
    conv_lhs => rw [← hexpand]
    rw [map_sum]
    exact Finset.sum_congr rfl fun U _ => by
      rw [map_smul, jucysMurphy_spechtSpectralVector, smul_smul]
  have hright : (α k : ℂ) • v = ∑ U, ((α k : ℂ) * c U) • spechtSpectralVector U := by
    conv_lhs => rw [← hexpand]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun U _ => smul_smul _ _ _
  have hjm : ∑ U, (c U * (U.content k : ℂ) - (α k : ℂ) * c U) • spechtSpectralVector U = 0 := by
    calc ∑ U, (c U * (U.content k : ℂ) - (α k : ℂ) * c U) • spechtSpectralVector U
        = (∑ U, (c U * (U.content k : ℂ)) • spechtSpectralVector U) -
          ∑ U, ((α k : ℂ) * c U) • spechtSpectralVector U := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun U _ => sub_smul _ _ _
      _ = 0 := by rw [← hleft, ← hright, hv k, sub_self]
  have hzero := Fintype.linearIndependent_iff.mp (linearIndependent_spechtSpectralVector μ) _ hjm T
  have hne : (T.content k : ℂ) - (α k : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hk (by exact_mod_cast h)
  have hfactor : (c T) * ((T.content k : ℂ) - (α k : ℂ)) = 0 := by
    rw [mul_sub, ← hzero]
    ring
  exact (mul_eq_zero.mp hfactor).resolve_right hne

theorem eq_smul_spechtSpectralVector_of_jucysMurphy {n : ℕ} {μ : YoungDiagramOfSize n}
    {v : spechtModule μ} {Q : StandardYoungTableau μ}
    (hv : ∀ k, jucysMurphy (spechtModule μ) k v = (Q.content k : ℂ) • v) :
    ∃ c : ℂ, v = c • spechtSpectralVector Q := by
  classical
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  have hexpand : ∑ U, ((spechtSpectralBasis μ).repr v U) • spechtSpectralVector U = v := by
    simpa using (spechtSpectralBasis μ).sum_repr v
  refine ⟨(spechtSpectralBasis μ).repr v Q, ?_⟩
  conv_lhs => rw [← hexpand]
  exact Finset.sum_eq_single Q (fun U _ hne => by
      rw [repr_spechtSpectralBasis_eq_zero hv fun hcontent =>
        hne (StandardYoungTableau.content_injective μ hcontent), zero_smul])
    (fun hmem => absurd (Finset.mem_univ Q) hmem)

section AdjacentAction

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau μ) (i : Fin n)

/-- The correction to the diagonal term in the action of an adjacent
transposition on a joint eigenvector. -/
noncomputable def spectralSwapCorrection : spechtModule μ :=
  (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtSpectralVector T) -
    ((T.axialDistance i : ℂ))⁻¹ • spechtSpectralVector T

theorem rho_adjacentTransposition_spechtSpectralVector :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtSpectralVector T) =
      ((T.axialDistance i : ℂ))⁻¹ • spechtSpectralVector T + spectralSwapCorrection T i := by
  rw [spectralSwapCorrection, add_sub_cancel]

theorem axialDistance_ne_zero_cast : ((T.axialDistance i : ℤ) : ℂ) ≠ 0 := by
  exact_mod_cast T.axialDistance_ne_zero i

theorem jucysMurphy_spectralSwapCorrection (k : Fin (n + 1)) :
    jucysMurphy (spechtModule μ) k (spectralSwapCorrection T i) =
      (T.content (Equiv.swap (Fin.castSucc i) i.succ k) : ℂ) • spectralSwapCorrection T i := by
  refine jucysMurphy_swap_eigenvector i (jucysMurphy_spechtSpectralVector T) ?_
    (axialDistance_ne_zero_cast T i) k
  rw [StandardYoungTableau.axialDistance]
  push_cast
  ring

/-- The correction is orthogonal to the eigenvector it corrects. -/
theorem spechtForm_spectralSwapCorrection_left :
    spechtForm (spectralSwapCorrection T i) (spechtSpectralVector T) = 0 := by
  refine spechtForm_eq_zero_of_jucysMurphy_ne (jucysMurphy_spectralSwapCorrection T i)
    (jucysMurphy_spechtSpectralVector T) fun hcontent => ?_
  have hat := congrFun hcontent (Fin.castSucc i)
  rw [Equiv.swap_apply_left] at hat
  exact T.axialDistance_ne_zero i (by rw [StandardYoungTableau.axialDistance, hat, sub_self])

theorem spechtForm_spectralSwapCorrection_right :
    spechtForm (spechtSpectralVector T) (spectralSwapCorrection T i) = 0 := by
  refine spechtForm_eq_zero_of_jucysMurphy_ne (jucysMurphy_spechtSpectralVector T)
    (jucysMurphy_spectralSwapCorrection T i) fun hcontent => ?_
  have hat := congrFun hcontent (Fin.castSucc i)
  rw [Equiv.swap_apply_left] at hat
  exact T.axialDistance_ne_zero i (by rw [StandardYoungTableau.axialDistance, ← hat, sub_self])

/-- **The length of the correction.** Isometry and orthogonality give it. -/
theorem spechtForm_spectralSwapCorrection_self :
    spechtForm (spectralSwapCorrection T i) (spectralSwapCorrection T i) =
      (1 - ((T.axialDistance i : ℂ))⁻¹ ^ 2) *
        spechtForm (spechtSpectralVector T) (spechtSpectralVector T) := by
  have hconj : (starRingEnd ℂ) ((T.axialDistance i : ℂ))⁻¹ = ((T.axialDistance i : ℂ))⁻¹ := by
    rw [map_inv₀, map_intCast]
  have hiso := spechtForm.rho (SymmetricGroup.adjacentTransposition i)
    (spechtSpectralVector T) (spechtSpectralVector T)
  rw [rho_adjacentTransposition_spechtSpectralVector T i, spechtForm.add_left,
    spechtForm.add_right, spechtForm.add_right, spechtForm.smul_left, spechtForm.smul_right,
    spechtForm.smul_left, spechtForm.smul_right, spechtForm_spectralSwapCorrection_left,
    spechtForm_spectralSwapCorrection_right, hconj] at hiso
  linear_combination hiso

/-- Outside the standard case the correction vanishes. -/
theorem spectralSwapCorrection_eq_zero (h : ¬ T.IsAdjacentSwapStandard i) :
    spectralSwapCorrection T i = 0 := by
  have hnat : (T.axialDistance i).natAbs = 1 := by
    have hne := T.axialDistance_ne_zero i
    have hlt : ¬ 2 ≤ (T.axialDistance i).natAbs :=
      fun htwo => h ((T.isAdjacentSwapStandard_iff_two_le_natAbs i).mpr htwo)
    have : (T.axialDistance i).natAbs ≠ 0 := fun hzero => hne (Int.natAbs_eq_zero.mp hzero)
    omega
  have hsq : ((T.axialDistance i : ℂ))⁻¹ ^ 2 = 1 := by
    rcases Int.natAbs_eq_iff.mp hnat with hcase | hcase <;> rw [hcase] <;> norm_num
  refine spechtForm.eq_zero_of_self_eq_zero ?_
  rw [spechtForm_spectralSwapCorrection_self, hsq, sub_self, zero_mul]

/-- In the standard case the correction lies in the line of the swapped
tableau. -/
theorem exists_spectralSwapCorrection_eq_smul (h : T.IsAdjacentSwapStandard i) :
    ∃ c : ℂ, spectralSwapCorrection T i = c • spechtSpectralVector (T.swapAdjacent i h) := by
  refine eq_smul_spechtSpectralVector_of_jucysMurphy fun k => ?_
  rw [jucysMurphy_spectralSwapCorrection, T.content_swapAdjacent i h k]

end AdjacentAction
