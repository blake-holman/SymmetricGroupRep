import SymmetricGroupRep.Branching
import SymmetricGroupRep.HookLength
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

universe u

private noncomputable def FDRep.biproductLinearEquivPi
    {k G : Type u} [Field k] [Group G]
    {ι : Type} [Finite ι] (f : ι → FDRep k G) :
    ((⨁ f : FDRep k G) : Type u) ≃ₗ[k] ∀ i, f i := by
  let forgetAction := Action.forget (FGModuleCat k) G
  let forgetFG := forget₂ (FGModuleCat k) (ModuleCat k)
  let e₁ : forgetAction.obj (⨁ f) ≅ ⨁ fun i => forgetAction.obj (f i) :=
    forgetAction.mapBiproduct f
  let e₂ :
      forgetFG.obj (⨁ fun i => forgetAction.obj (f i)) ≅
        ⨁ fun i => forgetFG.obj (forgetAction.obj (f i)) :=
    forgetFG.mapBiproduct (fun i => forgetAction.obj (f i))
  let e₃ :
      (⨁ fun i => forgetFG.obj (forgetAction.obj (f i))) ≅
        ModuleCat.of k (∀ i, f i) :=
    ModuleCat.biproductIsoPi _
  exact (FGModuleCat.isoToLinearEquiv e₁).trans
    (e₂.toLinearEquiv.trans e₃.toLinearEquiv)

/-- Finrank is additive across a finite biproduct of finite-dimensional
representations. -/
theorem FDRep.finrank_biproduct
    {k G : Type u} [Field k] [Group G]
    {ι : Type} [Fintype ι] (f : ι → FDRep k G) :
    Module.finrank k ((⨁ f : FDRep k G) : Type u) =
      ∑ i, Module.finrank k (f i) := by
  rw [(FDRep.biproductLinearEquivPi f).finrank_eq,
    Module.finrank_pi_fintype]

/-- The dimension of `S^μ` is the number of standard tableaux of shape `μ`. -/
theorem spechtModule_finrank_eq_card_standardYoungTableau {n : ℕ}
    (μ : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtModule μ) = Nat.card (StandardYoungTableau μ) := by
  exact Module.finrank_eq_nat_card_basis (spechtTableauBasis μ)

/-- Multiplicative hook formula for the dimension of a Specht module. -/
theorem spechtModule_finrank_mul_hookProduct {n : ℕ}
    (μ : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtModule μ) * μ.val.hookProduct = n.factorial := by
  rw [spechtModule_finrank_eq_card_standardYoungTableau]
  exact standardYoungTableau_card_mul_hookProduct μ

/-- Every complex Specht module has positive dimension. -/
theorem spechtModule_finrank_pos {n : ℕ} (μ : YoungDiagramOfSize n) :
    0 < Module.finrank ℂ (spechtModule μ) := by
  apply Nat.pos_of_mul_pos_right
  rw [spechtModule_finrank_mul_hookProduct μ]
  exact Nat.factorial_pos n

/-- Natural-number form of the hook-length dimension formula. -/
theorem spechtModule_finrank_eq_factorial_div_hookProduct {n : ℕ}
    (μ : YoungDiagramOfSize n) :
    Module.finrank ℂ (spechtModule μ) =
      n.factorial / μ.val.hookProduct := by
  have hdvd : μ.val.hookProduct ∣ n.factorial := by
    refine ⟨Module.finrank ℂ (spechtModule μ), ?_⟩
    rw [mul_comm]
    exact (spechtModule_finrank_mul_hookProduct μ).symm
  exact (Nat.eq_div_iff_mul_eq_left μ.val.hookProduct_pos.ne' hdvd).2
    (spechtModule_finrank_mul_hookProduct μ).symm

/-- Rational form of the hook-length dimension formula. -/
theorem spechtModule_finrank_cast_eq_factorial_div_hookProduct {n : ℕ}
    (μ : YoungDiagramOfSize n) :
    (Module.finrank ℂ (spechtModule μ) : ℚ) =
      (n.factorial : ℚ) / μ.val.hookProduct := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr μ.val.hookProduct_pos.ne')).2
  exact_mod_cast spechtModule_finrank_mul_hookProduct μ

/-- The ratio of two same-size Specht dimensions is the inverse ratio of
their hook products. -/
theorem spechtModule_finrank_ratio {n : ℕ}
    (μ ν : YoungDiagramOfSize n) :
    (Module.finrank ℂ (spechtModule μ) : ℚ) /
        Module.finrank ℂ (spechtModule ν) =
      (ν.val.hookProduct : ℚ) / μ.val.hookProduct := by
  rw [spechtModule_finrank_cast_eq_factorial_div_hookProduct μ,
    spechtModule_finrank_cast_eq_factorial_div_hookProduct ν]
  field_simp [μ.val.hookProduct_pos.ne', ν.val.hookProduct_pos.ne',
    Nat.factorial_ne_zero]

/-- Ratio of dimensions in consecutive ranks, expressed through hook products. -/
theorem spechtModule_finrank_ratio_succ {n : ℕ}
    (μ : YoungDiagramOfSize n) (ν : YoungDiagramOfSize (n + 1)) :
    (Module.finrank ℂ (spechtModule ν) : ℚ) /
        Module.finrank ℂ (spechtModule μ) =
      (n + 1 : ℚ) * μ.val.hookProduct / ν.val.hookProduct := by
  rw [spechtModule_finrank_cast_eq_factorial_div_hookProduct μ,
    spechtModule_finrank_cast_eq_factorial_div_hookProduct ν]
  rw [Nat.factorial_succ]
  push_cast
  field_simp [μ.val.hookProduct_pos.ne', ν.val.hookProduct_pos.ne',
    Nat.factorial_ne_zero]

/-- Taking dimensions in the one-step branching rule. -/
theorem spechtModule_finrank_branching {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) :
    Module.finrank ℂ (spechtModule μ) =
      ∑ ν : OneBoxRemoval μ, Module.finrank ℂ (spechtModule ν.val) := by
  letI := Fintype.ofFinite (OneBoxRemoval μ)
  let e := Classical.choice (spechtModule_branching μ)
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  change Module.finrank ℂ (spechtModule μ) =
    Module.finrank ℂ ((⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val :
      SymmetricGroupRepresentation n) : Type) at h
  rw [h, FDRep.finrank_biproduct]

/-- Taking dimensions in the endpoint-grouped two-step branching rule. -/
theorem spechtModule_finrank_branching_twoSteps_byEndpoint {n : ℕ}
    (μ : YoungDiagramOfSize (n + 2)) :
    Module.finrank ℂ (spechtModule μ) =
      ∑ ν : YoungDiagramOfSize n,
        twoStepBranchingMultiplicity μ ν * Module.finrank ℂ (spechtModule ν) := by
  letI := Fintype.ofFinite (YoungDiagramOfSize n)
  letI (ν : YoungDiagramOfSize n) := Fintype.ofFinite (TwoStepRemovalTo μ ν)
  let e := Classical.choice (spechtModule_branching_twoSteps_byEndpoint μ)
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  change Module.finrank ℂ (spechtModule μ) =
    Module.finrank ℂ ((⨁ fun ν : YoungDiagramOfSize n =>
      ⨁ fun _ : TwoStepRemovalTo μ ν => spechtModule ν :
      SymmetricGroupRepresentation n) : Type) at h
  rw [h, FDRep.finrank_biproduct]
  apply Finset.sum_congr rfl
  intro ν _
  rw [FDRep.finrank_biproduct]
  simp [twoStepBranchingMultiplicity, Nat.card_eq_fintype_card]

/-- Taking dimensions in the endpoint-grouped three-step branching rule. -/
theorem spechtModule_finrank_branching_threeSteps_byEndpoint {n : ℕ}
    (μ : YoungDiagramOfSize (n + 3)) :
    Module.finrank ℂ (spechtModule μ) =
      ∑ ν : YoungDiagramOfSize n,
        threeStepBranchingMultiplicity μ ν * Module.finrank ℂ (spechtModule ν) := by
  letI := Fintype.ofFinite (YoungDiagramOfSize n)
  letI (ν : YoungDiagramOfSize n) := Fintype.ofFinite (ThreeStepRemovalTo μ ν)
  let e := Classical.choice (spechtModule_branching_threeSteps_byEndpoint μ)
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  change Module.finrank ℂ (spechtModule μ) =
    Module.finrank ℂ ((⨁ fun ν : YoungDiagramOfSize n =>
      ⨁ fun _ : ThreeStepRemovalTo μ ν => spechtModule ν :
      SymmetricGroupRepresentation n) : Type) at h
  rw [h, FDRep.finrank_biproduct]
  apply Finset.sum_congr rfl
  intro ν _
  rw [FDRep.finrank_biproduct]
  simp [threeStepBranchingMultiplicity, Nat.card_eq_fintype_card]
