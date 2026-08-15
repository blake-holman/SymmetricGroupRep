import SymmetricGroupRep.Orthogonal
import Mathlib.RepresentationTheory.Character

open scoped Classical

private theorem sqrt_axialDistance_im {n : ℕ} (μ : YoungDiagramOfSize (n + 1))
    (T : StandardYoungTableau μ) (i : Fin n) :
    (Complex.sqrt (1 - ((T.axialDistance i : ℂ)⁻¹) ^ 2)).im = 0 := by
  let d := T.axialDistance i
  have hd : d ≠ 0 := T.axialDistance_ne_zero i
  have hdreal : (1 : ℝ) ≤ |(d : ℝ)| := by
    norm_cast
    exact Int.one_le_abs hd
  have hinvabs : |((d : ℝ)⁻¹)| ≤ 1 := by
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ hdreal
  have hsq : ((d : ℝ)⁻¹) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).2 hinvabs
  have hnonneg : 0 ≤ 1 - ((d : ℝ)⁻¹) ^ 2 := sub_nonneg.mpr hsq
  have hcast : ((d : ℂ)⁻¹) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
    rcases d with d | d <;> simp
  have harg : (1 - ((((d : ℝ)⁻¹ : ℝ) : ℂ) ^ 2) : ℂ) =
      ((1 - ((d : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) := by
    norm_cast
  rw [show T.axialDistance i = d by rfl, hcast, harg,
    Complex.sqrt_of_nonneg (by exact_mod_cast hnonneg)]
  simp

/-- The square-root coefficient in Young's orthogonal adjacent-transposition
formula is real. -/
theorem spechtOrthogonalBasis_adjacentTransposition_sqrt_im {n : ℕ}
    (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    (Complex.sqrt (1 - ((T.axialDistance i : ℂ)⁻¹) ^ 2)).im = 0 :=
  sqrt_axialDistance_im μ T i

/-- Adjacent transpositions generate the symmetric group. -/
theorem symmetricGroup_adjacentTranspositions_generate (n : ℕ) :
    Submonoid.closure (Set.range fun i : Fin n => SymmetricGroup.adjacentTransposition i) = ⊤ := by
  exact Equiv.Perm.mclosure_swap_castSucc_succ n

/-- Every complex Specht character is real-valued. -/
theorem spechtModule_character_im {n : ℕ} (μ : YoungDiagramOfSize n)
    (g : SymmetricGroup n) :
    ((show SymmetricGroupRepresentation n from spechtModule μ).character g).im = 0 := by
  cases n with
  | zero =>
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg, FDRep.char_one]
    simp
  | succ n =>
    letI := Fintype.ofFinite (StandardYoungTableau μ)
    let b := spechtOrthogonalBasis μ
    let realCoordinates : ((spechtModule μ) →ₗ[ℂ] (spechtModule μ)) → Prop :=
      fun f => ∀ U T, (LinearMap.toMatrix b b f U T).im = 0
    have realCoordinates_one : realCoordinates LinearMap.id := by
      intro U T
      change (LinearMap.toMatrix b b LinearMap.id U T).im = 0
      rw [LinearMap.toMatrix_id]
      by_cases h : U = T <;> simp [Matrix.one_apply, h]
    have realCoordinates_mul (f h : (spechtModule μ) →ₗ[ℂ] (spechtModule μ))
        (hf : realCoordinates f) (hh : realCoordinates h) : realCoordinates (f * h) := by
      intro U T
      change (LinearMap.toMatrix b b (f * h) U T).im = 0
      rw [LinearMap.toMatrix_mul, Matrix.mul_apply]
      rw [Complex.im_sum]
      apply Finset.sum_eq_zero
      intro V _
      rw [Complex.mul_im, hf, hh]
      ring
    have realCoordinates_adjacent (i : Fin n) :
        realCoordinates ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)) := by
      intro U T
      change (LinearMap.toMatrix b b
        ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)) U T).im = 0
      rw [LinearMap.toMatrix_apply, spechtOrthogonalBasis_adjacentTransposition]
      have hinv : ((T.axialDistance i : ℂ)⁻¹).im = 0 := by
        rcases T.axialDistance i with d | d <;> simp
      have hsqrt := spechtOrthogonalBasis_adjacentTransposition_sqrt_im μ T i
      have single_im (S : StandardYoungTableau μ) (z : ℂ) (hz : z.im = 0) :
          (Finsupp.single S z U).im = 0 := by
        by_cases hSU : S = U <;> simp [hSU, hz]
      unfold b
      unfold swappedOrthogonalBasisVector
      split_ifs with h
      · simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
          Finsupp.add_apply, Complex.add_im]
        simp only [smul_eq_mul, mul_one]
        rw [single_im T _ hinv, single_im (T.swapAdjacent i h) _ hsqrt]
        simp
      · simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
          Finsupp.add_apply, Complex.add_im, map_zero]
        simpa using single_im T _ hinv
    let H : Submonoid (SymmetricGroup (n + 1)) :=
      {
      carrier := {h | realCoordinates ((spechtModule μ).ρ h)}
      one_mem' := by
        simpa [Module.End.one_eq_id] using realCoordinates_one
      mul_mem' {h k} hh hk := by
        simpa using realCoordinates_mul _ _ hh hk
      }
    have hgenerators : Set.range (fun i : Fin n => SymmetricGroup.adjacentTransposition i) ⊆ H := by
      rintro _ ⟨i, rfl⟩
      exact realCoordinates_adjacent i
    have hclosure : Submonoid.closure
        (Set.range fun i : Fin n => SymmetricGroup.adjacentTransposition i) ≤ H :=
      Submonoid.closure_le.mpr hgenerators
    have hg : g ∈ H := by
      apply hclosure
      rw [symmetricGroup_adjacentTranspositions_generate]
      trivial
    change (LinearMap.trace ℂ (spechtModule μ) ((spechtModule μ).ρ g)).im = 0
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro T _
    exact hg T T
