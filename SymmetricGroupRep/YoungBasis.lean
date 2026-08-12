import SymmetricGroupRep.SpectralBasis
import SymmetricGroupRep.TableauInversions
import Mathlib.Analysis.RCLike.Sqrt

/-! # Young's orthogonal basis

Transporting the spectral vector of the reading tableau by the permutation that
produces `T` gives a vector whose expansion in the spectral basis is supported
on the tableaux with at most as many inversions as `T`, and whose leading
coefficient at `T` is nonzero. Scaling the resulting leading vectors to unit
length produces Young's orthogonal basis: on it an adjacent transposition acts
by `d⁻¹` on the diagonal and by the *positive* square root of `1 - d⁻²` off it,
because the off-diagonal coefficient is a ratio of lengths.

See Vershik and Okounkov, *A New Approach to the Representation Theory of the
Symmetric Groups II*, Theorem 5.8, and Geetha and Prasad, *Comparison of
Gelfand--Tsetlin Bases for Alternating and Symmetric Groups*, Section 2.
-/

open CategoryTheory

/-- The Young coefficient does not degenerate when the axial distance is at
least two in absolute value. -/
theorem one_sub_inv_sq_ne_zero_of_two_le {d : ℤ} (h : 2 ≤ d.natAbs) :
    (1 : ℂ) - ((d : ℂ))⁻¹ ^ 2 ≠ 0 := by
  have hd0 : d ≠ 0 := by omega
  have hdc : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd0
  intro hzero
  have hsq : ((d : ℂ)) ^ 2 = 1 := by
    field_simp at hzero
    linear_combination hzero
  have hd2 : d ^ 2 = 1 := by exact_mod_cast hsq
  have hnat : d.natAbs ^ 2 = 1 := by rw [← Int.natAbs_pow, hd2]; rfl
  have : d.natAbs = 1 := (Nat.pow_eq_one.mp hnat).resolve_right (by norm_num)
  omega

section Filtration

variable {n : ℕ} (μ : YoungDiagramOfSize n)

/-- The span of the spectral vectors of the tableaux with at most `m`
inversions. -/
noncomputable def spechtInversionFiltration (m : ℕ) : Submodule ℂ (spechtModule μ) :=
  Submodule.span ℂ (spechtSpectralVector '' {Q : StandardYoungTableau μ | Q.inversions ≤ m})

theorem spechtSpectralVector_mem_filtration {m : ℕ} {Q : StandardYoungTableau μ}
    (h : Q.inversions ≤ m) : spechtSpectralVector Q ∈ spechtInversionFiltration μ m :=
  Submodule.subset_span ⟨Q, h, rfl⟩

theorem spechtInversionFiltration_mono {m m' : ℕ} (h : m ≤ m') :
    spechtInversionFiltration μ m ≤ spechtInversionFiltration μ m' :=
  Submodule.span_mono (Set.image_mono fun _ hQ => le_trans hQ h)

theorem repr_eq_zero_of_mem_spechtInversionFiltration {m : ℕ} {x : spechtModule μ}
    (hx : x ∈ spechtInversionFiltration μ m) {Q : StandardYoungTableau μ}
    (hQ : m < Q.inversions) : (spechtSpectralBasis μ).repr x Q = 0 := by
  classical
  have hker : spechtInversionFiltration μ m ≤ LinearMap.ker
      ((Finsupp.lapply Q).comp (spechtSpectralBasis μ).repr.toLinearMap) := by
    rw [spechtInversionFiltration, Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe]
    rw [repr_spechtSpectralVector, if_neg]
    exact fun hPQ => absurd (hPQ ▸ hP) (not_le.mpr hQ)
  exact hker hx

end Filtration

section AdjacentFiltration

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (i : Fin n)

theorem rho_adjacentTransposition_mem_filtration {m : ℕ} {x : spechtModule μ}
    (hx : x ∈ spechtInversionFiltration μ m) :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) x ∈
      spechtInversionFiltration μ (m + 1) := by
  have hgen : spechtInversionFiltration μ m ≤ Submodule.comap
      ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i))
      (spechtInversionFiltration μ (m + 1)) := by
    rw [spechtInversionFiltration, Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [rho_adjacentTransposition_spechtSpectralVector]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _
      (spechtSpectralVector_mem_filtration μ (hP.trans (Nat.le_succ m)))) ?_
    by_cases hstd : P.IsAdjacentSwapStandard i
    · obtain ⟨c, hc⟩ := exists_spectralSwapCorrection_eq_smul P i hstd
      rw [hc]
      exact Submodule.smul_mem _ _ (spechtSpectralVector_mem_filtration μ
        ((P.inversions_swapAdjacent_le i hstd).trans (Nat.succ_le_succ hP)))
    · rw [spectralSwapCorrection_eq_zero P i hstd]
      exact Submodule.zero_mem _
  exact hgen hx

/-- The correction is orthogonal to every spectral vector other than the one it
points at. -/
theorem repr_rho_adjacentTransposition_spectralVector_eq_zero
    (P S : StandardYoungTableau μ) (hPS : P ≠ S)
    (hswap : ∀ hP : P.IsAdjacentSwapStandard i, P.swapAdjacent i hP ≠ S) :
    (spechtSpectralBasis μ).repr
      ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtSpectralVector P))
        S = 0 := by
  classical
  rw [rho_adjacentTransposition_spechtSpectralVector, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, repr_spechtSpectralVector, if_neg hPS, smul_zero, zero_add]
  by_cases hstd : P.IsAdjacentSwapStandard i
  · obtain ⟨c, hc⟩ := exists_spectralSwapCorrection_eq_smul P i hstd
    rw [hc, map_smul, Finsupp.smul_apply, repr_spechtSpectralVector, if_neg (hswap hstd),
      smul_zero]
  · simp [spectralSwapCorrection_eq_zero P i hstd]

end AdjacentFiltration

/-- **The filtration by inversions.** -/
theorem rho_readingPermutation_mem_filtration :
    ∀ (N : ℕ) {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ),
      T.inversions ≤ N →
      (spechtModule μ).ρ T.readingPermutation (spechtSpectralVector (readingTableau μ)) ∈
        spechtInversionFiltration μ T.inversions := by
  have hbase : ∀ {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ),
      T.inversions = 0 →
      (spechtModule μ).ρ T.readingPermutation (spechtSpectralVector (readingTableau μ)) ∈
        spechtInversionFiltration μ T.inversions := by
    intro n μ T hzero
    have hT : T = readingTableau μ := T.eq_readingTableau_of_inversions_eq_zero hzero
    subst hT
    rw [StandardYoungTableau.readingPermutation_readingTableau, map_one]
    exact spechtSpectralVector_mem_filtration μ le_rfl
  intro N
  induction N with
  | zero => exact fun T hle => hbase T (Nat.le_zero.mp hle)
  | succ N ih =>
    intro n μ T hle
    by_cases hzero : T.inversions = 0
    · exact hbase T hzero
    · have hpos := T.pos_of_inversions_ne_zero hzero
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨i, hi, hlt⟩ := T.exists_swapAdjacent_inversions_lt hzero
      have hperm : T.readingPermutation = SymmetricGroup.adjacentTransposition i *
          (T.swapAdjacent i hi).readingPermutation := by
        rw [StandardYoungTableau.readingPermutation_swapAdjacent, ← mul_assoc,
          adjacentTransposition_mul_self, one_mul]
      rw [hperm, FDRep.rho_mul_apply]
      exact spechtInversionFiltration_mono μ (by omega)
        (rho_adjacentTransposition_mem_filtration i (ih (T.swapAdjacent i hi) (by omega)))

/-- The coefficient of `T` in the transported reading vector. -/
noncomputable def spechtLeadingCoefficient {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : ℂ :=
  (spechtSpectralBasis μ).repr
    ((spechtModule μ).ρ T.readingPermutation (spechtSpectralVector (readingTableau μ))) T

theorem repr_rho_readingPermutation_eq_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    (T Q : StandardYoungTableau μ) (h : T.inversions < Q.inversions) :
    (spechtSpectralBasis μ).repr
      ((spechtModule μ).ρ T.readingPermutation (spechtSpectralVector (readingTableau μ)))
        Q = 0 :=
  repr_eq_zero_of_mem_spechtInversionFiltration μ
    (rho_readingPermutation_mem_filtration T.inversions T le_rfl) h

/-- **The leading coefficient propagates along an up-step.** -/
theorem spechtLeadingCoefficient_swapAdjacent {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    (T : StandardYoungTableau μ) (i : Fin n) (h : T.IsAdjacentSwapStandard i)
    (hup : T.inversions < (T.swapAdjacent i h).inversions) {γ : ℂ}
    (hγ : spectralSwapCorrection T i = γ • spechtSpectralVector (T.swapAdjacent i h)) :
    spechtLeadingCoefficient (T.swapAdjacent i h) = spechtLeadingCoefficient T * γ := by
  classical
  letI : Fintype (StandardYoungTableau μ) := Fintype.ofFinite _
  set S := T.swapAdjacent i h with hS
  set x := (spechtModule μ).ρ T.readingPermutation (spechtSpectralVector (readingTableau μ))
    with hx
  have hTS : T ≠ S := fun hcontra => absurd (hcontra ▸ hup) (lt_irrefl _)
  have hexpand : ∑ P, ((spechtSpectralBasis μ).repr x P) • spechtSpectralVector P = x := by
    simpa using (spechtSpectralBasis μ).sum_repr x
  have hy : (spechtModule μ).ρ S.readingPermutation (spechtSpectralVector (readingTableau μ)) =
      ∑ P, ((spechtSpectralBasis μ).repr x P) •
        ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
          (spechtSpectralVector P)) := by
    rw [StandardYoungTableau.readingPermutation_swapAdjacent, FDRep.rho_mul_apply, ← hx]
    conv_lhs => rw [← hexpand]
    rw [map_sum]
    exact Finset.sum_congr rfl fun P _ => map_smul _ _ _
  have hdiag : (spechtSpectralBasis μ).repr
      ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtSpectralVector T))
        S = γ := by
    rw [rho_adjacentTransposition_spechtSpectralVector, hγ, map_add, map_smul, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, repr_spechtSpectralVector,
      repr_spechtSpectralVector, if_neg hTS, if_pos rfl, smul_zero, zero_add, smul_eq_mul,
      mul_one]
  rw [spechtLeadingCoefficient, hy, map_sum, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single T]
  · rw [map_smul, Finsupp.smul_apply, hdiag, smul_eq_mul, spechtLeadingCoefficient, ← hx]
  · intro P _ hne
    have hstdS : S.IsAdjacentSwapStandard i := T.isAdjacentSwapStandard_swapAdjacent i h
    rcases lt_or_ge T.inversions P.inversions with hgt | hle
    · have hzeroP : (spechtSpectralBasis μ).repr x P = 0 := by
        rw [hx]
        exact repr_rho_readingPermutation_eq_zero T P hgt
      simp [hzeroP]
    · have hPS : P ≠ S := fun hcontra => absurd (hcontra ▸ hle) (not_le.mpr hup)
      have hswap : ∀ hP : P.IsAdjacentSwapStandard i, P.swapAdjacent i hP ≠ S := by
        intro hP hcontra
        refine hne ?_
        have hentry : P.entry = (S.swapAdjacent i hstdS).entry := by
          refine Equiv.ext fun c => ?_
          have hc : (P.swapAdjacent i hP).entry c = S.entry c :=
            congrArg (fun e : StandardYoungTableau μ => e.entry c) hcontra
          show P.entry c = Equiv.swap (Fin.castSucc i) i.succ (S.entry c)
          rw [← hc]
          exact (Equiv.swap_apply_self _ _ _).symm
        rw [StandardYoungTableau.ext hentry, T.swapAdjacent_swapAdjacent i h]
      rw [map_smul, Finsupp.smul_apply,
        repr_rho_adjacentTransposition_spectralVector_eq_zero i P S hPS hswap, smul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ T) hmem

private theorem spechtLeadingCoefficient_ne_zero_of_le :
    ∀ (N : ℕ) {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ),
      T.inversions ≤ N → spechtLeadingCoefficient T ≠ 0 := by
  have hbase : ∀ {n : ℕ} {μ : YoungDiagramOfSize n} (T : StandardYoungTableau μ),
      T.inversions = 0 → spechtLeadingCoefficient T ≠ 0 := by
    classical
    intro n μ T hzero
    have hT : T = readingTableau μ := T.eq_readingTableau_of_inversions_eq_zero hzero
    subst hT
    rw [spechtLeadingCoefficient, StandardYoungTableau.readingPermutation_readingTableau,
      map_one]
    show (spechtSpectralBasis μ).repr (spechtSpectralVector (readingTableau μ))
      (readingTableau μ) ≠ 0
    rw [repr_spechtSpectralVector, if_pos rfl]
    exact one_ne_zero
  intro N
  induction N with
  | zero => exact fun T hle => hbase T (Nat.le_zero.mp hle)
  | succ N ih =>
    intro n μ T hle
    by_cases hzero : T.inversions = 0
    · exact hbase T hzero
    · have hpos := T.pos_of_inversions_ne_zero hzero
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨i, hi, hlt⟩ := T.exists_swapAdjacent_inversions_lt hzero
      have hback : (T.swapAdjacent i hi).swapAdjacent i
          (T.isAdjacentSwapStandard_swapAdjacent i hi) = T := T.swapAdjacent_swapAdjacent i hi
      have hstd := T.isAdjacentSwapStandard_swapAdjacent i hi
      obtain ⟨γ, hγ⟩ := exists_spectralSwapCorrection_eq_smul (T.swapAdjacent i hi) i hstd
      have hγne : γ ≠ 0 := by
        intro hzeroγ
        have hcorr : spectralSwapCorrection (T.swapAdjacent i hi) i = 0 := by
          rw [hγ, hzeroγ, zero_smul]
        have hnorm := spechtForm_spectralSwapCorrection_self (T.swapAdjacent i hi) i
        have hself : spechtForm (spechtSpectralVector (T.swapAdjacent i hi))
            (spechtSpectralVector (T.swapAdjacent i hi)) ≠ 0 := fun hz =>
          spechtSpectralVector_ne_zero _ (spechtForm.eq_zero_of_self_eq_zero hz)
        rw [hcorr, spechtForm.zero_left] at hnorm
        have hzero' : (1 - (((T.swapAdjacent i hi).axialDistance i : ℂ))⁻¹ ^ 2) = 0 :=
          (mul_eq_zero.mp hnorm.symm).resolve_right hself
        exact absurd hzero' (one_sub_inv_sq_ne_zero_of_two_le
          ((StandardYoungTableau.isAdjacentSwapStandard_iff_two_le_natAbs _ i).mp hstd))
      have hrec := spechtLeadingCoefficient_swapAdjacent (T.swapAdjacent i hi) i hstd
        (by rw [hback]; exact hlt) hγ
      rw [hback] at hrec
      rw [hrec]
      exact mul_ne_zero (ih (T.swapAdjacent i hi) (by omega)) hγne

/-- **The leading coefficient never vanishes.** -/
theorem spechtLeadingCoefficient_ne_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : spechtLeadingCoefficient T ≠ 0 :=
  spechtLeadingCoefficient_ne_zero_of_le T.inversions T le_rfl

section Coefficient

theorem one_sub_inv_sq_nonneg {d : ℤ} (hd : d ≠ 0) : 0 ≤ 1 - ((d : ℝ))⁻¹ ^ 2 := by
  have habs : (1 : ℝ) ≤ |(d : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hd
  have hinv : |((d : ℝ))⁻¹| ≤ 1 := by
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ habs
  exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 hinv)

theorem one_sub_inv_sq_pos_of_two_le {d : ℤ} (h : 2 ≤ d.natAbs) : 0 < 1 - ((d : ℝ))⁻¹ ^ 2 := by
  have hd : d ≠ 0 := by omega
  have habs : (2 : ℝ) ≤ |(d : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h
  have hinv : |((d : ℝ))⁻¹| ≤ 2⁻¹ := by
    rw [abs_inv]
    exact inv_anti₀ (by norm_num) habs
  nlinarith [sq_abs ((d : ℝ))⁻¹, abs_nonneg ((d : ℝ))⁻¹]

/-- The Young coefficient is the real square root of `1 - d⁻²`. -/
theorem complex_sqrt_one_sub_inv_sq {d : ℤ} (hd : d ≠ 0) :
    Complex.sqrt (1 - ((d : ℂ))⁻¹ ^ 2) = ((Real.sqrt (1 - ((d : ℝ))⁻¹ ^ 2) : ℝ) : ℂ) := by
  have hcast : ((d : ℂ))⁻¹ = (((d : ℝ))⁻¹ : ℝ) := by
    rcases d with d | d <;> simp
  have harg : (1 - ((((d : ℝ))⁻¹ : ℝ) : ℂ) ^ 2 : ℂ) = ((1 - ((d : ℝ))⁻¹ ^ 2 : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, harg, Complex.sqrt_of_nonneg (by exact_mod_cast one_sub_inv_sq_nonneg hd),
    Complex.ofReal_re]

end Coefficient

/-- The leading vector: the `T`-component of the transported reading vector. -/
noncomputable def spechtLeadingVector {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : spechtModule μ :=
  spechtLeadingCoefficient T • spechtSpectralVector T

theorem spechtLeadingVector_ne_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : spechtLeadingVector T ≠ 0 :=
  smul_ne_zero (spechtLeadingCoefficient_ne_zero T) (spechtSpectralVector_ne_zero T)

theorem spechtNorm_spechtLeadingVector_ne_zero {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) :
    ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (spechtNorm.pos (spechtLeadingVector_ne_zero T)).ne'

/-- **Young's orthogonal basis vector.** -/
noncomputable def spechtYoungBasisVector {n : ℕ} (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ) : spechtModule μ :=
  ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ • spechtLeadingVector T

theorem spechtLeadingVector_eq_smul {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) :
    spechtLeadingVector T =
      ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ) • spechtYoungBasisVector μ T := by
  rw [spechtYoungBasisVector, smul_smul, mul_inv_cancel₀
    (spechtNorm_spechtLeadingVector_ne_zero T), one_smul]

theorem spechtYoungBasisVector_eq_smul {n : ℕ} (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ) :
    spechtYoungBasisVector μ T =
      (((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ * spechtLeadingCoefficient T) •
        spechtSpectralVector T := by
  rw [spechtYoungBasisVector, spechtLeadingVector, smul_smul]

theorem one_sub_inv_sq_cast (d : ℤ) :
    (1 : ℂ) - ((d : ℂ))⁻¹ ^ 2 = ((1 - ((d : ℝ))⁻¹ ^ 2 : ℝ) : ℂ) := by
  have hcast : ((d : ℂ))⁻¹ = (((d : ℝ))⁻¹ : ℝ) := by rcases d with d | d <;> simp
  rw [hcast]
  norm_cast

/-- **Young's orthogonal form along an up-step.** The off-diagonal coefficient
is a ratio of lengths, hence the positive square root. -/
theorem rho_adjacentTransposition_spechtYoungBasisVector_of_lt
    {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (T : StandardYoungTableau μ) (i : Fin n)
    (h : T.IsAdjacentSwapStandard i) (hup : T.inversions < (T.swapAdjacent i h).inversions) :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtYoungBasisVector μ T) =
      ((T.axialDistance i : ℂ))⁻¹ • spechtYoungBasisVector μ T +
        ((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ) •
          spechtYoungBasisVector μ (T.swapAdjacent i h) := by
  classical
  obtain ⟨γ, hγ⟩ := exists_spectralSwapCorrection_eq_smul T i h
  set S := T.swapAdjacent i h with hS
  have hcS : spechtLeadingCoefficient S = spechtLeadingCoefficient T * γ :=
    spechtLeadingCoefficient_swapAdjacent T i h hup hγ
  have hstep : (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
      (spechtLeadingVector T) =
      ((T.axialDistance i : ℂ))⁻¹ • spechtLeadingVector T + spechtLeadingVector S := by
    rw [spechtLeadingVector, map_smul, rho_adjacentTransposition_spechtSpectralVector, hγ,
      spechtLeadingVector, hcS]
    module
  have hgS : spechtLeadingVector S = spechtLeadingCoefficient T • spectralSwapCorrection T i := by
    rw [spechtLeadingVector, hcS, hγ, smul_smul]
  have hformS : spechtForm (spechtLeadingVector S) (spechtLeadingVector S) =
      (1 - ((T.axialDistance i : ℂ))⁻¹ ^ 2) *
        spechtForm (spechtLeadingVector T) (spechtLeadingVector T) := by
    rw [hgS, spechtForm.smul_left, spechtForm.smul_right,
      spechtForm_spectralSwapCorrection_self, spechtLeadingVector, spechtForm.smul_left,
      spechtForm.smul_right]
    ring
  have hnormS : spechtNorm (spechtLeadingVector S) =
      Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) *
        spechtNorm (spechtLeadingVector T) := by
    have hcast : ((spechtNorm (spechtLeadingVector S) ^ 2 : ℝ) : ℂ) =
        (((1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) *
          spechtNorm (spechtLeadingVector T) ^ 2 : ℝ) : ℂ) := by
      rw [← spechtNorm.sq, hformS, one_sub_inv_sq_cast, spechtNorm.sq]
      push_cast
      ring
    have hreal : (spechtNorm (spechtLeadingVector S)) ^ 2 =
        (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) * (spechtNorm (spechtLeadingVector T)) ^ 2 := by
      exact_mod_cast hcast
    rw [← Real.sqrt_sq (spechtNorm.nonneg (spechtLeadingVector S)), hreal,
      Real.sqrt_mul (one_sub_inv_sq_nonneg (T.axialDistance_ne_zero i)),
      Real.sqrt_sq (spechtNorm.nonneg (spechtLeadingVector T))]
  have hcoef : ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ *
      ((spechtNorm (spechtLeadingVector S) : ℝ) : ℂ) =
      ((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ) := by
    have hne : ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ) ≠ 0 :=
      spechtNorm_spechtLeadingVector_ne_zero T
    rw [hnormS]
    push_cast
    field_simp
  have hvT : spechtYoungBasisVector μ T =
      ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ • spechtLeadingVector T := rfl
  calc (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtYoungBasisVector μ T)
      = ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ •
          ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
            (spechtLeadingVector T)) := by rw [hvT, map_smul]
    _ = ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ •
          (((T.axialDistance i : ℂ))⁻¹ • spechtLeadingVector T + spechtLeadingVector S) := by
        rw [hstep]
    _ = ((T.axialDistance i : ℂ))⁻¹ • spechtYoungBasisVector μ T +
          (((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ *
            ((spechtNorm (spechtLeadingVector S) : ℝ) : ℂ)) • spechtYoungBasisVector μ S := by
        rw [hvT]
        conv_lhs => rw [spechtLeadingVector_eq_smul S]
        module
    _ = _ := by rw [hcoef]

open scoped Classical in
/-- **Young's orthogonal form for the constructed basis.** -/
theorem rho_adjacentTransposition_spechtYoungBasisVector
    {n : ℕ} (μ : YoungDiagramOfSize (n + 1)) (T : StandardYoungTableau μ) (i : Fin n) :
    (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i) (spechtYoungBasisVector μ T) =
      ((T.axialDistance i : ℂ))⁻¹ • spechtYoungBasisVector μ T +
        Complex.sqrt (1 - ((T.axialDistance i : ℂ))⁻¹ ^ 2) •
          (if h : T.IsAdjacentSwapStandard i then spechtYoungBasisVector μ (T.swapAdjacent i h)
            else 0) := by
  classical
  have hvT : spechtYoungBasisVector μ T =
      ((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ • spechtLeadingVector T := rfl
  by_cases h : T.IsAdjacentSwapStandard i
  · rcases T.inversions_swapAdjacent_lt_or_lt i h with hdown | hup
    · set S := T.swapAdjacent i h with hS
      have hstdS : S.IsAdjacentSwapStandard i := T.isAdjacentSwapStandard_swapAdjacent i h
      have hback : S.swapAdjacent i hstdS = T := T.swapAdjacent_swapAdjacent i h
      have hupS : S.inversions < (S.swapAdjacent i hstdS).inversions := by
        rw [hback]; exact hdown
      have hstep := rho_adjacentTransposition_spechtYoungBasisVector_of_lt S i hstdS hupS
      have hneg : (((S.axialDistance i : ℤ)) : ℂ)⁻¹ = -(((T.axialDistance i : ℤ)) : ℂ)⁻¹ := by
        rw [T.axialDistance_swapAdjacent i h]
        push_cast
        ring
      have hsqarg : (((S.axialDistance i : ℤ)) : ℝ)⁻¹ ^ 2 =
          (((T.axialDistance i : ℤ)) : ℝ)⁻¹ ^ 2 := by
        rw [T.axialDistance_swapAdjacent i h]
        push_cast
        ring
      rw [hback, hneg, hsqarg] at hstep
      have hr2 : (((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ)) *
          (((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ)) =
          1 - ((T.axialDistance i : ℂ))⁻¹ ^ 2 := by
        rw [← Complex.ofReal_mul,
          Real.mul_self_sqrt (one_sub_inv_sq_nonneg (T.axialDistance_ne_zero i)),
          one_sub_inv_sq_cast]
      have hrne : ((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ) ≠ 0 := by
        refine Complex.ofReal_ne_zero.mpr ?_
        exact (Real.sqrt_pos.mpr (one_sub_inv_sq_pos_of_two_le
          ((T.isAdjacentSwapStandard_iff_two_le_natAbs i).mp h))).ne'
      have hinvol : (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
          ((spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
            (spechtYoungBasisVector μ S)) = spechtYoungBasisVector μ S := by
        rw [← FDRep.rho_mul_apply, adjacentTransposition_mul_self, map_one]
        rfl
      rw [hstep, map_add, map_smul, map_smul, hstep] at hinvol
      have hrX := eq_sub_of_add_eq' hinvol
      rw [dif_pos h, complex_sqrt_one_sub_inv_sq (T.axialDistance_ne_zero i)]
      refine smul_right_injective _ hrne ?_
      show ((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ) • _ =
        ((Real.sqrt (1 - ((T.axialDistance i : ℤ) : ℝ)⁻¹ ^ 2) : ℝ) : ℂ) • _
      rw [hrX]
      match_scalars
      · linear_combination -hr2
      · ring
    · rw [dif_pos h, complex_sqrt_one_sub_inv_sq (T.axialDistance_ne_zero i)]
      exact rho_adjacentTransposition_spechtYoungBasisVector_of_lt T i h hup
  · rw [dif_neg h, smul_zero, add_zero]
    have hstep : (spechtModule μ).ρ (SymmetricGroup.adjacentTransposition i)
        (spechtLeadingVector T) = ((T.axialDistance i : ℂ))⁻¹ • spechtLeadingVector T := by
      rw [spechtLeadingVector, map_smul, rho_adjacentTransposition_spechtSpectralVector,
        spectralSwapCorrection_eq_zero T i h, add_zero, smul_smul, smul_smul, mul_comm]
    rw [hvT, map_smul, hstep]
    module

/-- The unit rescaling the spectral basis to Young's orthogonal basis. -/
noncomputable def spechtYoungUnit {n : ℕ} {μ : YoungDiagramOfSize n}
    (T : StandardYoungTableau μ) : ℂˣ :=
  Units.mk0 (((spechtNorm (spechtLeadingVector T) : ℝ) : ℂ)⁻¹ * spechtLeadingCoefficient T)
    (mul_ne_zero (inv_ne_zero (spechtNorm_spechtLeadingVector_ne_zero T))
      (spechtLeadingCoefficient_ne_zero T))

/-- **Young's orthogonal basis of a Specht module.** -/
noncomputable def spechtYoungBasis {n : ℕ} (μ : YoungDiagramOfSize n) :
    Module.Basis (StandardYoungTableau μ) ℂ (spechtModule μ) :=
  (spechtSpectralBasis μ).unitsSMul spechtYoungUnit

@[simp]
theorem spechtYoungBasis_apply {n : ℕ} (μ : YoungDiagramOfSize n)
    (T : StandardYoungTableau μ) : spechtYoungBasis μ T = spechtYoungBasisVector μ T := by
  rw [spechtYoungBasis, Module.Basis.unitsSMul_apply, spechtSpectralBasis_apply,
    spechtYoungBasisVector_eq_smul, spechtYoungUnit]
  rfl
