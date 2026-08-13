import SymmetricGroupRep.SchurKostka

/-! # Inverting the Kostka matrix

The Kostka matrix in a fixed size is unitriangular for the dominance order:
its diagonal is one and it vanishes off dominance.  Well-founded recursion on
strict dominance therefore produces an integer inverse column for each shape,
and convolving with it recovers individual coefficients from Kostka-weighted
sums.
-/

/-- Each Kostka column has an integral inverse: a vector pairing to `1` with
its own shape and to `0` with every other. -/
theorem exists_kostka_inverse {n : ℕ} (μ : YoungDiagramOfSize n) :
    ∃ z : YoungDiagramOfSize n → ℤ, ∀ lam : YoungDiagramOfSize n,
      ∑ α : YoungDiagramOfSize n, z α * (kostkaNumber lam α : ℤ) =
        if lam = μ then 1 else 0 := by
  classical
  set r : YoungDiagramOfSize n → YoungDiagramOfSize n → Prop :=
    fun α lam => α ≠ lam ∧ lam.val.Dominates α.val with hr
  have hwf : WellFounded r := by
    haveI : IsTrans (YoungDiagramOfSize n) r := ⟨by
      rintro x y z ⟨hxy, hyx⟩ ⟨hyz, hzy⟩
      refine ⟨fun hxz => ?_, fun j => (hyx j).trans (hzy j)⟩
      subst hxz
      exact hyz (Subtype.ext (YoungDiagram.Dominates.antisymm hyx hzy))⟩
    haveI : Std.Irrefl r := ⟨fun x hx => hx.1 rfl⟩
    exact Finite.wellFounded_of_trans_of_irrefl r
  set F : ∀ lam : YoungDiagramOfSize n,
      (∀ α, r α lam → ℤ) → ℤ := fun lam ih =>
    (if lam = μ then 1 else 0) -
      ∑ α ∈ (Finset.univ.filter fun α => r α lam).attach,
        ih α.1 (Finset.mem_filter.mp α.2).2 * (kostkaNumber lam α.1 : ℤ) with hF
  refine ⟨hwf.fix F, fun lam => ?_⟩
  have hzeq : hwf.fix F lam = (if lam = μ then 1 else 0) -
      ∑ α ∈ Finset.univ.filter (fun α => r α lam),
        hwf.fix F α * (kostkaNumber lam α : ℤ) := by
    rw [WellFounded.fix_eq]
    show (if lam = μ then 1 else 0) -
        ∑ α ∈ (Finset.univ.filter fun α => r α lam).attach,
          hwf.fix F α.1 * (kostkaNumber lam α.1 : ℤ) = _
    congr 1
    exact Finset.sum_attach (Finset.univ.filter fun α => r α lam)
      (fun α => hwf.fix F α * (kostkaNumber lam α : ℤ))
  have herase : ∑ α ∈ Finset.univ.filter (fun α => r α lam),
      hwf.fix F α * (kostkaNumber lam α : ℤ) =
      ∑ α ∈ Finset.univ.erase lam, hwf.fix F α * (kostkaNumber lam α : ℤ) := by
    refine Finset.sum_subset ?_ ?_
    · intro α hα
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hα).2.1, Finset.mem_univ α⟩
    · intro α hα hnot
      have hndom : ¬ lam.val.Dominates α.val := fun hdom =>
        hnot (Finset.mem_filter.mpr
          ⟨Finset.mem_univ α, (Finset.mem_erase.mp hα).1, hdom⟩)
      rw [kostkaNumber_eq_zero_of_not_dominates hndom]
      simp
  calc ∑ α : YoungDiagramOfSize n, hwf.fix F α * (kostkaNumber lam α : ℤ)
      = hwf.fix F lam * (kostkaNumber lam lam : ℤ) +
          ∑ α ∈ Finset.univ.erase lam, hwf.fix F α * (kostkaNumber lam α : ℤ) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ lam)).symm
    _ = hwf.fix F lam +
          ∑ α ∈ Finset.univ.filter (fun α => r α lam),
            hwf.fix F α * (kostkaNumber lam α : ℤ) := by
        rw [kostkaNumber_self, ← herase]
        push_cast
        ring
    _ = (if lam = μ then 1 else 0) := by
        rw [hzeq]
        ring

/-- Recover a coefficient from a Kostka-weighted sum: a vector convolving to
zero against every Kostka column is zero. -/
theorem kostka_convolution_cancel {n : ℕ} (c : YoungDiagramOfSize n → ℤ)
    (h : ∀ α : YoungDiagramOfSize n,
      ∑ μ : YoungDiagramOfSize n, (kostkaNumber μ α : ℤ) * c μ = 0)
    (μ₀ : YoungDiagramOfSize n) : c μ₀ = 0 := by
  classical
  obtain ⟨z, hz⟩ := exists_kostka_inverse μ₀
  have hkey : ∑ α : YoungDiagramOfSize n,
      z α * ∑ μ : YoungDiagramOfSize n, (kostkaNumber μ α : ℤ) * c μ = 0 := by
    simp [h]
  rw [show ∑ α : YoungDiagramOfSize n,
        z α * ∑ μ : YoungDiagramOfSize n, (kostkaNumber μ α : ℤ) * c μ =
      ∑ μ : YoungDiagramOfSize n,
        (∑ α : YoungDiagramOfSize n, z α * (kostkaNumber μ α : ℤ)) * c μ by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ => by ring]
    at hkey
  simp only [hz, ite_mul, one_mul, zero_mul] at hkey
  rwa [Finset.sum_ite_eq' Finset.univ μ₀ c, if_pos (Finset.mem_univ μ₀)] at hkey
