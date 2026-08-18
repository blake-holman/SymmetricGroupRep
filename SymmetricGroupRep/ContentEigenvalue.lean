import SymmetricGroupRep.TableauContent

/-! # The class sum acts on a Specht module by the content sum

Schur's lemma makes the class sum of the transpositions a scalar on `S^μ`. The
scalar is computed by applying it to a polytabloid and reading off the
coefficient at the underlying tabloid: a transposition contributes `1` when its
two labels share a row of the tableau, `-1` when they share a column, and `0`
otherwise. Counting those pairs gives `∑ (column - row)` over the cells.

Combined with the splitting of the class sum, this identifies the eigenvalue of
the last Jucys–Murphy operator on a branching summand as the content of the
removed cell.
-/

open CategoryTheory

/-- The class sum as an endomorphism of a representation. -/
noncomputable def classSumHom {n : ℕ} (V : SymmetricGroupRepresentation n) : V ⟶ V where
  hom := FGModuleCat.ofHom (classSum V)
  comm g := by
    ext v
    show classSum V (V.ρ g v) = V.ρ g (classSum V v)
    exact classSum_comm V g v

theorem exists_classSum_spechtModule_eq_smul {n : ℕ} (μ : YoungDiagramOfSize n) :
    ∃ c : ℂ, ∀ v : spechtModule μ, classSum (spechtModule μ) v = c • v := by
  obtain ⟨c, hc⟩ := spechtEndomorphism_eq_smul_id μ (classSumHom (spechtModule μ))
  refine ⟨c, fun v => ?_⟩
  have h := congrArg (fun f : spechtModule μ ⟶ spechtModule μ => f.hom.hom.hom v) hc
  change classSum (spechtModule μ) v = c • v at h
  exact h

/-- The scalar by which the sum of the transpositions acts on `S^μ`. -/
noncomputable def transpositionScalar {n : ℕ} (μ : YoungDiagramOfSize n) : ℂ :=
  Classical.choose (exists_classSum_spechtModule_eq_smul μ)

theorem classSum_spechtModule {n : ℕ} (μ : YoungDiagramOfSize n) (v : spechtModule μ) :
    classSum (spechtModule μ) v = transpositionScalar μ • v :=
  Classical.choose_spec (exists_classSum_spechtModule_eq_smul μ) v

/-- **Sagan's Corollary 2.4.3 for a transposition.** Moving a polytabloid by a
transposition changes its coefficient at the original tabloid by `1` when the
two labels share a row, by `-1` when they share a column, and not at all
otherwise. -/
theorem polytabloid_swap_apply_tabloid {n : ℕ} {μ : YoungDiagramOfSize n}
    (t : YoungTableau μ) {a b : Fin n} (hab : a ≠ b) :
    (YoungTableau.polytabloid (Equiv.swap a b • t)).coeff t.tabloid =
      (if t.row a = t.row b then 1 else 0) - (if t.column a = t.column b then 1 else 0) := by
  classical
  have hexpand : (YoungTableau.polytabloid (Equiv.swap a b • t)).coeff t.tabloid =
      ∑ τ : t.columnGroup, ((Equiv.Perm.sign (τ : SymmetricGroup n) : ℤ) : ℂ) *
        (if (Equiv.swap a b * (τ : SymmetricGroup n)) • t.tabloid = t.tabloid then 1 else 0) := by
    rw [← YoungTableau.smul_polytabloid, YoungTableau.polytabloid, map_sum,
      MonoidAlgebra.coeff_sum, Finset.sum_apply']
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_smul, Representation.ofMulAction_single, ← mul_smul,
      MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      smul_eq_mul]
  rw [hexpand]
  by_cases hrow : t.row a = t.row b
  · have hcol : t.column a ≠ t.column b := fun h =>
      hab (t.row_column_injective (Prod.ext hrow h))
    have hfix : (Equiv.swap a b) • t.tabloid = t.tabloid := by
      apply Tabloid.ext
      funext i
      rw [Tabloid.smul_rowOf, Equiv.swap_inv]
      rcases eq_or_ne i a with rfl | hia
      · exact Fin.ext (by rw [Equiv.swap_apply_left]; exact hrow.symm)
      · rcases eq_or_ne i b with rfl | hib
        · exact Fin.ext (by rw [Equiv.swap_apply_right]; exact hrow)
        · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
    rw [if_pos hrow, if_neg hcol]
    rw [Finset.sum_eq_single (1 : t.columnGroup)]
    · simp [hfix]
    · intro τ _ hne
      have hzero : ¬ ((Equiv.swap a b * (τ : SymmetricGroup n)) • t.tabloid = t.tabloid) := by
        intro heq
        exact hne (Subtype.ext (YoungTableau.eq_one_of_mem_columnGroup_of_smul_tabloid_eq τ.2
          (MulAction.injective (Equiv.swap a b)
            (((mul_smul (Equiv.swap a b) (τ : SymmetricGroup n) t.tabloid) ▸ heq).trans
              hfix.symm))))
      simp [hzero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · by_cases hcol : t.column a = t.column b
    · have hmem : Equiv.swap a b ∈ t.columnGroup := by
        intro i
        rcases eq_or_ne i a with rfl | hia
        · rw [Equiv.swap_apply_left]; exact hcol.symm
        · rcases eq_or_ne i b with rfl | hib
          · rw [Equiv.swap_apply_right]; exact hcol
          · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      rw [if_neg hrow, if_pos hcol]
      rw [Finset.sum_eq_single (⟨Equiv.swap a b, hmem⟩ : t.columnGroup)]
      · simp [Equiv.Perm.sign_swap hab, Equiv.swap_mul_self]
      · intro τ _ hne
        have hzero : ¬ ((Equiv.swap a b * (τ : SymmetricGroup n)) • t.tabloid = t.tabloid) := by
          intro heq
          have hprod : Equiv.swap a b * (τ : SymmetricGroup n) ∈ t.columnGroup :=
            t.columnGroup.mul_mem hmem τ.2
          have hone := YoungTableau.eq_one_of_mem_columnGroup_of_smul_tabloid_eq hprod heq
          refine hne (Subtype.ext ?_)
          rw [← Equiv.swap_mul_self a b] at hone
          exact mul_left_cancel hone
        simp [hzero]
      · intro hmem'
        exact absurd (Finset.mem_univ _) hmem'
    · rw [if_neg hrow, if_neg hcol, sub_zero]
      refine Finset.sum_eq_zero fun τ _ => ?_
      have hzero : ¬ ((Equiv.swap a b * (τ : SymmetricGroup n)) • t.tabloid = t.tabloid) := by
        intro heq
        have hrows : ∀ i, t.row ((Equiv.swap a b * (τ : SymmetricGroup n)) i) = t.row i := by
          intro i
          have := congrArg (fun T : Tabloid μ =>
            (T.rowOf ((Equiv.swap a b * (τ : SymmetricGroup n)) i) : ℕ)) heq
          simpa using this.symm
        rcases eq_or_ne ((τ : SymmetricGroup n) a) a with hx | hxa
        · have := hrows a
          rw [Equiv.Perm.mul_apply, hx, Equiv.swap_apply_left] at this
          exact hrow this.symm
        · rcases eq_or_ne ((τ : SymmetricGroup n) a) b with hx | hxb
          · exact hcol (by rw [← τ.2 a, hx])
          · have hfix : Equiv.swap a b ((τ : SymmetricGroup n) a) = (τ : SymmetricGroup n) a :=
              Equiv.swap_apply_of_ne_of_ne hxa hxb
            have hr := hrows a
            rw [Equiv.Perm.mul_apply, hfix] at hr
            exact hxa (t.row_column_injective (Prod.ext hr (τ.2 a)))
      simp [hzero]

/-- Reading the class-sum scalar off the polytabloid of a tableau. -/
theorem transpositionScalar_eq_sum {n : ℕ} (μ : YoungDiagramOfSize n) (t : YoungTableau μ) :
    transpositionScalar μ =
      ∑ p ∈ transpositionPairs n,
        ((if t.row p.1 = t.row p.2 then 1 else 0) -
          (if t.column p.1 = t.column p.2 then 1 else 0)) := by
  classical
  set incl : spechtModule μ →ₗ[ℂ] MonoidAlgebra ℂ (Tabloid μ) :=
    (spechtSubrepresentation μ).toSubmodule.subtype with hincl
  set e : spechtModule μ := (⟨YoungTableau.polytabloid t, Submodule.subset_span ⟨t, rfl⟩⟩ :
    ↥(spechtSubrepresentation μ).toSubmodule) with hedef
  have hleft : (incl (classSum (spechtModule μ) e)).coeff t.tabloid =
      transpositionScalar μ := by
    rw [classSum_spechtModule, map_smul]
    change transpositionScalar μ * (YoungTableau.polytabloid t).coeff t.tabloid = _
    rw [YoungTableau.polytabloid_apply_tabloid, mul_one]
  rw [← hleft, classSum_apply, map_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun p hp => ?_
  have hne : p.1 ≠ p.2 := (mem_transpositionPairs.mp hp).ne
  rw [← polytabloid_swap_apply_tabloid t hne, ← YoungTableau.smul_polytabloid]
  rfl

section Counting

variable {n : ℕ} (μ : YoungDiagramOfSize n) (R : StandardYoungTableau μ)

/-- Pairs of labels sharing a row are counted by the columns of the cells. -/
theorem card_transpositionPairs_row_eq :
    ((transpositionPairs n).filter fun p =>
        YoungTableau.row R.entry p.1 = YoungTableau.row R.entry p.2).card =
      ∑ c ∈ μ.val.cells, c.2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p => (YoungTableau.row R.entry p.2, YoungTableau.column R.entry p.2))
    (t := μ.val.cells) fun p _ => YoungTableau.mem_cells R.entry p.2]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [← Finset.card_range c.2]
  refine Finset.card_bij (fun p _ => YoungTableau.column R.entry p.1) (fun p hp => ?_)
    (fun p hp q hq h => ?_) (fun k hk => ?_)
  · simp only [Finset.mem_filter, mem_transpositionPairs] at hp
    show YoungTableau.column R.entry p.1 ∈ Finset.range c.2
    refine Finset.mem_range.mpr ?_
    have hlt := R.column_lt_column_of_row_eq hp.1.2 hp.1.1
    have hcol : YoungTableau.column R.entry p.2 = c.2 := congrArg Prod.snd hp.2
    rwa [hcol] at hlt
  · simp only [Finset.mem_filter, mem_transpositionPairs] at hp hq
    have hsecond : p.2 = q.2 := YoungTableau.row_column_injective R.entry (hp.2.trans hq.2.symm)
    have hrows : YoungTableau.row R.entry p.1 = YoungTableau.row R.entry q.1 :=
      hp.1.2.trans ((congrArg Prod.fst hp.2).trans
        ((congrArg Prod.fst hq.2).symm.trans hq.1.2.symm))
    exact Prod.ext (YoungTableau.row_column_injective R.entry (Prod.ext hrows h)) hsecond
  · rw [Finset.mem_range] at hk
    have hcell : (c.1, k) ∈ μ.val.cells :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (hk.trans (YoungDiagram.mem_iff_lt_rowLen.mp hc))
    refine ⟨(R.entry ⟨(c.1, k), hcell⟩, R.entry ⟨c, hc⟩), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨mem_transpositionPairs.mpr ?_, ?_⟩, ?_⟩
      · exact R.lt_of_row_eq_of_column_lt (by simp) (by simpa using hk)
      · simp
      · simp
    · show YoungTableau.column R.entry (R.entry ⟨(c.1, k), hcell⟩) = k
      simp

/-- Pairs of labels sharing a column are counted by the rows of the cells. -/
theorem card_transpositionPairs_column_eq :
    ((transpositionPairs n).filter fun p =>
        YoungTableau.column R.entry p.1 = YoungTableau.column R.entry p.2).card =
      ∑ c ∈ μ.val.cells, c.1 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p => (YoungTableau.row R.entry p.2, YoungTableau.column R.entry p.2))
    (t := μ.val.cells) fun p _ => YoungTableau.mem_cells R.entry p.2]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [← Finset.card_range c.1]
  refine Finset.card_bij (fun p _ => YoungTableau.row R.entry p.1) (fun p hp => ?_)
    (fun p hp q hq h => ?_) (fun k hk => ?_)
  · simp only [Finset.mem_filter, mem_transpositionPairs] at hp
    show YoungTableau.row R.entry p.1 ∈ Finset.range c.1
    refine Finset.mem_range.mpr ?_
    have hlt := R.row_lt_row_of_column_eq hp.1.2 hp.1.1
    have hrow : YoungTableau.row R.entry p.2 = c.1 := congrArg Prod.fst hp.2
    rwa [hrow] at hlt
  · simp only [Finset.mem_filter, mem_transpositionPairs] at hp hq
    have hsecond : p.2 = q.2 := YoungTableau.row_column_injective R.entry (hp.2.trans hq.2.symm)
    have hcols : YoungTableau.column R.entry p.1 = YoungTableau.column R.entry q.1 :=
      hp.1.2.trans ((congrArg Prod.snd hp.2).trans
        ((congrArg Prod.snd hq.2).symm.trans hq.1.2.symm))
    exact Prod.ext (YoungTableau.row_column_injective R.entry (Prod.ext h hcols)) hsecond
  · rw [Finset.mem_range] at hk
    have hcell : (k, c.2) ∈ μ.val.cells := μ.val.up_left_mem hk.le le_rfl hc
    refine ⟨(R.entry ⟨(k, c.2), hcell⟩, R.entry ⟨c, hc⟩), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨mem_transpositionPairs.mpr ?_, ?_⟩, ?_⟩
      · exact R.lt_of_column_eq_of_row_lt (by simp) (by simpa using hk)
      · simp
      · simp
    · show YoungTableau.row R.entry (R.entry ⟨(k, c.2), hcell⟩) = k
      simp

end Counting

/-- **The class-sum scalar is the content sum.** -/
theorem transpositionScalar_eq_contentSum {n : ℕ} (μ : YoungDiagramOfSize n) :
    transpositionScalar μ = (contentSum μ : ℂ) := by
  classical
  set R := readingTableau μ with hR
  have hsplit : (∑ c ∈ μ.val.cells, YoungDiagram.cellContent c) =
      (∑ c ∈ μ.val.cells, ((c.2 : ℤ))) - ∑ c ∈ μ.val.cells, ((c.1 : ℤ)) :=
    Finset.sum_sub_distrib (fun c : ℕ × ℕ => ((c.2 : ℤ))) (fun c : ℕ × ℕ => ((c.1 : ℤ)))
  rw [transpositionScalar_eq_sum μ R.entry, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole, card_transpositionPairs_row_eq μ R,
    card_transpositionPairs_column_eq μ R, contentSum, hsplit]
  push_cast
  ring

/-- The class sum of the smaller group is scalar on the image of `S^ν`. -/
theorem restrictedClassSum_spechtModule_hom {n : ℕ} {μ : YoungDiagramOfSize (n + 1)}
    {ν : YoungDiagramOfSize n}
    (f : spechtModule ν ⟶ (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ))
    (v : spechtModule ν) :
    restrictedClassSum (spechtModule μ) (f.hom.hom.hom v) =
      transpositionScalar ν • f.hom.hom.hom v := by
  rw [restrictedClassSum_hom_apply, classSum_spechtModule, map_smul]

/-- **The last Jucys–Murphy operator on a branching summand.** It is the content
of the removed cell, because the class sum contributes the content sum of each
shape and the two differ by that cell. -/
theorem jucysMurphy_last_hom {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (ν : OneBoxRemoval μ)
    (f : spechtModule ν.val ⟶
      (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ))
    (v : spechtModule ν.val) :
    jucysMurphy (spechtModule μ) (Fin.last n) (f.hom.hom.hom v) =
      (ν.cellContent : ℂ) • f.hom.hom.hom v := by
  have hsplit := classSum_eq_restricted_add_jucysMurphy_last (spechtModule μ) (f.hom.hom.hom v)
  rw [classSum_spechtModule, restrictedClassSum_spechtModule_hom] at hsplit
  have hscalar : (ν.cellContent : ℂ) = transpositionScalar μ - transpositionScalar ν.val := by
    rw [transpositionScalar_eq_contentSum, transpositionScalar_eq_contentSum,
      ← Int.cast_sub, contentSum_sub_contentSum]
  rw [hscalar, sub_smul]
  exact eq_sub_of_add_eq ((add_comm _ _).trans hsplit.symm)
