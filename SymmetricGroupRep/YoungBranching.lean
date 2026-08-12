import SymmetricGroupRep.YoungBasis

/-! # The branching isomorphism carried by Young's orthogonal basis

Writing the largest label back into the cell a one-box removal deletes carries
Young's orthogonal basis of `S^ν` into part of the one of `S^μ`. Young's
formula for an adjacent transposition is the same on both sides, because the
axial distance, the standardness of the swap and the swap itself are all
unchanged by that extension, so the resulting linear map is equivariant. The
maps assembled over all removals form an isomorphism, since Schur's lemma makes
the composite with any branching isomorphism diagonal with nonzero entries.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

section Embedding

variable {n : ℕ} {μ : YoungDiagramOfSize (n + 1)} (ν : OneBoxRemoval μ)

/-- Extending tableaux carries Young's orthogonal basis of `S^ν` into `S^μ`. -/
noncomputable def spechtBranchingMap : (spechtModule ν.val).V →ₗ[ℂ] (spechtModule μ).V :=
  (spechtYoungBasis ν.val).constr ℂ fun T' =>
    spechtYoungBasisVector μ (OneBoxRemoval.extend ν T')

@[simp]
theorem spechtBranchingMap_apply (T' : StandardYoungTableau ν.val) :
    spechtBranchingMap ν (spechtYoungBasisVector ν.val T') =
      spechtYoungBasisVector μ (OneBoxRemoval.extend ν T') := by
  rw [← spechtYoungBasis_apply, spechtBranchingMap, Module.Basis.constr_basis]

open scoped Classical in
theorem spechtBranchingMap_equivariant (g : SymmetricGroup n) (x : spechtModule ν.val) :
    spechtBranchingMap ν ((spechtModule ν.val).ρ g x) =
      (spechtModule μ).ρ (SymmetricGroup.inclusion n g) (spechtBranchingMap ν x) := by
  cases n with
  | zero =>
    have hg : g = 1 := Subsingleton.elim g 1
    subst hg
    simp
  | succ m =>
    have hstep : ∀ h : SymmetricGroup (m + 1),
        h ∈ Submonoid.closure (Set.range fun j : Fin m =>
          SymmetricGroup.adjacentTransposition j) →
        ∀ y, spechtBranchingMap ν ((spechtModule ν.val).ρ h y) =
          (spechtModule μ).ρ (SymmetricGroup.inclusion (m + 1) h) (spechtBranchingMap ν y) := by
      intro h hh
      induction hh using Submonoid.closure_induction with
      | mem z hz =>
          obtain ⟨j, rfl⟩ := hz
          have hmaps : (spechtBranchingMap ν).comp
              ((spechtModule ν.val).ρ (SymmetricGroup.adjacentTransposition j)) =
            ((spechtModule μ).ρ (SymmetricGroup.inclusion (m + 1)
              (SymmetricGroup.adjacentTransposition j))).comp (spechtBranchingMap ν) := by
            refine (spechtYoungBasis ν.val).ext fun T' => ?_
            rw [LinearMap.comp_apply, LinearMap.comp_apply, spechtYoungBasis_apply,
              rho_adjacentTransposition_spechtYoungBasisVector ν.val T' j,
              SymmetricGroup.inclusion_adjacentTransposition, map_add, map_smul, map_smul,
              spechtBranchingMap_apply,
              rho_adjacentTransposition_spechtYoungBasisVector μ
                (OneBoxRemoval.extend ν T') (Fin.castSucc j),
              OneBoxRemoval.axialDistance_extend ν T' j]
            by_cases hstd : T'.IsAdjacentSwapStandard j
            · rw [dif_pos hstd, dif_pos ((OneBoxRemoval.isAdjacentSwapStandard_extend ν T' j).mpr
                hstd), spechtBranchingMap_apply, OneBoxRemoval.extend_swapAdjacent ν T' j hstd]
            · rw [dif_neg hstd, dif_neg (fun hcontra => hstd
                ((OneBoxRemoval.isAdjacentSwapStandard_extend ν T' j).mp hcontra)), map_zero]
          exact fun y => LinearMap.congr_fun hmaps y
      | one => intro y; simp
      | mul a b _ _ ha hb =>
          intro y
          rw [FDRep.rho_mul_apply, ha, hb, map_mul, FDRep.rho_mul_apply]
    have hgen : Submonoid.closure (Set.range fun j : Fin m =>
        SymmetricGroup.adjacentTransposition j) = ⊤ :=
      Equiv.Perm.mclosure_swap_castSucc_succ m
    exact hstep g (by rw [hgen]; exact Submonoid.mem_top g) x

/-- Extending tableaux as a morphism of representations of the smaller group. -/
noncomputable def spechtBranchingEmbedding :
    spechtModule ν.val ⟶ (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) where
  hom := FGModuleCat.ofHom (spechtBranchingMap ν)
  comm g := by
    ext x
    show spechtBranchingMap ν ((spechtModule ν.val).ρ g x) =
      (spechtModule μ).ρ (SymmetricGroup.inclusion n g) (spechtBranchingMap ν x)
    exact spechtBranchingMap_equivariant ν g x

@[simp]
theorem spechtBranchingEmbedding_apply (T' : StandardYoungTableau ν.val) :
    (spechtBranchingEmbedding ν).hom.hom.hom (spechtYoungBasisVector ν.val T') =
      spechtYoungBasisVector μ (OneBoxRemoval.extend ν T') :=
  spechtBranchingMap_apply ν T'

theorem spechtBranchingEmbedding_ne_zero : spechtBranchingEmbedding ν ≠ 0 := by
  intro hzero
  have happly : spechtYoungBasisVector μ (OneBoxRemoval.extend ν (readingTableau ν.val)) = 0 := by
    rw [← spechtBranchingEmbedding_apply ν (readingTableau ν.val), hzero]
    show (0 : (spechtModule ν.val).V →ₗ[ℂ] (spechtModule μ).V)
      (spechtYoungBasisVector ν.val (readingTableau ν.val)) = 0
    rw [LinearMap.zero_apply]
  refine (spechtYoungBasis μ).ne_zero (OneBoxRemoval.extend ν (readingTableau ν.val)) ?_
  rw [spechtYoungBasis_apply]
  exact happly

end Embedding

section BranchingIso

/-- A biproduct endomorphism with nonzero scalars on the diagonal and nothing
off it is invertible. -/
private theorem isIso_of_biproduct_diagonal {m : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (F : J → SymmetricGroupRepresentation m) (Θ : (⨁ F) ⟶ (⨁ F)) (c : J → ℂ)
    (hdiag : ∀ j, (biproduct.ι F j ≫ Θ) ≫ biproduct.π F j = c j • 𝟙 (F j))
    (hoff : ∀ j k, j ≠ k → (biproduct.ι F j ≫ Θ) ≫ biproduct.π F k = 0)
    (hcne : ∀ j, c j ≠ 0) : IsIso Θ := by
  have hiso : ∀ j, IsIso (c j • 𝟙 (F j)) := fun j =>
    ⟨(c j)⁻¹ • 𝟙 (F j),
      by simp [Linear.comp_smul, smul_smul, inv_mul_cancel₀ (hcne j)],
      by simp [Linear.comp_smul, smul_smul, mul_inv_cancel₀ (hcne j)]⟩
  have heq : Θ = biproduct.map fun j => c j • 𝟙 (F j) := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    refine biproduct.hom_ext _ _ fun k => ?_
    rw [Category.assoc, Category.assoc, biproduct.map_π, ← Category.assoc, ← Category.assoc]
    by_cases hjk : j = k
    · subst hjk
      rw [biproduct.ι_π_self, hdiag j, Category.id_comp]
    · rw [hoff j k hjk, biproduct.ι_π_ne _ hjk, zero_comp]
  have hmap : biproduct.map (fun j => c j • 𝟙 (F j)) =
      (biproduct.mapIso fun j => @asIso _ _ _ _ (c j • 𝟙 (F j)) (hiso j)).hom := rfl
  rw [heq, hmap]
  infer_instance

variable {n : ℕ} (μ : YoungDiagramOfSize (n + 1))

/-- The extension maps, assembled over all one-box removals. -/
noncomputable def spechtBranchingDesc :
    (⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val) ⟶
      (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) :=
  biproduct.desc fun ν : OneBoxRemoval μ => spechtBranchingEmbedding ν

theorem biproduct_ι_spechtBranchingDesc (ν : OneBoxRemoval μ) :
    biproduct.ι (fun ξ : OneBoxRemoval μ => spechtModule ξ.val) ν ≫ spechtBranchingDesc μ =
      spechtBranchingEmbedding ν :=
  biproduct.ι_desc _ _

/-- **The assembled extension maps form an isomorphism.** Composing with any
branching isomorphism gives a diagonal endomorphism of the biproduct with
nonzero entries, by Schur's lemma. -/
theorem isIso_spechtBranchingDesc : IsIso (spechtBranchingDesc μ) := by
  classical
  letI : Fintype (OneBoxRemoval μ) := Fintype.ofFinite _
  obtain ⟨e⟩ := spechtModule_branching μ
  have hcomp : ∀ ν : OneBoxRemoval μ,
      biproduct.ι (fun ξ : OneBoxRemoval μ => spechtModule ξ.val) ν ≫
          (spechtBranchingDesc μ ≫ e.hom) =
        spechtBranchingEmbedding ν ≫ e.hom := by
    intro ν
    rw [← Category.assoc, biproduct_ι_spechtBranchingDesc]
  have hoff : ∀ ν ξ : OneBoxRemoval μ, ν ≠ ξ →
      (biproduct.ι (fun ζ : OneBoxRemoval μ => spechtModule ζ.val) ν ≫
          (spechtBranchingDesc μ ≫ e.hom)) ≫
        biproduct.π (fun ζ : OneBoxRemoval μ => spechtModule ζ.val) ξ = 0 := by
    intro ν ξ hne
    exact spechtHom_eq_zero_of_ne (fun hcontra => hne (Subtype.ext hcontra)) _
  have hdiag : ∀ ν : OneBoxRemoval μ, ∃ c : ℂ,
      (biproduct.ι (fun ζ : OneBoxRemoval μ => spechtModule ζ.val) ν ≫
          (spechtBranchingDesc μ ≫ e.hom)) ≫
        biproduct.π (fun ζ : OneBoxRemoval μ => spechtModule ζ.val) ν =
          c • 𝟙 (spechtModule ν.val) :=
    fun ν => spechtEndomorphism_eq_smul_id ν.val _
  choose c hc using hdiag
  have hcne : ∀ ν, c ν ≠ 0 := by
    intro ν hzero
    have hvanish : biproduct.ι (fun ζ : OneBoxRemoval μ => spechtModule ζ.val) ν ≫
        (spechtBranchingDesc μ ≫ e.hom) = 0 := by
      refine biproduct.hom_ext _ _ fun ξ => ?_
      rw [zero_comp]
      by_cases hne : ν = ξ
      · subst hne
        rw [hc ν, hzero, zero_smul]
      · exact hoff ν ξ hne
    rw [hcomp ν] at hvanish
    refine spechtBranchingEmbedding_ne_zero ν ?_
    calc spechtBranchingEmbedding ν = (spechtBranchingEmbedding ν ≫ e.hom) ≫ e.inv := by simp
      _ = 0 := by rw [hvanish, zero_comp]
  have hΘ : IsIso (spechtBranchingDesc μ ≫ e.hom) :=
    isIso_of_biproduct_diagonal _ _ c hc (fun ν ξ => hoff ν ξ) hcne
  have hdescr : spechtBranchingDesc μ = (spechtBranchingDesc μ ≫ e.hom) ≫ e.inv := by
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [hdescr]
  infer_instance

end BranchingIso

section Coherence

variable {n : ℕ} (μ : YoungDiagramOfSize (n + 1))

private theorem hom_comp_apply {m : ℕ} {A B C : SymmetricGroupRepresentation m} (f : A ⟶ B)
    (g : B ⟶ C) (x : A.V) : (f ≫ g).hom.hom.hom x = g.hom.hom.hom (f.hom.hom.hom x) := rfl

/-- **The branching isomorphism carried by Young's orthogonal basis.** -/
noncomputable def spechtYoungBranchingIso :
    (SymmetricGroupRepresentation.restriction n).obj (spechtModule μ) ≅
      ⨁ fun ν : OneBoxRemoval μ => spechtModule ν.val :=
  letI := isIso_spechtBranchingDesc μ
  (asIso (spechtBranchingDesc μ)).symm

/-- Deleting the largest label selects the corresponding branching summand. -/
theorem spechtYoungBranchingIso_basis (T : StandardYoungTableau μ) :
    FDRep.isoToLinearEquiv (spechtYoungBranchingIso μ) (spechtYoungBasis μ T) =
      (biproduct.ι (fun ν : OneBoxRemoval μ => spechtModule ν.val)
          T.largestRemoval).hom.hom.hom
        (spechtYoungBasis T.largestRemoval.val T.restrictLargest) := by
  letI := isIso_spechtBranchingDesc μ
  have hdesc : (spechtBranchingDesc μ).hom.hom.hom
      ((biproduct.ι (fun ν : OneBoxRemoval μ => spechtModule ν.val)
          T.largestRemoval).hom.hom.hom
        (spechtYoungBasisVector T.largestRemoval.val T.restrictLargest)) =
      spechtYoungBasisVector μ T := by
    have happ : (biproduct.ι (fun ξ : OneBoxRemoval μ => spechtModule ξ.val)
          T.largestRemoval ≫ spechtBranchingDesc μ).hom.hom.hom
        (spechtYoungBasisVector T.largestRemoval.val T.restrictLargest) =
      (spechtBranchingEmbedding T.largestRemoval).hom.hom.hom
        (spechtYoungBasisVector T.largestRemoval.val T.restrictLargest) := by
      rw [biproduct_ι_spechtBranchingDesc]
    rw [hom_comp_apply] at happ
    rw [happ, spechtBranchingEmbedding_apply, OneBoxRemoval.extend_restrictLargest]
  have hleft : ∀ z, (spechtBranchingDesc μ).hom.hom.hom
      (FDRep.isoToLinearEquiv (spechtYoungBranchingIso μ) z) = z := by
    intro z
    have hiso : FDRep.isoToLinearEquiv (spechtYoungBranchingIso μ) z =
        (inv (spechtBranchingDesc μ)).hom.hom.hom z := rfl
    have hid : (inv (spechtBranchingDesc μ) ≫ spechtBranchingDesc μ).hom.hom.hom z = z := by
      rw [IsIso.inv_hom_id]
      rfl
    rw [hom_comp_apply] at hid
    rw [hiso]
    exact hid
  have hinj : ∀ a b, (spechtBranchingDesc μ).hom.hom.hom a =
      (spechtBranchingDesc μ).hom.hom.hom b → a = b := by
    intro a b hab
    have hcancel : ∀ z, (inv (spechtBranchingDesc μ)).hom.hom.hom
        ((spechtBranchingDesc μ).hom.hom.hom z) = z := by
      intro z
      have hid : (spechtBranchingDesc μ ≫ inv (spechtBranchingDesc μ)).hom.hom.hom z = z := by
        rw [IsIso.hom_inv_id]
        rfl
      rw [hom_comp_apply] at hid
      exact hid
    rw [← hcancel a, hab, hcancel b]
  refine hinj _ _ ?_
  rw [spechtYoungBasis_apply, spechtYoungBasis_apply]
  show (spechtBranchingDesc μ).hom.hom.hom
      (FDRep.isoToLinearEquiv (spechtYoungBranchingIso μ) (spechtYoungBasisVector μ T)) =
    (spechtBranchingDesc μ).hom.hom.hom
      ((biproduct.ι (fun ν : OneBoxRemoval μ => spechtModule ν.val)
          T.largestRemoval).hom.hom.hom
        (spechtYoungBasisVector T.largestRemoval.val T.restrictLargest))
  rw [hleft, hdesc]

end Coherence
