import SymmetricGroupRep.Classification
import SymmetricGroupRep.Pieri

open CategoryTheory
open scoped MonoidalCategory

/-! # Twisting by the sign character

Tensoring with the sign representation permutes the simple modules of `S_n`, and
the permutation it induces is transposition of the Young diagram. This is James,
*The Representation Theory of the Symmetric Groups*, Lecture Notes in
Mathematics 682 (1978), Theorem 6.7 on page 25.

James proves it by constructing a homomorphism out of `M^(μᵀ)` and then counting
dimensions. Here Schur's lemma replaces the dimension count: `S^(μᵀ)` and the
sign twist of `S^μ` are both irreducible, so a single nonzero map between them
is already an isomorphism.

The twisted representation `g ↦ sgn g • ρ g` is used in place of `S^μ ⊗ sgn`, so
that the whole construction stays inside the tabloid module. The two are
identified at the end by their characters.

The map sends the tabloid `σ • {tᵀ}` to `sgn σ • σ • e_t`. It is well defined
because the permutations fixing `{tᵀ}` are exactly the column-preserving
permutations of `t`, and those multiply `e_t` by their sign, which the twist
cancels. It is nonzero because the image of the polytabloid `e_(tᵀ)` has
coefficient `Fintype.card (t.transpose.columnGroup)` on the tabloid of `t`.
-/

/-- Twisting a representation of the symmetric group by the sign character. -/
noncomputable def Representation.signTwist {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (SymmetricGroup n) V) : Representation ℂ (SymmetricGroup n) V where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℂ) • rho g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp [smul_smul]
    ring_nf

@[simp]
theorem Representation.signTwist_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (SymmetricGroup n) V) (g : SymmetricGroup n) (v : V) :
    rho.signTwist g v = ((Equiv.Perm.sign g : ℤ) : ℂ) • rho g v :=
  rfl

/-- A subspace is stable under a representation exactly when it is stable under the sign
twist, since the sign is a unit. -/
def Subrepresentation.signTwistOrderIso {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (SymmetricGroup n) V) :
    Subrepresentation rho.signTwist ≃o Subrepresentation rho where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    have := W.apply_mem_toSubmodule g hv
    rw [Representation.signTwist_apply] at this
    simpa using W.toSubmodule.smul_mem ((Equiv.Perm.sign g : ℤ) : ℂ)⁻¹ this⟩
  invFun W := ⟨W.toSubmodule, fun g v hv =>
    W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule g hv)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (SymmetricGroup n) V) [Representation.IsIrreducible rho] :
    Representation.IsIrreducible rho.signTwist :=
  (Subrepresentation.signTwistOrderIso rho).isSimpleOrder_iff.mpr inferInstance

/-- The Specht module twisted by the sign character. -/
noncomputable def spechtSignTwist {n : ℕ} (μ : YoungDiagramOfSize n) :
    SymmetricGroupRepresentation n :=
  FDRep.of (spechtSubrepresentation μ).toRepresentation.signTwist

instance {n : ℕ} (μ : YoungDiagramOfSize n) : Simple (spechtSignTwist μ) :=
  FDRep.simple_of_isIrreducible _

/-- The sign representation is one dimensional, so its character is the sign itself. -/
theorem SymmetricGroupRepresentation.sign_character {n : ℕ} (g : SymmetricGroup n) :
    (SymmetricGroupRepresentation.sign n).character g = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  unfold FDRep.character SymmetricGroupRepresentation.sign
  show LinearMap.trace ℂ ℂ (((Equiv.Perm.sign g : ℤ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/-- The sign twist multiplies the character by the sign. -/
theorem spechtSignTwist_character {n : ℕ} (μ : YoungDiagramOfSize n) (g : SymmetricGroup n) :
    (spechtSignTwist μ).character g =
      ((Equiv.Perm.sign g : ℤ) : ℂ) * (spechtModule μ).character g := by
  show LinearMap.trace ℂ _
    (((Equiv.Perm.sign g : ℤ) : ℂ) • (spechtSubrepresentation μ).toRepresentation g) = _
  rw [map_smul]
  rfl

/-- The sign twist of a Specht module is its tensor product with the sign representation:
both have the sign-weighted Specht character. -/
theorem spechtSignTwist_iso_tensor_sign {n : ℕ} (μ : YoungDiagramOfSize n) :
    Nonempty (spechtSignTwist μ ≅ spechtModule μ ⊗ SymmetricGroupRepresentation.sign n) :=
  SymmetricGroupRepresentation.nonempty_iso_of_character_eq <| funext fun g => by
    rw [FDRep.char_tensor, Pi.mul_apply, spechtSignTwist_character,
      SymmetricGroupRepresentation.sign_character, mul_comm]

/-- Transpose a fixed-size Young diagram. -/
def YoungDiagramOfSize.transpose {n : ℕ}
    (μ : YoungDiagramOfSize n) : YoungDiagramOfSize n :=
  ⟨μ.val.transpose, by
    rw [YoungDiagram.card]
    simpa [YoungDiagram.transpose] using μ.property⟩

namespace YoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize n}

/-- The transposed tableau: the same filling read with rows and columns exchanged. -/
def transpose (t : YoungTableau μ) : YoungTableau μ.transpose :=
  (Equiv.subtypeEquiv (Equiv.prodComm ℕ ℕ) fun _ => YoungDiagram.mem_transpose).trans t

@[simp]
theorem transpose_row (t : YoungTableau μ) (i : Fin n) : t.transpose.row i = t.column i :=
  rfl

@[simp]
theorem transpose_column (t : YoungTableau μ) (i : Fin n) : t.transpose.column i = t.row i :=
  rfl

/-- The permutations fixing the tabloid of the transposed tableau are exactly the
column-preserving permutations of the original tableau. -/
theorem smul_transpose_tabloid_eq_iff (t : YoungTableau μ) (sigma : SymmetricGroup n) :
    sigma • t.transpose.tabloid = t.transpose.tabloid ↔ sigma ∈ t.columnGroup := by
  simp only [Tabloid.ext_iff, funext_iff, Fin.ext_iff, mem_columnGroup, Tabloid.smul_rowOf,
    tabloid_rowOf, transpose_row]
  constructor
  · intro h i
    have hi := h (sigma i)
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at hi
    exact hi.symm
  · intro h i
    have hi := h (sigma⁻¹ i)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hi
    exact hi.symm

/-- A column-preserving permutation multiplies the polytabloid by its sign. -/
theorem ofMulAction_polytabloid_of_mem_columnGroup {t : YoungTableau μ}
    {sigma : SymmetricGroup n} (hsigma : sigma ∈ t.columnGroup) :
    Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) sigma (polytabloid t) =
      ((Equiv.Perm.sign sigma : ℤ) : ℂ) • polytabloid t := by
  rw [polytabloid, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨sigma, hsigma⟩ : t.columnGroup)) _ _ fun tau => ?_
  rw [map_smul, Representation.ofMulAction_single]
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Units.val_mul, Int.cast_mul, mul_smul]
  rw [smul_smul, smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
    Int.cast_one, one_smul]

/-- A permutation preserving the columns of the transposed tableau preserves the tabloid of
the original one. -/
theorem smul_tabloid_of_mem_transpose_columnGroup {t : YoungTableau μ}
    {sigma : SymmetricGroup n} (hsigma : sigma ∈ t.transpose.columnGroup) :
    sigma • t.tabloid = t.tabloid := by
  apply Tabloid.ext
  funext i
  apply Fin.ext
  have hi := hsigma (sigma⁻¹ i)
  simp only [transpose_column, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hi
  simpa using hi.symm

/-- The polytabloid of `t`, as an element of the Specht module. -/
noncomputable def spechtPolytabloid (t : YoungTableau μ) :
    ↥(spechtSubrepresentation μ).toSubmodule :=
  ⟨polytabloid t, Submodule.subset_span ⟨t, rfl⟩⟩

/-- The sign twist fixes the polytabloid under column-preserving permutations. -/
theorem signTwist_spechtPolytabloid_of_mem_columnGroup {t : YoungTableau μ}
    {sigma : SymmetricGroup n} (hsigma : sigma ∈ t.columnGroup) :
    (spechtSubrepresentation μ).toRepresentation.signTwist sigma t.spechtPolytabloid =
      t.spechtPolytabloid := by
  apply Subtype.ext
  show ((Equiv.Perm.sign sigma : ℤ) : ℂ) •
    (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)) sigma (polytabloid t) =
      polytabloid t
  rw [ofMulAction_polytabloid_of_mem_columnGroup hsigma, smul_smul, ← Int.cast_mul,
    ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

/-- A permutation carrying the tabloid of the transposed tableau to `T`. -/
private noncomputable def transposeCarrier (t : YoungTableau μ) (T : Tabloid μ.transpose) :
    SymmetricGroup n :=
  (MulAction.exists_smul_eq (SymmetricGroup n) t.transpose.tabloid T).choose

private theorem transposeCarrier_smul (t : YoungTableau μ) (T : Tabloid μ.transpose) :
    transposeCarrier t T • t.transpose.tabloid = T :=
  (MulAction.exists_smul_eq (SymmetricGroup n) t.transpose.tabloid T).choose_spec

/-- Transporting the polytabloid of `t` along the sign twist gives a well-defined element of
the Specht module for every tabloid of the transposed shape. -/
private noncomputable def signTwistOrbitMap (t : YoungTableau μ) (T : Tabloid μ.transpose) :
    ↥(spechtSubrepresentation μ).toSubmodule :=
  (spechtSubrepresentation μ).toRepresentation.signTwist (transposeCarrier t T)
    t.spechtPolytabloid

private theorem signTwistOrbitMap_eq (t : YoungTableau μ) {T : Tabloid μ.transpose}
    {sigma : SymmetricGroup n} (hsigma : sigma • t.transpose.tabloid = T) :
    signTwistOrbitMap t T =
      (spechtSubrepresentation μ).toRepresentation.signTwist sigma t.spechtPolytabloid := by
  have hmem : sigma⁻¹ * transposeCarrier t T ∈ t.columnGroup := by
    rw [← smul_transpose_tabloid_eq_iff, mul_smul, transposeCarrier_smul, ← hsigma, inv_smul_smul]
  show (spechtSubrepresentation μ).toRepresentation.signTwist (transposeCarrier t T) _ = _
  rw [show transposeCarrier t T = sigma * (sigma⁻¹ * transposeCarrier t T) from
      (mul_inv_cancel_left _ _).symm, map_mul, Module.End.mul_apply,
    signTwist_spechtPolytabloid_of_mem_columnGroup hmem]

private theorem signTwistOrbitMap_smul (t : YoungTableau μ) (g : SymmetricGroup n)
    (T : Tabloid μ.transpose) :
    signTwistOrbitMap t (g • T) =
      (spechtSubrepresentation μ).toRepresentation.signTwist g (signTwistOrbitMap t T) := by
  rw [signTwistOrbitMap_eq t (sigma := g * transposeCarrier t T)
      (by rw [mul_smul, transposeCarrier_smul]),
    signTwistOrbitMap, map_mul]
  rfl

/-- The linear extension of the orbit map to the transposed permutation module. -/
private noncomputable def signTwistLinearMap (t : YoungTableau μ) :
    (Tabloid μ.transpose →₀ ℂ) →ₗ[ℂ] ↥(spechtSubrepresentation μ).toSubmodule :=
  Finsupp.linearCombination ℂ (signTwistOrbitMap t)

private theorem signTwistLinearMap_ofMulAction (t : YoungTableau μ) (g : SymmetricGroup n)
    (v : Tabloid μ.transpose →₀ ℂ) :
    signTwistLinearMap t
        (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ.transpose) g v) =
      (spechtSubrepresentation μ).toRepresentation.signTwist g (signTwistLinearMap t v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single T c =>
      simp [signTwistLinearMap, Representation.ofMulAction_single, signTwistOrbitMap_smul]

private theorem signTwistLinearMap_polytabloid (t : YoungTableau μ) :
    signTwistLinearMap t (polytabloid t.transpose) =
      ∑ sigma : t.transpose.columnGroup,
        (spechtSubrepresentation μ).toRepresentation (sigma : SymmetricGroup n)
          t.spechtPolytabloid := by
  rw [polytabloid, map_sum]
  refine Finset.sum_congr rfl fun sigma _ => ?_
  rw [map_smul]
  simp only [signTwistLinearMap, Finsupp.linearCombination_single, one_smul]
  rw [signTwistOrbitMap_eq t (sigma := (sigma : SymmetricGroup n)) rfl,
    Representation.signTwist_apply, smul_smul, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

private theorem signTwistLinearMap_polytabloid_ne_zero (t : YoungTableau μ) :
    signTwistLinearMap t (polytabloid t.transpose) ≠ 0 := by
  have hvalue : (signTwistLinearMap t (polytabloid t.transpose) : Tabloid μ →₀ ℂ) t.tabloid =
      (Fintype.card t.transpose.columnGroup : ℂ) := by
    have hterm : ∀ sigma : t.transpose.columnGroup,
        ((spechtSubrepresentation μ).toRepresentation (sigma : SymmetricGroup n)
          t.spechtPolytabloid : Tabloid μ →₀ ℂ) t.tabloid = 1 := fun sigma => by
      rw [show ((spechtSubrepresentation μ).toRepresentation (sigma : SymmetricGroup n)
            t.spechtPolytabloid : Tabloid μ →₀ ℂ) =
            Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)
              (sigma : SymmetricGroup n) (polytabloid t) from rfl,
        Representation.ofMulAction_apply,
        smul_tabloid_of_mem_transpose_columnGroup (t.transpose.columnGroup.inv_mem sigma.2),
        polytabloid_apply_tabloid]
    rw [signTwistLinearMap_polytabloid, AddSubmonoidClass.coe_finset_sum,
      Finsupp.finset_sum_apply]
    simp [hterm]
  intro hzero
  rw [hzero] at hvalue
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.mp hvalue.symm)

/-- The orbit map, read as a morphism from the transposed permutation module to the
sign-twisted Specht module. -/
private noncomputable def signTwistHom (t : YoungTableau μ) :
    youngPermutationModule μ.transpose ⟶ spechtSignTwist μ :=
  Action.Hom.mk (FGModuleCat.ofHom (signTwistLinearMap t)) (by
    intro g
    apply FGModuleCat.hom_ext
    ext v
    exact signTwistLinearMap_ofMulAction t g v)

private noncomputable def spechtSignTwistHom (t : YoungTableau μ) :
    spechtModule μ.transpose ⟶ spechtSignTwist μ :=
  Subrepresentation.toFDRepHom (youngPermutationModule μ.transpose)
      (spechtSubrepresentation μ.transpose) ≫ signTwistHom t

private theorem spechtSignTwistHom_ne_zero (t : YoungTableau μ) : spechtSignTwistHom t ≠ 0 := by
  intro hzero
  apply signTwistLinearMap_polytabloid_ne_zero t
  have happly := congrArg (fun f : spechtModule μ.transpose ⟶ spechtSignTwist μ =>
    f.hom.hom t.transpose.spechtPolytabloid) hzero
  simpa [spechtSignTwistHom, signTwistHom, spechtPolytabloid] using happly

end YoungTableau

/-- Transposing the Young diagram twists the Specht module by the sign character. -/
theorem spechtModule_transpose_iso_spechtSignTwist {n : ℕ} (μ : YoungDiagramOfSize n) :
    Nonempty (spechtModule μ.transpose ≅ spechtSignTwist μ) := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  haveI := spechtModule_irreducible μ.transpose
  haveI := isIso_of_hom_simple (YoungTableau.spechtSignTwistHom_ne_zero t)
  exact ⟨asIso (YoungTableau.spechtSignTwistHom t)⟩
