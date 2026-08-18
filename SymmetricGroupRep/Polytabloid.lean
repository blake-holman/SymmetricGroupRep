import SymmetricGroupRep.Tabloids
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Tableaux, column groups, and polytabloids

This is the concrete construction underlying the complex Specht module,
following Sagan, *The Symmetric Group*, 2nd ed., Section 2.3: Definition 2.3.1
for the column group, Definition 2.3.2 for the polytabloid, and Definition
2.3.4 for the Specht module as the span of the polytabloids inside the Young
permutation module.
-/

/-- A bijective filling of the cells of `μ` by the labels `Fin n`. -/
abbrev YoungTableau {n : ℕ} (μ : YoungDiagramOfSize n) := ↥μ.val.cells ≃ Fin n

namespace YoungTableau

variable {n : ℕ} {μ : YoungDiagramOfSize n}

/-- Every Young diagram of size `n` admits a tableau. -/
theorem nonempty (μ : YoungDiagramOfSize n) : Nonempty (YoungTableau μ) :=
  ⟨μ.val.cells.equivFinOfCardEq μ.property⟩

/-- The row containing a label. -/
def row (t : YoungTableau μ) (i : Fin n) : ℕ := (t.symm i).1.1

/-- The column containing a label. -/
def column (t : YoungTableau μ) (i : Fin n) : ℕ := (t.symm i).1.2

/-- Relabelling a tableau by a permutation. -/
instance : MulAction (SymmetricGroup n) (YoungTableau μ) where
  smul sigma t := t.trans sigma
  one_smul t := by
    apply Equiv.ext
    intro c
    rfl
  mul_smul sigma tau t := by
    apply Equiv.ext
    intro c
    rfl

@[simp]
theorem smul_symm_apply (sigma : SymmetricGroup n) (t : YoungTableau μ) (i : Fin n) :
    (sigma • t).symm i = t.symm (sigma⁻¹ i) :=
  rfl

@[simp]
theorem smul_row (sigma : SymmetricGroup n) (t : YoungTableau μ) (i : Fin n) :
    (sigma • t).row i = t.row (sigma⁻¹ i) :=
  rfl

@[simp]
theorem smul_column (sigma : SymmetricGroup n) (t : YoungTableau μ) (i : Fin n) :
    (sigma • t).column i = t.column (sigma⁻¹ i) :=
  rfl

/-- The column group of a tableau: the relabellings that keep every label in its
own column. -/
def columnGroup (t : YoungTableau μ) : Subgroup (SymmetricGroup n) where
  carrier := {sigma | ∀ i, t.column (sigma i) = t.column i}
  mul_mem' {a b} ha hb i := by
    change t.column (a (b i)) = t.column i
    rw [ha (b i), hb i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by
    have hcol := ha (a⁻¹ i)
    rw [show a (a⁻¹ i) = i from a.apply_symm_apply i] at hcol
    exact hcol.symm

@[simp]
theorem mem_columnGroup {t : YoungTableau μ} {sigma : SymmetricGroup n} :
    sigma ∈ t.columnGroup ↔ ∀ i, t.column (sigma i) = t.column i :=
  Iff.rfl

noncomputable instance (t : YoungTableau μ) : Fintype t.columnGroup :=
  Fintype.ofFinite _

/-- The tabloid underlying a tableau: it records the row of each label. -/
def tabloid (t : YoungTableau μ) : Tabloid μ := Tabloid.ofCellEquiv t.symm

@[simp]
theorem smul_tabloid (sigma : SymmetricGroup n) (t : YoungTableau μ) :
    (sigma • t).tabloid = sigma • t.tabloid := by
  apply Tabloid.ext
  funext i
  apply Fin.ext
  rfl

@[simp]
theorem tabloid_rowOf (t : YoungTableau μ) (i : Fin n) :
    (t.tabloid.rowOf i : ℕ) = t.row i :=
  rfl

/-- A column-preserving relabelling that fixes the tabloid is the identity. -/
theorem eq_one_of_mem_columnGroup_of_smul_tabloid_eq {t : YoungTableau μ}
    {pi : SymmetricGroup n} (hpi : pi ∈ t.columnGroup)
    (hfix : pi • t.tabloid = t.tabloid) : pi = 1 := by
  apply Equiv.ext
  intro i
  have hrow : t.row (pi i) = t.row i := by
    have := congrArg (fun T => (Tabloid.rowOf T (pi i) : ℕ)) hfix
    simpa using this.symm
  have hcolumn : t.column (pi i) = t.column i := hpi i
  have hcell : t.symm (pi i) = t.symm i :=
    Subtype.ext (Prod.ext hrow hcolumn)
  simpa using t.symm.injective hcell

/-- Distinct column-group elements move the tabloid to distinct tabloids. -/
theorem smul_tabloid_injOn (t : YoungTableau μ) :
    Function.Injective fun sigma : t.columnGroup =>
      (sigma : SymmetricGroup n) • t.tabloid := by
  intro sigma tau hequal
  have hequal' : (sigma : SymmetricGroup n) • t.tabloid =
      (tau : SymmetricGroup n) • t.tabloid := hequal
  apply Subtype.ext
  have hmem : (tau : SymmetricGroup n)⁻¹ * (sigma : SymmetricGroup n) ∈ t.columnGroup :=
    t.columnGroup.mul_mem (t.columnGroup.inv_mem tau.2) sigma.2
  have hfix : ((tau : SymmetricGroup n)⁻¹ * (sigma : SymmetricGroup n)) • t.tabloid =
      t.tabloid := by
    rw [mul_smul, hequal', ← mul_smul, inv_mul_cancel, one_smul]
  have hone := eq_one_of_mem_columnGroup_of_smul_tabloid_eq hmem hfix
  rw [inv_mul_eq_one] at hone
  exact hone.symm

/-- Conjugation identifies the column group of a tableau with that of its
relabelling. -/
def columnGroupEquiv (sigma : SymmetricGroup n) (t : YoungTableau μ) :
    t.columnGroup ≃ (sigma • t).columnGroup where
  toFun tau := ⟨sigma * (tau : SymmetricGroup n) * sigma⁻¹, by
    intro i
    change t.column (sigma⁻¹ (sigma * (tau : SymmetricGroup n) * sigma⁻¹ $ i)) =
      t.column (sigma⁻¹ i)
    have hstep : sigma⁻¹ (sigma * (tau : SymmetricGroup n) * sigma⁻¹ $ i) =
        (tau : SymmetricGroup n) (sigma⁻¹ i) := by
      simp [Equiv.Perm.mul_apply]
    rw [hstep]
    exact tau.2 (sigma⁻¹ i)⟩
  invFun pi := ⟨sigma⁻¹ * (pi : SymmetricGroup n) * sigma, by
    intro i
    have hpi := pi.2 (sigma i)
    change t.column (sigma⁻¹ * (pi : SymmetricGroup n) * sigma $ i) = t.column i
    change (sigma • t).column ((pi : SymmetricGroup n) (sigma i)) =
      (sigma • t).column (sigma i) at hpi
    simpa [Equiv.Perm.mul_apply] using hpi⟩
  left_inv tau := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv pi := by
    apply Subtype.ext
    simp [mul_assoc]

/-- The polytabloid of a tableau: the column-antisymmetrised tabloid. -/
noncomputable def polytabloid (t : YoungTableau μ) : MonoidAlgebra ℂ (Tabloid μ) :=
  ∑ sigma : t.columnGroup,
    ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
      MonoidAlgebra.single ((sigma : SymmetricGroup n) • t.tabloid) 1

/-- Relabelling a tableau relabels its polytabloid. This is Sagan's Lemma 2.3.3(4). -/
theorem smul_polytabloid (sigma : SymmetricGroup n) (t : YoungTableau μ) :
    (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)) sigma (polytabloid t) =
      polytabloid (sigma • t) := by
  rw [polytabloid, map_sum, polytabloid]
  refine Fintype.sum_equiv (columnGroupEquiv sigma t) _ _ fun tau => ?_
  have hsign : Equiv.Perm.sign ((columnGroupEquiv sigma t tau : SymmetricGroup n)) =
      Equiv.Perm.sign (tau : SymmetricGroup n) := by
    show Equiv.Perm.sign (sigma * (tau : SymmetricGroup n) * sigma⁻¹) = _
    simp [mul_comm, ← mul_assoc, Int.units_mul_self]
  have hact : ((columnGroupEquiv sigma t tau : SymmetricGroup n)) • (sigma • t).tabloid =
      sigma • ((tau : SymmetricGroup n) • t.tabloid) := by
    rw [smul_tabloid, ← mul_smul, ← mul_smul]
    congr 1
    show sigma * (tau : SymmetricGroup n) * sigma⁻¹ * sigma = sigma * (tau : SymmetricGroup n)
    group
  rw [hsign, hact]
  simp [Representation.ofMulAction_single]

/-- The polytabloid has coefficient one on its own tabloid; in particular it is
nonzero, so the Specht module is a nonzero subrepresentation. -/
theorem polytabloid_apply_tabloid (t : YoungTableau μ) :
    (polytabloid t).coeff t.tabloid = 1 := by
  rw [polytabloid, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  rw [Finset.sum_eq_single (1 : t.columnGroup)]
  · simp
  · intro sigma _ hne
    have hne' : (sigma : SymmetricGroup n) • t.tabloid ≠ t.tabloid := by
      intro hequal
      exact hne (Subtype.ext (eq_one_of_mem_columnGroup_of_smul_tabloid_eq sigma.2 hequal))
    simp [hne']
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem polytabloid_ne_zero (t : YoungTableau μ) : polytabloid t ≠ 0 := by
  intro hzero
  have := polytabloid_apply_tabloid t
  rw [hzero] at this
  simp at this

end YoungTableau

/-- The Specht subrepresentation of the Young permutation module: the span of the
polytabloids.

See Sagan, *The Symmetric Group*, 2nd ed., Definition 2.3.4. Invariance is
`YoungTableau.smul_polytabloid`, which is Sagan's Lemma 2.3.3(4). -/
noncomputable def spechtSubrepresentation {n : ℕ} (μ : YoungDiagramOfSize n) :
    Subrepresentation (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ)) where
  toSubmodule := Submodule.span ℂ (Set.range (YoungTableau.polytabloid (μ := μ)))
  apply_mem_toSubmodule sigma v hv := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨t, rfl⟩ := hx
        rw [YoungTableau.smul_polytabloid]
        exact Submodule.subset_span ⟨sigma • t, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The Specht module is a nonzero subrepresentation: it contains the nonzero
polytabloid of any tableau. -/
theorem spechtSubrepresentation_ne_bot {n : ℕ} (μ : YoungDiagramOfSize n) :
    (spechtSubrepresentation μ).toSubmodule ≠ ⊥ := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  intro hbot
  have hmem : YoungTableau.polytabloid t ∈ (spechtSubrepresentation μ).toSubmodule :=
    Submodule.subset_span ⟨t, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact YoungTableau.polytabloid_ne_zero t hmem
