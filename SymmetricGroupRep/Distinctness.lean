import SymmetricGroupRep.Decomposition
import SymmetricGroupRep.SubmoduleTheorem

/-! # Specht modules of distinct shapes are not isomorphic

This is Sagan, *The Symmetric Group*, 2nd ed., Proposition 2.4.5 and the distinctness half of
Theorem 2.4.6, over `ℂ`. The mechanism is the dominance order: an isomorphism `S^μ ≅ S^ν` carries
the polytabloid of a `μ`-tableau `t` to a nonzero vector of the Young permutation module `M^ν` on
which the column group of `t` acts by its sign, and a vector like that exists only when `μ`
dominates `ν`. Applying this to the isomorphism and to its inverse gives dominance both ways, and
dominance is antisymmetric.

The reason a sign eigenvector forces dominance is a counting argument. In a tabloid `S` carrying
such a vector with a nonzero coefficient, no two labels can share both a row of `S` and a column of
`t`, since their transposition would be an odd element of the column group fixing `S`. So the labels
in the first `j` rows of `S` — there are `∑ i < j, ν.rowLen i` of them — meet each column of `t` in
at most `min (μ.colLen c) j` places, and summing that bound over the columns counts exactly the
cells of `μ` in its first `j` rows.

The counting lemmas below are the transposes of the ones proving the submodule theorem in
`SubmoduleTheorem.lean`, which follow `TauCetiProject/TauCeti` (Apache-2.0). That package proves
this file's theorem too, in `RepresentationTheory/Symmetric/Specht/Distinctness.lean`, but by a
different route — a group-algebra column symmetriser transported along a permutation congruence
between the label sets of the two shapes — so nothing here is adapted from it.
-/

namespace YoungTableau

variable {n : ℕ} {μ ν : YoungDiagramOfSize n}

theorem row_lt_colLen (t : YoungTableau μ) (i : Fin n) :
    t.row i < μ.val.colLen (t.column i) :=
  YoungDiagram.mem_iff_lt_colLen.mp (t.mem_cells i)

theorem column_lt (t : YoungTableau μ) (i : Fin n) : t.column i < n :=
  lt_of_lt_of_le (μ.val.cell_snd_lt_card (t.symm i).2) μ.property.le

/-- Column `c` of a tableau meets its first `j` rows in `min (μ.colLen c) j` labels. -/
theorem card_filter_row_lt_and_column_eq (t : YoungTableau μ) (j c : ℕ) :
    (Finset.univ.filter fun y => t.row y < j ∧ t.column y = c).card =
      min (μ.val.colLen c) j := by
  classical
  have hinj : Set.InjOn t.row
      ↑(Finset.univ.filter fun y => t.row y < j ∧ t.column y = c) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    exact t.row_column_injective (Prod.ext hab (ha.2.trans hb.2.symm))
  have himage : (Finset.univ.filter fun y => t.row y < j ∧ t.column y = c).image t.row =
      Finset.range (min (μ.val.colLen c) j) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      lt_min_iff]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy2 ▸ t.row_lt_colLen y, hy1⟩
    · rintro ⟨hi1, hi2⟩
      have hcell : ((i, c) : ℕ × ℕ) ∈ μ.val.cells := YoungDiagram.mem_iff_lt_colLen.mpr hi1
      exact ⟨t ⟨(i, c), hcell⟩, ⟨by simpa using hi2, by simp⟩, by simp⟩
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_range]

/-- Column `c` of a tableau holds `μ.colLen c` labels. -/
theorem card_filter_column_eq (t : YoungTableau μ) (c : ℕ) :
    (Finset.univ.filter fun y => t.column y = c).card = μ.val.colLen c := by
  classical
  have hcolLen : μ.val.colLen c ≤ n :=
    calc μ.val.colLen c = (μ.val.col c).card := YoungDiagram.colLen_eq_card _
      _ ≤ μ.val.cells.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := μ.property
  rw [← min_eq_left hcolLen, ← t.card_filter_row_lt_and_column_eq n c]
  exact congrArg Finset.card
    (Finset.filter_congr fun y _ => ⟨fun h => ⟨t.row_lt y, h⟩, And.right⟩)

/-- **Sagan's dominance lemma.** If a label is determined by its row in the tabloid `S` together
with its column in the tableau `t`, then the shape of `t` dominates the shape of `S`.

The labels in the first `j` rows of `S` number `∑ i < j, ν.rowLen i`. Each column `c` of `t` holds
at most `min (μ.colLen c) j` of them — at most `μ.colLen c` because that is the length of the
column, and at most `j` because those labels have distinct rows in `S` — and summing that bound
over the columns of `t` counts the cells of `μ` in its first `j` rows. -/
theorem dominates_of_injective (t : YoungTableau μ) (S : Tabloid ν)
    (hinj : Function.Injective fun a => ((S.rowOf a : ℕ), t.column a)) :
    μ.val.Dominates ν.val := by
  classical
  intro j
  have hrows : (Finset.univ.filter fun a : Fin n => (S.rowOf a : ℕ) < j).card =
      ∑ i ∈ Finset.range j, ν.val.rowLen i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin n => (S.rowOf a : ℕ))
      (t := Finset.range j) (fun a ha => by simpa using (Finset.mem_filter.mp ha).2)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.filter_filter, ← S.content i]
    exact congrArg Finset.card
      (Finset.filter_congr fun a _ =>
        ⟨fun h => h.2, fun h => ⟨h ▸ Finset.mem_range.mp hi, h⟩⟩)
  have hcells : (Finset.univ.filter fun y : Fin n => t.row y < j).card =
      ∑ i ∈ Finset.range j, μ.val.rowLen i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun y : Fin n => t.row y)
      (t := Finset.range j) (fun y hy => by simpa using (Finset.mem_filter.mp hy).2)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.filter_filter, ← t.tabloid.content i]
    exact congrArg Finset.card
      (Finset.filter_congr fun y _ =>
        ⟨fun h => h.2, fun h =>
          ⟨(show t.row y = i from h) ▸ Finset.mem_range.mp hi, h⟩⟩)
  rw [← hrows, ← hcells,
    Finset.card_eq_sum_card_fiberwise (f := fun a : Fin n => t.column a) (t := Finset.range n)
      (fun a _ => Finset.mem_range.mpr (t.column_lt a)),
    Finset.card_eq_sum_card_fiberwise (f := fun y : Fin n => t.column y) (t := Finset.range n)
      (fun y _ => Finset.mem_range.mpr (t.column_lt y))]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.filter_filter, Finset.filter_filter, t.card_filter_row_lt_and_column_eq j c]
  refine le_min ?_ ?_
  · rw [← t.card_filter_column_eq c]
    refine Finset.card_le_card fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.2
  · have hinjOn : Set.InjOn (fun a : Fin n => (S.rowOf a : ℕ))
        ↑(Finset.univ.filter fun a : Fin n => (S.rowOf a : ℕ) < j ∧ t.column a = c) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
      exact hinj (Prod.ext hab (ha.2.trans hb.2.symm))
    calc (Finset.univ.filter fun a : Fin n => (S.rowOf a : ℕ) < j ∧ t.column a = c).card
        = ((Finset.univ.filter fun a : Fin n => (S.rowOf a : ℕ) < j ∧ t.column a = c).image
            fun a => (S.rowOf a : ℕ)).card := (Finset.card_image_of_injOn hinjOn).symm
      _ ≤ (Finset.range j).card := by
          refine Finset.card_le_card fun i hi => ?_
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨a, ⟨ha, -⟩, rfl⟩ := hi
          exact Finset.mem_range.mpr ha
      _ = j := Finset.card_range j

/-- A column permutation acts on the polytabloid by its sign: relabelling by `sigma` reindexes the
sum defining the polytabloid, and for `sigma` in the column group the reindexing only moves signs.

This is Sagan's Sign Lemma 2.4.1 for the column group, read at the tabloid of `t`. -/
theorem smul_polytabloid_of_mem_columnGroup (t : YoungTableau μ) {sigma : SymmetricGroup n}
    (hsigma : sigma ∈ t.columnGroup) :
    Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid μ) sigma (polytabloid t) =
      ((Equiv.Perm.sign sigma : ℤ) : ℂ) • polytabloid t := by
  rw [polytabloid, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨sigma, hsigma⟩ : t.columnGroup)) _ _ fun tau => ?_
  have hcoe : ((Equiv.mulLeft (⟨sigma, hsigma⟩ : t.columnGroup) tau : t.columnGroup) :
      SymmetricGroup n) = sigma * (tau : SymmetricGroup n) := rfl
  have hsq : ((Equiv.Perm.sign sigma : ℤ) : ℂ) * ((Equiv.Perm.sign sigma : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign sigma) with hone | hone <;> rw [hone] <;> norm_num
  rw [map_smul, Representation.ofMulAction_single, hcoe, map_mul Equiv.Perm.sign, Units.val_mul,
    Int.cast_mul]
  simp only [smul_smul, ← mul_assoc, hsq, one_mul]

/-- **Sagan's Proposition 2.4.5, in eigenvector form.** If a nonzero vector of the Young
permutation module of `ν` is scaled by the sign under the column group of a `μ`-tableau, then `μ`
dominates `ν`.

Pick a tabloid on which the vector has a nonzero coefficient. Two labels sharing a row of that
tabloid and a column of the tableau would give an odd column permutation fixing the tabloid, hence
a coefficient equal to its own negative; so no two do, and the dominance lemma applies. -/
theorem dominates_of_smul_eq_sign_smul (t : YoungTableau μ) {x : Tabloid ν →₀ ℂ} (hx : x ≠ 0)
    (hsign : ∀ sigma ∈ t.columnGroup,
      Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid ν) sigma x =
        ((Equiv.Perm.sign sigma : ℤ) : ℂ) • x) :
    μ.val.Dominates ν.val := by
  obtain ⟨S, hS⟩ := Finsupp.ne_iff.mp hx
  rw [Finsupp.coe_zero, Pi.zero_apply] at hS
  refine dominates_of_injective t S ?_
  by_contra hinj
  obtain ⟨sigma, hsigma, hsgn, hfix⟩ := t.exists_mem_columnGroup_sign_eq_neg_one S hinj
  have hinvfix : sigma⁻¹ • S = S := by
    conv_lhs => rw [← hfix]
    rw [inv_smul_smul]
  have hself : x S = -x S := by
    have hvalue := congrArg (fun y : Tabloid ν →₀ ℂ => y S) (hsign sigma hsigma)
    simpa [Representation.ofMulAction_apply, hinvfix, hsgn] using hvalue
  exact hS (by linear_combination hself / 2)

end YoungTableau

open CategoryTheory in
/-- **Specht modules of different shapes are not isomorphic.** An isomorphism of Specht modules
forces the shape of the source to dominate the shape of the target.

An isomorphism is injective, so it carries the polytabloid of a tableau `t` to a nonzero vector of
`S^ν`, hence of `M^ν`; equivariance turns the sign lemma for `t` into the sign eigenvector property
there.

See Sagan, *The Symmetric Group*, 2nd ed., Proposition 2.4.5. -/
theorem dominates_of_iso_spechtSubrepresentation {n : ℕ} (μ ν : YoungDiagramOfSize n)
    (f : FDRep.of (spechtSubrepresentation μ).toRepresentation ≅
      FDRep.of (spechtSubrepresentation ν).toRepresentation) :
    μ.val.Dominates ν.val := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  set F := FDRep.homEquivIntertwiningMap _ _ f.hom
  set e : ↥(spechtSubrepresentation μ).toSubmodule :=
    ⟨YoungTableau.polytabloid t, Submodule.subset_span ⟨t, rfl⟩⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    have ha : (ConcreteCategory.hom f.inv.hom) (F a) = a := Iso.hom_inv_id_apply f a
    have hb : (ConcreteCategory.hom f.inv.hom) (F b) = b := Iso.hom_inv_id_apply f b
    rw [hab, hb] at ha
    exact ha.symm
  refine YoungTableau.dominates_of_smul_eq_sign_smul t
    (x := ((F e : ↥(spechtSubrepresentation ν).toSubmodule) : Tabloid ν →₀ ℂ)) ?_ ?_
  · intro hzero
    have he : e = 0 := hFinj (by rw [map_zero]; exact Submodule.coe_eq_zero.mp hzero)
    exact YoungTableau.polytabloid_ne_zero t (congrArg Subtype.val he)
  · intro sigma hsigma
    have hpolytabloid : (FDRep.of (spechtSubrepresentation μ).toRepresentation).ρ sigma e =
        ((Equiv.Perm.sign sigma : ℤ) : ℂ) • e :=
      Subtype.ext (YoungTableau.smul_polytabloid_of_mem_columnGroup t hsigma)
    have hcomm := Representation.IntertwiningMap.isIntertwining _ _ F sigma e
    rw [hpolytabloid, map_smul] at hcomm
    exact congrArg Subtype.val hcomm.symm
