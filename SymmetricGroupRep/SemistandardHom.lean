import SymmetricGroupRep.Classification

/-! # The semistandard homomorphisms from a Specht module to a Young permutation module

This file computes `dim Hom(S^lam, M^mu)`, the multiplicity of the Specht module `S^lam` in the
Young permutation module `M^mu`.  Following Sagan, *The Symmetric Group*, 2nd ed., Section 2.10,
the answer is the number of semistandard tabloids: those `S : Tabloid mu` whose rows, read through
a fixed tableau `t` of shape `lam`, increase weakly along the rows of `t` and strictly down its
columns.

Both bounds come from evaluating a homomorphism at the single polytabloid `e_t`, which generates
`S^lam`.  The upper bound is Sagan's Lemma 2.10.7: the vector `F e_t` is a sign eigenvector for the
column group of `t`, and if it is nonzero then it has a nonzero coefficient at a semistandard
tabloid.  The lower bound is Sagan's Proposition 2.10.6: the homomorphisms attached to the
semistandard tabloids have a unitriangular coefficient matrix.

Two weights organise the combinatorics in place of Sagan's dominance order on generalised tableaux:
`rowWeight t S = ∑ i, t.column i * S.rowOf i` and `colWeight t S = ∑ i, t.row i * S.rowOf i`.
Sorting a row of `t` increasingly raises `rowWeight`, sorting a column increasingly raises
`colWeight`, and each weight is maximal exactly at the sorted representative of its orbit.

The Garnir relation (Sagan's Proposition 2.6.3) is used only through its antisymmetriser form:
summing `sgn(sigma) sigma` over all permutations of the labels in the union of a lower part of one
column of `t` and an upper part of the next annihilates `e_t`.  No Garnir element and no transversal
is needed, because the argument only needs that the coefficient the relation produces is a positive
natural number.
-/

open Finset

/-! ### Permutations of a block of labels -/

section Block

variable {n : ℕ} {lam : YoungDiagramOfSize n}

/-- The permutations of a block of labels: those fixing every label outside the block. -/
def blockGroup (X : Finset (Fin n)) : Subgroup (SymmetricGroup n) :=
  fixingSubgroup (SymmetricGroup n) ((X : Set (Fin n))ᶜ)

@[simp]
theorem mem_blockGroup {X : Finset (Fin n)} {sigma : SymmetricGroup n} :
    sigma ∈ blockGroup X ↔ ∀ i ∉ X, sigma i = i := by
  simp [blockGroup, mem_fixingSubgroup_iff]

noncomputable instance (X : Finset (Fin n)) : Fintype (blockGroup X) :=
  Fintype.ofFinite _

/-- A block permutation maps the block to itself. -/
theorem blockGroup.mapsTo {X : Finset (Fin n)} {sigma : SymmetricGroup n}
    (hsigma : sigma ∈ blockGroup X) {i : Fin n} (hi : i ∈ X) : sigma i ∈ X := by
  by_contra hout
  have hfix := mem_blockGroup.mp ((blockGroup X).inv_mem hsigma) _ hout
  rw [show sigma⁻¹ (sigma i) = i from sigma.symm_apply_apply i] at hfix
  exact hout (hfix ▸ hi)

/-- Transposing two labels of a block is a block permutation. -/
theorem blockGroup.swap_mem {X : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ X) (hb : b ∈ X) : Equiv.swap a b ∈ blockGroup X :=
  mem_blockGroup.mpr fun _ hi =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ ha)) fun h => hi (h ▸ hb)

/-- The antisymmetriser over the permutations of a block of labels, acting on the Young
permutation module. -/
noncomputable def blockAntisymmetriser (X : Finset (Fin n)) (lam : YoungDiagramOfSize n) :
    (Tabloid lam →₀ ℂ) →ₗ[ℂ] (Tabloid lam →₀ ℂ) :=
  ∑ sigma : blockGroup X, ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
    Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid lam) (sigma : SymmetricGroup n)

theorem blockAntisymmetriser_apply (X : Finset (Fin n)) (v : Tabloid lam →₀ ℂ) :
    blockAntisymmetriser X lam v = ∑ sigma : blockGroup X,
      ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
        Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid lam)
          (sigma : SymmetricGroup n) v := by
  rw [blockAntisymmetriser, LinearMap.sum_apply]
  rfl

/-- The block antisymmetriser absorbs a block permutation through its sign. -/
theorem blockAntisymmetriser_ofMulAction (X : Finset (Fin n)) {g : SymmetricGroup n}
    (hg : g ∈ blockGroup X) (v : Tabloid lam →₀ ℂ) :
    blockAntisymmetriser X lam
        (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid lam) g v) =
      ((Equiv.Perm.sign g : ℤ) : ℂ) • blockAntisymmetriser X lam v := by
  rw [blockAntisymmetriser_apply, blockAntisymmetriser_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : blockGroup X)) _ _ fun sigma => ?_
  have hcoe : ((Equiv.mulRight (⟨g, hg⟩ : blockGroup X) sigma : blockGroup X) :
      SymmetricGroup n) = (sigma : SymmetricGroup n) * g := rfl
  rw [hcoe, map_mul (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid lam)),
    Module.End.mul_apply, smul_smul, map_mul Equiv.Perm.sign, Units.val_mul, Int.cast_mul,
    ← mul_assoc]
  congr 1
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hone | hone <;> rw [hone] <;> push_cast <;>
    ring

/-- The block antisymmetriser kills a tabloid that puts two block labels in one row: their
transposition is an odd block permutation fixing the tabloid. -/
theorem blockAntisymmetriser_single_eq_zero {X : Finset (Fin n)} {U : Tabloid lam} {a b : Fin n}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) (hrow : U.rowOf a = U.rowOf b) :
    blockAntisymmetriser X lam (Finsupp.single U 1) = 0 := by
  have hfix : Equiv.swap a b • U = U := by
    refine Tabloid.ext (funext fun i => ?_)
    rw [Tabloid.smul_rowOf, Equiv.swap_inv]
    rcases eq_or_ne i a with rfl | hia
    · rw [Equiv.swap_apply_left, hrow]
    · rcases eq_or_ne i b with rfl | hib
      · rw [Equiv.swap_apply_right, hrow]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  have hself : blockAntisymmetriser X lam (Finsupp.single U 1) =
      -blockAntisymmetriser X lam (Finsupp.single U 1) := by
    conv_lhs => rw [← hfix, ← Representation.ofMulAction_single,
      blockAntisymmetriser_ofMulAction X (blockGroup.swap_mem ha hb), Equiv.Perm.sign_swap hab]
    simp
  have htwo : (2 : ℂ) • blockAntisymmetriser X lam (Finsupp.single U 1) = 0 := by
    rw [two_smul, ← eq_neg_iff_add_eq_zero]
    exact hself
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

end Block

namespace YoungTableau

variable {n : ℕ} {lam mu : YoungDiagramOfSize n}

noncomputable local instance : Fintype (Tabloid mu) := Fintype.ofFinite _

/-! ### The row group of a tableau and the permutations of a block of labels -/

/-- The row group of a tableau: the relabellings that keep every label in its own row. -/
def rowGroup (t : YoungTableau lam) : Subgroup (SymmetricGroup n) where
  carrier := {sigma | ∀ i, t.row (sigma i) = t.row i}
  mul_mem' {a b} ha hb i := by
    change t.row (a (b i)) = t.row i
    rw [ha (b i), hb i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by
    have hrow := ha (a⁻¹ i)
    rw [show a (a⁻¹ i) = i from a.apply_symm_apply i] at hrow
    exact hrow.symm

@[simp]
theorem mem_rowGroup {t : YoungTableau lam} {sigma : SymmetricGroup n} :
    sigma ∈ t.rowGroup ↔ ∀ i, t.row (sigma i) = t.row i :=
  Iff.rfl

noncomputable instance (t : YoungTableau lam) : Fintype t.rowGroup :=
  Fintype.ofFinite _

/-- A relabelling fixes the tabloid of a tableau exactly when it keeps every label in its row. -/
theorem smul_tabloid_eq_iff_mem_rowGroup (t : YoungTableau lam) (sigma : SymmetricGroup n) :
    sigma • t.tabloid = t.tabloid ↔ sigma ∈ t.rowGroup := by
  constructor
  · intro hfix i
    have hvalue := congrArg (fun T : Tabloid lam => (T.rowOf (sigma i) : ℕ)) hfix
    simpa using hvalue.symm
  · intro hmem
    refine Tabloid.ext (funext fun i => Fin.ext ?_)
    rw [Tabloid.smul_rowOf, t.tabloid_rowOf, t.tabloid_rowOf]
    simpa using (hmem (sigma⁻¹ i)).symm

/-! ### Semistandard tabloids -/

/-- The rows of `t` read weakly increasing entries from `S`. -/
def RowIncreasing (t : YoungTableau lam) (S : Tabloid mu) : Prop :=
  ∀ i j, t.row i = t.row j → t.column i < t.column j → S.rowOf i ≤ S.rowOf j

/-- The columns of `t` read strictly increasing entries from `S`. -/
def ColStrict (t : YoungTableau lam) (S : Tabloid mu) : Prop :=
  ∀ i j, t.column i = t.column j → t.row i < t.row j → S.rowOf i < S.rowOf j

/-- A tabloid is semistandard for `t` when `t` reads it as a semistandard tableau: weakly
increasing along rows and strictly increasing down columns. -/
def Semistandard (t : YoungTableau lam) (S : Tabloid mu) : Prop :=
  RowIncreasing t S ∧ ColStrict t S

/-- A column-strict tabloid separates the labels of each column of `t`. -/
theorem ColStrict.injective {t : YoungTableau lam} {S : Tabloid mu} (hS : ColStrict t S) :
    Function.Injective fun i => (t.column i, S.rowOf i) := by
  intro a b hab
  rw [Prod.mk.injEq] at hab
  rcases lt_trichotomy (t.row a) (t.row b) with h | h | h
  · exact absurd hab.2 (hS a b hab.1 h).ne
  · exact t.row_column_injective (Prod.ext h hab.1)
  · exact absurd hab.2.symm (hS b a hab.1.symm h).ne

/-! ### The two weights -/

/-- The row weight of a tabloid: each label contributes its entry scaled by its column in `t`. -/
def rowWeight (t : YoungTableau lam) (S : Tabloid mu) : ℕ :=
  ∑ i, t.column i * (S.rowOf i : ℕ)

/-- The column weight of a tabloid: each label contributes its entry scaled by its row in `t`. -/
def colWeight (t : YoungTableau lam) (S : Tabloid mu) : ℕ :=
  ∑ i, t.row i * (S.rowOf i : ℕ)

theorem rowWeight_smul (t : YoungTableau lam) (sigma : SymmetricGroup n) (S : Tabloid mu) :
    rowWeight t (sigma • S) = ∑ i, t.column (sigma i) * (S.rowOf i : ℕ) :=
  (Fintype.sum_equiv sigma _ _ fun i => by rw [Tabloid.smul_rowOf, show sigma⁻¹ (sigma i) = i from sigma.symm_apply_apply i]).symm

theorem colWeight_smul (t : YoungTableau lam) (sigma : SymmetricGroup n) (S : Tabloid mu) :
    colWeight t (sigma • S) = ∑ i, t.row (sigma i) * (S.rowOf i : ℕ) :=
  (Fintype.sum_equiv sigma _ _ fun i => by rw [Tabloid.smul_rowOf, show sigma⁻¹ (sigma i) = i from sigma.symm_apply_apply i]).symm

/-- A column permutation leaves the row weight alone. -/
theorem rowWeight_smul_of_mem_columnGroup (t : YoungTableau lam) {sigma : SymmetricGroup n}
    (hsigma : sigma ∈ t.columnGroup) (S : Tabloid mu) :
    rowWeight t (sigma • S) = rowWeight t S := by
  rw [rowWeight_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [hsigma i]

/-- A row permutation leaves the column weight alone. -/
theorem colWeight_smul_of_mem_rowGroup (t : YoungTableau lam) {sigma : SymmetricGroup n}
    (hsigma : sigma ∈ t.rowGroup) (S : Tabloid mu) :
    colWeight t (sigma • S) = colWeight t S := by
  rw [colWeight_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [hsigma i]

/-! ### Sorted representatives -/

/-- Inside a block of labels indexed by an initial segment of `ord`, a weakly increasing tabloid
puts the small entries first: the entry at `i` is at most `v` exactly when `ord i` is below the
number of block labels with entry at most `v`. -/
private theorem le_iff_ord_lt_card {blk ord : Fin n → ℕ}
    (hpair : Function.Injective fun i => (blk i, ord i))
    (hord : ∀ i, ord i < (univ.filter fun k => blk k = blk i).card)
    {S : Tabloid mu} (hS : ∀ i j, blk i = blk j → ord i < ord j → S.rowOf i ≤ S.rowOf j)
    (i : Fin n) (v : ℕ) :
    (S.rowOf i : ℕ) ≤ v ↔
      ord i < ((univ.filter fun k => blk k = blk i).filter
        fun k => (S.rowOf k : ℕ) ≤ v).card := by
  classical
  set P := univ.filter fun k => blk k = blk i with hPdef
  set Q := P.filter fun k => (S.rowOf k : ℕ) ≤ v with hQdef
  have hmemP : ∀ k, k ∈ P ↔ blk k = blk i := fun k => by simp [hPdef]
  have hmemQ : ∀ k, k ∈ Q ↔ blk k = blk i ∧ (S.rowOf k : ℕ) ≤ v := fun k => by
    simp [hQdef, hmemP]
  have hinj : Set.InjOn ord ↑P := fun a ha b hb hab =>
    hpair (Prod.ext (((hmemP a).mp ha).trans ((hmemP b).mp hb).symm) hab)
  have hordP : ∀ k ∈ P, ord k < P.card := fun k hk => by
    have hk' := hord k
    rwa [show (univ.filter fun m => blk m = blk k) = P from by rw [hPdef, (hmemP k).mp hk]] at hk'
  have himgP : P.image ord = range P.card := by
    refine Finset.eq_of_subset_of_card_le (fun a ha => ?_) ?_
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (hordP k hk)
    · rw [Finset.card_range, Finset.card_image_of_injOn hinj]
  have hstep : ∀ k ∈ Q, ord k < Q.card := by
    intro k hk
    have hsub : range (ord k + 1) ⊆ Q.image ord := by
      intro b hb
      have hbP : b ∈ P.image ord := by
        rw [himgP]
        exact Finset.mem_range.mpr
          (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
            (hordP k ((Finset.mem_filter.mp hk).1)))
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hbP
      refine Finset.mem_image.mpr ⟨m, (hmemQ m).mpr ⟨(hmemP m).mp hm, ?_⟩, rfl⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) with hlt | heq
      · exact le_trans (hS m k (((hmemP m).mp hm).trans ((hmemQ k).mp hk).1.symm) hlt)
          ((hmemQ k).mp hk).2
      · rw [hinj hm (Finset.mem_coe.mpr (Finset.mem_filter.mp hk).1) heq]
        exact ((hmemQ k).mp hk).2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range,
      Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast Finset.filter_subset _ _))] at hcard
    omega
  constructor
  · intro hv
    exact hstep i ((hmemQ i).mpr ⟨rfl, hv⟩)
  · intro hlt
    have himgQ : Q.image ord = range Q.card :=
      Finset.eq_of_subset_of_card_le
        (fun a ha => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
          exact Finset.mem_range.mpr (hstep k hk))
        (by
          rw [Finset.card_range,
            Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast Finset.filter_subset _ _))])
    have hmem : ord i ∈ Q.image ord := by rw [himgQ]; exact Finset.mem_range.mpr hlt
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hmem
    rw [hinj (Finset.mem_coe.mpr (Finset.mem_filter.mp hk).1)
      (Finset.mem_coe.mpr ((hmemP i).mpr rfl)) hki] at hk
    exact ((hmemQ i).mp hk).2

/-- A tabloid that increases weakly along each block of `blk` is the only such tabloid in its orbit
under the permutations preserving `blk`. -/
private theorem tabloid_eq_of_sorted {blk ord : Fin n → ℕ}
    (hpair : Function.Injective fun i => (blk i, ord i))
    (hord : ∀ i, ord i < (univ.filter fun k => blk k = blk i).card)
    {S : Tabloid mu} {g : SymmetricGroup n} (hg : ∀ i, blk (g i) = blk i)
    (hS : ∀ i j, blk i = blk j → ord i < ord j → S.rowOf i ≤ S.rowOf j)
    (hgS : ∀ i j, blk i = blk j → ord i < ord j → (g • S).rowOf i ≤ (g • S).rowOf j) :
    g • S = S := by
  classical
  have hcount : ∀ (i : Fin n) (v : ℕ),
      ((univ.filter fun k => blk k = blk i).filter fun k => (S.rowOf k : ℕ) ≤ v).card =
        ((univ.filter fun k => blk k = blk i).filter
          fun k => ((g • S).rowOf k : ℕ) ≤ v).card := by
    intro i v
    refine Finset.card_bijective g g.bijective fun k => ?_
    simp [Tabloid.smul_rowOf, hg k]
  refine Tabloid.ext (funext fun i => Fin.ext (le_antisymm ?_ ?_))
  · rw [le_iff_ord_lt_card hpair hord hgS i, ← hcount i,
      ← le_iff_ord_lt_card hpair hord hS i]
  · rw [le_iff_ord_lt_card hpair hord hS i, hcount i,
      ← le_iff_ord_lt_card hpair hord hgS i]

/-- Row `r` of a tableau holds `lam.rowLen r` labels. -/
theorem card_filter_row_eq (t : YoungTableau lam) (r : ℕ) :
    (univ.filter fun k => t.row k = r).card = lam.val.rowLen r := by
  rw [← t.tabloid.content r]
  exact congrArg Finset.card (Finset.filter_congr fun k _ => by rw [t.tabloid_rowOf])

/-- Sorting the rows of `t` increasingly picks out one tabloid from each row-group orbit. -/
theorem eq_of_rowIncreasing {t : YoungTableau lam} {S : Tabloid mu} {sigma : SymmetricGroup n}
    (hsigma : sigma ∈ t.rowGroup) (hS : RowIncreasing t S)
    (hsigmaS : RowIncreasing t (sigma • S)) : sigma • S = S :=
  tabloid_eq_of_sorted t.row_column_injective
    (fun i => by rw [card_filter_row_eq]; exact t.column_lt_rowLen i)
    (mem_rowGroup.mp hsigma) hS hsigmaS

/-- Sorting the columns of `t` increasingly picks out one tabloid from each column-group orbit. -/
theorem eq_of_colStrict {t : YoungTableau lam} {S : Tabloid mu} {pi : SymmetricGroup n}
    (hpi : pi ∈ t.columnGroup) (hS : ColStrict t S) (hpiS : ColStrict t (pi • S)) :
    pi • S = S :=
  tabloid_eq_of_sorted
    (fun a b hab => t.row_column_injective (Prod.ext (congrArg Prod.snd hab)
      (congrArg Prod.fst hab)))
    (fun i => by rw [t.card_filter_column_eq]; exact t.row_lt_colLen i)
    (mem_columnGroup.mp hpi)
    (fun i j hcol hrow => (hS i j hcol hrow).le)
    (fun i j hcol hrow => (hpiS i j hcol hrow).le)

/-! ### Descents raise a weight -/

/-- Swapping a larger factor onto a larger value increases the pairing. -/
private theorem mul_add_mul_lt {c₁ c₂ a b : ℕ} (hc : c₁ < c₂) (hab : b < a) :
    c₁ * a + c₂ * b < c₂ * a + c₁ * b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hc
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hab
  nlinarith

/-- Transposing two labels whose weights and entries are oppositely ordered raises the pairing of
the weights against the entries. -/
private theorem sum_swap_lt {w : Fin n → ℕ} {S : Tabloid mu} {i j : Fin n}
    (hw : w i < w j) (hval : S.rowOf j < S.rowOf i) :
    ∑ k, w k * (S.rowOf k : ℕ) < ∑ k, w (Equiv.swap i j k) * (S.rowOf k : ℕ) := by
  classical
  have hij : i ≠ j := fun h => absurd hw (by rw [h]; exact lt_irrefl _)
  have hsplit : ∀ f : Fin n → ℕ,
      ∑ k, f k = ∑ k ∈ univ \ ({i, j} : Finset (Fin n)), f k + (f i + f j) := fun f => by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({i, j} : Finset (Fin n))), Finset.sum_pair hij]
  have hrest : ∀ k ∈ univ \ ({i, j} : Finset (Fin n)),
      w (Equiv.swap i j k) * (S.rowOf k : ℕ) = w k * (S.rowOf k : ℕ) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [Equiv.swap_apply_of_ne_of_ne hk.2.1 hk.2.2]
  rw [hsplit fun k => w k * (S.rowOf k : ℕ), hsplit fun k => w (Equiv.swap i j k) * (S.rowOf k : ℕ),
    Finset.sum_congr rfl hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact Nat.add_lt_add_left (mul_add_mul_lt hw hval) _

/-- Transposing two labels of one row of `t` keeps every label in its row. -/
theorem swap_mem_rowGroup {t : YoungTableau lam} {i j : Fin n} (hrow : t.row i = t.row j) :
    Equiv.swap i j ∈ t.rowGroup := by
  intro k
  rcases eq_or_ne k i with rfl | hki
  · rw [Equiv.swap_apply_left, hrow]
  · rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right, hrow]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Transposing two labels of one column of `t` keeps every label in its column. -/
theorem swap_mem_columnGroup {t : YoungTableau lam} {i j : Fin n}
    (hcol : t.column i = t.column j) : Equiv.swap i j ∈ t.columnGroup := by
  intro k
  rcases eq_or_ne k i with rfl | hki
  · rw [Equiv.swap_apply_left, hcol]
  · rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right, hcol]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- A descent along a row of `t` is removed by a transposition that raises the row weight. -/
theorem rowWeight_lt_swap (t : YoungTableau lam) (S : Tabloid mu) {i j : Fin n}
    (hcol : t.column i < t.column j) (hval : S.rowOf j < S.rowOf i) :
    rowWeight t S < rowWeight t (Equiv.swap i j • S) := by
  rw [rowWeight_smul]
  exact sum_swap_lt hcol hval

/-- A descent down a column of `t` is removed by a transposition that raises the column weight. -/
theorem colWeight_lt_swap (t : YoungTableau lam) (S : Tabloid mu) {i j : Fin n}
    (hrow : t.row i < t.row j) (hval : S.rowOf j < S.rowOf i) :
    colWeight t S < colWeight t (Equiv.swap i j • S) := by
  rw [colWeight_smul]
  exact sum_swap_lt hrow hval

/-! ### The row weight is maximal at the increasing representative -/

/-- A tabloid of maximal row weight in its row-group orbit increases weakly along the rows. -/
private theorem rowIncreasing_of_maximal (t : YoungTableau lam) {T : Tabloid mu}
    (hmax : ∀ sigma ∈ t.rowGroup, rowWeight t (sigma • T) ≤ rowWeight t T) :
    RowIncreasing t T := by
  intro i j hrow hcol
  by_contra hle
  exact absurd (hmax _ (swap_mem_rowGroup hrow))
    (not_le.mpr (rowWeight_lt_swap t T hcol (not_le.mp hle)))

/-- Permuting inside the rows of `t` cannot raise the row weight of a row-increasing tabloid. -/
theorem rowWeight_smul_le (t : YoungTableau lam) {S : Tabloid mu} (hS : RowIncreasing t S)
    {sigma : SymmetricGroup n} (hsigma : sigma ∈ t.rowGroup) :
    rowWeight t (sigma • S) ≤ rowWeight t S := by
  obtain ⟨rho, -, hmax⟩ := Finset.exists_max_image (univ : Finset t.rowGroup)
    (fun r => rowWeight t ((r : SymmetricGroup n) • S)) ⟨1, mem_univ 1⟩
  have hrho : RowIncreasing t ((rho : SymmetricGroup n) • S) := by
    refine rowIncreasing_of_maximal t fun tau htau => ?_
    have hstep := hmax ⟨tau * (rho : SymmetricGroup n), t.rowGroup.mul_mem htau rho.2⟩ (mem_univ _)
    rwa [show (tau * (rho : SymmetricGroup n)) • S = tau • ((rho : SymmetricGroup n) • S) from
      mul_smul _ _ _] at hstep
  have hle := hmax ⟨sigma, hsigma⟩ (mem_univ _)
  rwa [eq_of_rowIncreasing rho.2 hS hrho] at hle

/-- Permuting inside the rows of `t` strictly lowers the row weight of a row-increasing tabloid,
unless it leaves the tabloid alone. -/
theorem eq_of_rowWeight_smul_eq (t : YoungTableau lam) {S : Tabloid mu} (hS : RowIncreasing t S)
    {sigma : SymmetricGroup n} (hsigma : sigma ∈ t.rowGroup)
    (hweight : rowWeight t (sigma • S) = rowWeight t S) : sigma • S = S := by
  refine eq_of_rowIncreasing hsigma hS (rowIncreasing_of_maximal t fun tau htau => ?_)
  rw [← mul_smul, hweight]
  exact rowWeight_smul_le t hS (t.rowGroup.mul_mem htau hsigma)

/-! ### The Garnir relation -/

/-- **Garnir's relation, in antisymmetriser form.**  If `A` holds labels from column `c` of `t`,
`B` holds labels from column `c + 1`, and together they outnumber the length of column `c`, then
antisymmetrising over the permutations of `A ∪ B` annihilates the polytabloid of `t`.

This is Sagan, *The Symmetric Group*, 2nd ed., Proposition 2.6.3, equation (2.4).  Every tabloid of
`e_t` is a column permutation of the tabloid of `t`, and a column permutation keeps the labels of
`A ∪ B` inside the first `lam.colLen c` rows, where there are too many of them to occupy distinct
rows.  No Garnir element and no transversal appears: the full antisymmetriser suffices. -/
theorem blockAntisymmetriser_polytabloid (t : YoungTableau lam) {A B : Finset (Fin n)} {c : ℕ}
    (hA : ∀ a ∈ A, t.column a = c) (hB : ∀ b ∈ B, t.column b = c + 1)
    (hcard : lam.val.colLen c < (A ∪ B).card) :
    blockAntisymmetriser (A ∪ B) lam (polytabloid t) = 0 := by
  rw [polytabloid, map_sum]
  refine Finset.sum_eq_zero fun pi _ => ?_
  have hrows : ∀ x ∈ A ∪ B, t.row ((pi : SymmetricGroup n)⁻¹ x) < lam.val.colLen c := by
    intro x hx
    have hcolumn : t.column ((pi : SymmetricGroup n)⁻¹ x) = t.column x :=
      t.columnGroup.inv_mem pi.2 x
    rcases Finset.mem_union.mp hx with h | h
    · rw [← hA x h, ← hcolumn]
      exact t.row_lt_colLen _
    · refine lt_of_lt_of_le ?_ (lam.val.colLen_anti c (c + 1) (Nat.le_succ c))
      rw [← hB x h, ← hcolumn]
      exact t.row_lt_colLen _
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (f := fun x => t.row ((pi : SymmetricGroup n)⁻¹ x))
      (by rwa [Finset.card_range]) fun x hx => Finset.mem_range.mpr (hrows x hx)
  have hzero : blockAntisymmetriser (A ∪ B) lam
      (Finsupp.single ((pi : SymmetricGroup n) • t.tabloid) 1) = 0 :=
    blockAntisymmetriser_single_eq_zero hx hy hxy (Fin.ext (by
      rw [Tabloid.smul_rowOf, Tabloid.smul_rowOf, t.tabloid_rowOf, t.tabloid_rowOf]
      exact heq))
  rw [map_smul, hzero, smul_zero]

/-! ### The semistandard homomorphisms -/

/-- The sum of the tabloids reachable from `S0` by a relabelling that carries the tabloid of `t`
to `U`.

Reading the slice off the orbit relation rather than off a coset representative makes
equivariance the substitution `sigma ↦ tau⁻¹ * sigma`. -/
noncomputable def orbitVector (t : YoungTableau lam) (S0 : Tabloid mu) (U : Tabloid lam) :
    Tabloid mu →₀ ℂ :=
  Finsupp.equivFunOnFinite.symm
    (Set.indicator {S | ∃ sigma : SymmetricGroup n, sigma • t.tabloid = U ∧ sigma • S0 = S} 1)

theorem orbitVector_apply_eq_one (t : YoungTableau lam) (S0 : Tabloid mu) (U : Tabloid lam)
    (S : Tabloid mu) (h : ∃ sigma : SymmetricGroup n, sigma • t.tabloid = U ∧ sigma • S0 = S) :
    orbitVector t S0 U S = 1 :=
  Set.indicator_of_mem h 1

theorem orbitVector_apply_eq_zero (t : YoungTableau lam) (S0 : Tabloid mu) (U : Tabloid lam)
    (S : Tabloid mu) (h : ¬ ∃ sigma : SymmetricGroup n, sigma • t.tabloid = U ∧ sigma • S0 = S) :
    orbitVector t S0 U S = 0 :=
  Set.indicator_of_notMem h 1

theorem orbitVector_smul (t : YoungTableau lam) (S0 : Tabloid mu) (tau : SymmetricGroup n)
    (U : Tabloid lam) :
    orbitVector t S0 (tau • U) =
      Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu) tau (orbitVector t S0 U) := by
  refine Finsupp.ext fun S => ?_
  rw [Representation.ofMulAction_apply]
  by_cases h : ∃ sigma : SymmetricGroup n, sigma • t.tabloid = U ∧ sigma • S0 = tau⁻¹ • S
  · obtain ⟨sigma, hfix, hval⟩ := h
    rw [orbitVector_apply_eq_one t S0 U _ ⟨sigma, hfix, hval⟩,
      orbitVector_apply_eq_one t S0 _ S
        ⟨tau * sigma, by rw [mul_smul, hfix], by rw [mul_smul, hval, smul_inv_smul]⟩]
  · rw [orbitVector_apply_eq_zero t S0 U _ h, orbitVector_apply_eq_zero t S0 _ S]
    rintro ⟨sigma, hfix, hval⟩
    exact h ⟨tau⁻¹ * sigma, by rw [mul_smul, hfix, inv_smul_smul], by rw [mul_smul, hval]⟩

/-- The map of Young permutation modules attached to a tabloid `S0` of shape `mu`.

This is Sagan, *The Symmetric Group*, 2nd ed., Definition 2.9.3. -/
noncomputable def semistandardMap (t : YoungTableau lam) (S0 : Tabloid mu) :
    (Tabloid lam →₀ ℂ) →ₗ[ℂ] (Tabloid mu →₀ ℂ) :=
  Finsupp.linearCombination ℂ (orbitVector t S0)

theorem semistandardMap_ofMulAction (t : YoungTableau lam) (S0 : Tabloid mu)
    (tau : SymmetricGroup n) (v : Tabloid lam →₀ ℂ) :
    semistandardMap t S0
        (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid lam) tau v) =
      Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu) tau
        (semistandardMap t S0 v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single U c =>
      rw [Representation.ofMulAction_single, semistandardMap, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, orbitVector_smul, map_smul]

/-- The polytabloid of `t`, viewed inside the Specht module. -/
noncomputable def spechtPolytabloid (t : YoungTableau lam) : (spechtModule lam : Type) :=
  ⟨polytabloid t, Submodule.subset_span ⟨t, rfl⟩⟩

/-- The semistandard homomorphism `S^lam ⟶ M^mu` attached to a tabloid `S0` of shape `mu`. -/
noncomputable def semistandardHom (t : YoungTableau lam) (S0 : Tabloid mu) :
    spechtModule lam ⟶ youngPermutationModule mu :=
  (FDRep.homEquivIntertwiningMap (spechtModule lam) (youngPermutationModule mu)).symm
    (LinearMap.intertwiningMap_of_isIntertwiningMap
      (spechtSubrepresentation lam).toRepresentation
      (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu))
      ((semistandardMap t S0).comp (spechtSubrepresentation lam).toSubmodule.subtype)
      fun tau v => semistandardMap_ofMulAction t S0 tau (v : Tabloid lam →₀ ℂ))

@[simp]
theorem semistandardHom_polytabloid (t : YoungTableau lam) (S0 : Tabloid mu) :
    FDRep.homEquivIntertwiningMap (spechtModule lam) (youngPermutationModule mu)
        (semistandardHom t S0) (spechtPolytabloid t) = semistandardMap t S0 (polytabloid t) := by
  rw [semistandardHom, LinearEquiv.apply_symm_apply]
  rfl

/-! ### The coefficient matrix of the semistandard homomorphisms -/

/-- A relabelling carrying the tabloid of `t` where a column permutation carries it is that column
permutation followed by a row permutation. -/
theorem exists_smul_tabloid_iff (t : YoungTableau lam) (pi : SymmetricGroup n)
    (S0 S1 : Tabloid mu) :
    (∃ sigma : SymmetricGroup n, sigma • t.tabloid = pi • t.tabloid ∧ sigma • S0 = S1) ↔
      ∃ rho ∈ t.rowGroup, (pi * rho) • S0 = S1 := by
  constructor
  · rintro ⟨sigma, hfix, hval⟩
    refine ⟨pi⁻¹ * sigma, (smul_tabloid_eq_iff_mem_rowGroup t _).mp ?_, ?_⟩
    · rw [mul_smul, hfix, inv_smul_smul]
    · rw [← mul_assoc, mul_inv_cancel, one_mul, hval]
  · rintro ⟨rho, hrho, hval⟩
    exact ⟨pi * rho, by rw [mul_smul, (smul_tabloid_eq_iff_mem_rowGroup t rho).mpr hrho], hval⟩

/-- Semistandard tabloids are rigid: if a column permutation followed by a row permutation carries
one semistandard tabloid to another of at least the same row weight, both permutations act
trivially and the two tabloids agree.

The row permutation cannot raise the row weight, so it must fix `S0`; the column permutation then
carries one column-strict tabloid to another, so it too must fix `S0`; and a column permutation
fixing a column-strict tabloid is the identity. -/
theorem eq_and_eq_one_of_smul_eq (t : YoungTableau lam) {S0 S1 : Tabloid mu}
    (hS0 : Semistandard t S0) (hS1 : Semistandard t S1)
    (hweight : rowWeight t S0 ≤ rowWeight t S1)
    {pi rho : SymmetricGroup n} (hpi : pi ∈ t.columnGroup) (hrho : rho ∈ t.rowGroup)
    (hval : (pi * rho) • S0 = S1) : S1 = S0 ∧ pi = 1 := by
  have hchain : rowWeight t S1 = rowWeight t (rho • S0) := by
    rw [← hval, mul_smul, rowWeight_smul_of_mem_columnGroup t hpi]
  have hfixrho : rho • S0 = S0 :=
    eq_of_rowWeight_smul_eq t hS0.1 hrho
      (le_antisymm (rowWeight_smul_le t hS0.1 hrho) (hchain ▸ hweight))
  have hpiS : pi • S0 = S1 := by rw [← hval, mul_smul, hfixrho]
  have hfixpi : pi • S0 = S0 := eq_of_colStrict hpi hS0.2 (by rw [hpiS]; exact hS1.2)
  refine ⟨by rw [← hpiS, hfixpi], Equiv.ext fun m => ?_⟩
  have hrowOf : S0.rowOf (pi m) = S0.rowOf m := by
    have hvalue := congrArg (fun T : Tabloid mu => T.rowOf (pi m)) hfixpi
    simpa using hvalue.symm
  exact hS0.2.injective (Prod.ext (hpi m) hrowOf)

/-- The coefficients of the semistandard homomorphism at the polytabloid of `t`. -/
theorem semistandardMap_polytabloid (t : YoungTableau lam) (S0 S1 : Tabloid mu) :
    semistandardMap t S0 (polytabloid t) S1 =
      ∑ pi : t.columnGroup, ((Equiv.Perm.sign (pi : SymmetricGroup n) : ℤ) : ℂ) *
        orbitVector t S0 ((pi : SymmetricGroup n) • t.tabloid) S1 := by
  have hsingle : ∀ U : Tabloid lam,
      semistandardMap t S0 (Finsupp.single U 1) = orbitVector t S0 U := fun U => by
    rw [semistandardMap, Finsupp.linearCombination_single, one_smul]
  rw [polytabloid, map_sum, Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun pi _ => by
    rw [map_smul, Finsupp.smul_apply, hsingle, smul_eq_mul]

/-- The semistandard homomorphism attached to `S0` has coefficient one at `S0`. -/
theorem semistandardMap_polytabloid_self (t : YoungTableau lam) {S0 : Tabloid mu}
    (hS0 : Semistandard t S0) : semistandardMap t S0 (polytabloid t) S0 = 1 := by
  rw [semistandardMap_polytabloid]
  refine (Finset.sum_eq_single (1 : t.columnGroup) (fun pi _ hne => ?_) fun h =>
    absurd (Finset.mem_univ _) h).trans ?_
  · rw [orbitVector_apply_eq_zero, mul_zero]
    rw [exists_smul_tabloid_iff]
    rintro ⟨rho, hrho, hval⟩
    exact hne (Subtype.ext (eq_and_eq_one_of_smul_eq t hS0 hS0 le_rfl pi.2 hrho hval).2)
  · rw [orbitVector_apply_eq_one t S0 _ S0
      ⟨((1 : t.columnGroup) : SymmetricGroup n), rfl, by simp⟩]
    simp

/-- The semistandard homomorphism attached to `S0` vanishes at every other semistandard tabloid of
at least the same row weight. -/
theorem semistandardMap_polytabloid_of_ne (t : YoungTableau lam) {S0 S1 : Tabloid mu}
    (hS0 : Semistandard t S0) (hS1 : Semistandard t S1)
    (hweight : rowWeight t S0 ≤ rowWeight t S1) (hne : S1 ≠ S0) :
    semistandardMap t S0 (polytabloid t) S1 = 0 := by
  rw [semistandardMap_polytabloid]
  refine Finset.sum_eq_zero fun pi _ => ?_
  rw [orbitVector_apply_eq_zero, mul_zero]
  rw [exists_smul_tabloid_iff]
  rintro ⟨rho, hrho, hval⟩
  exact hne (eq_and_eq_one_of_smul_eq t hS0 hS1 hweight pi.2 hrho hval).1

/-! ### The upper bound -/

/-- Weak increase between adjacent columns propagates along a row. -/
theorem rowIncreasing_of_adjacent (t : YoungTableau lam) (S : Tabloid mu)
    (h : ∀ i j, t.row i = t.row j → t.column j = t.column i + 1 → S.rowOf i ≤ S.rowOf j) :
    RowIncreasing t S := by
  have hstep : ∀ (k : ℕ) (a b : Fin n), t.row a = t.row b → t.column b = t.column a + k →
      S.rowOf a ≤ S.rowOf b := by
    intro k
    induction k with
    | zero =>
        intro a b hrow hcol
        rw [Nat.add_zero] at hcol
        rw [t.row_column_injective (Prod.ext hrow hcol.symm)]
    | succ k ih =>
        intro a b hrow hcol
        have hlen : t.column a + k < lam.val.rowLen (t.row a) := by
          have hb := t.column_lt_rowLen b
          rw [← hrow] at hb
          omega
        have hcell : (t.row a, t.column a + k) ∈ lam.val.cells :=
          YoungDiagram.mem_iff_lt_rowLen.mpr hlen
        -- the label between `a` and `b` sits in the same row, one column before `b`
        refine le_trans (ih a (t ⟨(t.row a, t.column a + k), hcell⟩) ?_ ?_) (h _ b ?_ ?_)
        · rw [t.row_apply]
        · rw [t.column_apply]
        · rw [t.row_apply]
          exact hrow
        · rw [t.column_apply]
          omega
  intro i j hrow hcol
  exact hstep (t.column j - t.column i) i j hrow (by omega)

/-- The labels of `t` in column `c` at row `r` or below. -/
private def lowerBlock (t : YoungTableau lam) (r c : ℕ) : Finset (Fin n) :=
  univ.filter fun a => t.column a = c ∧ r ≤ t.row a

/-- The labels of `t` in column `c + 1` at row `r` or above. -/
private def upperBlock (t : YoungTableau lam) (r c : ℕ) : Finset (Fin n) :=
  univ.filter fun b => t.column b = c + 1 ∧ t.row b ≤ r

private theorem mem_lowerBlock {t : YoungTableau lam} {r c : ℕ} {a : Fin n} :
    a ∈ lowerBlock t r c ↔ t.column a = c ∧ r ≤ t.row a := by
  simp [lowerBlock]

private theorem mem_upperBlock {t : YoungTableau lam} {r c : ℕ} {b : Fin n} :
    b ∈ upperBlock t r c ↔ t.column b = c + 1 ∧ t.row b ≤ r := by
  simp [upperBlock]

private theorem disjoint_lowerBlock_upperBlock (t : YoungTableau lam) (r c : ℕ) :
    Disjoint (lowerBlock t r c) (upperBlock t r c) := by
  refine Finset.disjoint_left.mpr fun a ha hb => ?_
  have hlow := (mem_lowerBlock.mp ha).1
  have hup := (mem_upperBlock.mp hb).1
  omega

/-- The two blocks at a row descent hold one more label than column `c` is long. -/
private theorem colLen_lt_card_block (t : YoungTableau lam) {i j : Fin n}
    (hrow : t.row i = t.row j) (hcol : t.column j = t.column i + 1) :
    lam.val.colLen (t.column i) <
      (lowerBlock t (t.row i) (t.column i) ∪ upperBlock t (t.row i) (t.column i)).card := by
  set r := t.row i with hr
  set c := t.column i with hc
  have hlower : (lowerBlock t r c).card + r = lam.val.colLen c := by
    have hsub : (univ.filter fun a => t.row a < r ∧ t.column a = c) ⊆
        univ.filter fun a => t.column a = c := fun a ha => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.2
    have hdiff : (univ.filter fun a => t.column a = c) \
        (univ.filter fun a => t.row a < r ∧ t.column a = c) = lowerBlock t r c := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, mem_lowerBlock]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by by_contra hlt; exact h2 ⟨not_le.mp hlt, h1⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h3 => absurd h3.1 (by omega)⟩
    have hcards := Finset.card_sdiff_add_card_eq_card hsub
    rw [hdiff, t.card_filter_row_lt_and_column_eq r c, t.card_filter_column_eq c,
      min_eq_right (le_of_lt (hr ▸ t.row_lt_colLen i))] at hcards
    exact hcards
  have hupper : (upperBlock t r c).card = r + 1 := by
    have hcards := t.card_filter_row_lt_and_column_eq (r + 1) (c + 1)
    rw [min_eq_right (by have := hrow ▸ hcol ▸ t.row_lt_colLen j; omega)] at hcards
    rw [← hcards]
    exact congrArg Finset.card (Finset.filter_congr fun a _ =>
      ⟨fun h => ⟨by omega, h.1⟩, fun h => ⟨h.2, by omega⟩⟩)
  rw [Finset.card_union_of_disjoint (disjoint_lowerBlock_upperBlock t r c), hupper]
  omega

/-- A block permutation that preserves the upper block preserves every column of `t`. -/
private theorem mem_columnGroup_of_preserves_upperBlock (t : YoungTableau lam) {r c : ℕ}
    {tau : SymmetricGroup n} (htau : tau ∈ blockGroup (lowerBlock t r c ∪ upperBlock t r c))
    (hpres : ∀ a, tau a ∈ upperBlock t r c ↔ a ∈ upperBlock t r c) : tau ∈ t.columnGroup := by
  intro k
  by_cases hk : k ∈ lowerBlock t r c ∪ upperBlock t r c
  · have himage := blockGroup.mapsTo htau hk
    rcases Finset.mem_union.mp hk with hlow | hup
    · have hnot : tau k ∉ upperBlock t r c := fun h =>
        Finset.disjoint_left.mp (disjoint_lowerBlock_upperBlock t r c) hlow ((hpres k).mp h)
      rw [(mem_lowerBlock.mp ((Finset.mem_union.mp himage).resolve_right hnot)).1,
        (mem_lowerBlock.mp hlow).1]
    · rw [(mem_upperBlock.mp ((hpres k).mpr hup)).1, (mem_upperBlock.mp hup).1]
  · rw [mem_blockGroup.mp htau k hk]

/-- **The heart of Sagan's Lemma 2.10.7(3).**  At a row descent, permuting the two blocks strictly
raises the row weight unless the permutation preserves each block.

The lower block carries entries at least that of `i`, the upper block entries at most that of `j`,
and the descent puts the entry of `j` below that of `i`.  Moving a label into the upper block
therefore trades a small entry for a large one in the column that scores. -/
private theorem rowWeight_lt_of_mem_blockGroup (t : YoungTableau lam) {S : Tabloid mu}
    (hS : ColStrict t S) {i j : Fin n} (hrow : t.row i = t.row j)
    (hcol : t.column j = t.column i + 1) (hval : S.rowOf j < S.rowOf i)
    {tau : SymmetricGroup n}
    (htau : tau ∈ blockGroup (lowerBlock t (t.row i) (t.column i) ∪
      upperBlock t (t.row i) (t.column i)))
    (hne : ¬ ∀ a, tau a ∈ upperBlock t (t.row i) (t.column i) ↔
      a ∈ upperBlock t (t.row i) (t.column i)) :
    rowWeight t S < rowWeight t (tau • S) := by
  classical
  set r := t.row i with hr
  set c := t.column i with hc
  set A := lowerBlock t r c with hA
  set B := upperBlock t r c with hB
  set Z := univ.filter fun k => tau k ∈ B with hZ
  -- moving a label between the blocks shifts its column by exactly one
  have hshift : ∀ k, t.column (tau k) + (if k ∈ B then 1 else 0) =
      t.column k + (if tau k ∈ B then 1 else 0) := by
    intro k
    by_cases hk : k ∈ A ∪ B
    · have himage := blockGroup.mapsTo htau hk
      have hcolumn : ∀ a ∈ A ∪ B, t.column a = if a ∈ B then c + 1 else c := by
        intro a ha
        rcases Finset.mem_union.mp ha with hlow | hup
        · rw [if_neg (Finset.disjoint_left.mp (disjoint_lowerBlock_upperBlock t r c) hlow),
            (mem_lowerBlock.mp hlow).1]
        · rw [if_pos hup, (mem_upperBlock.mp hup).1]
      rw [hcolumn k hk, hcolumn (tau k) himage]
      by_cases h1 : k ∈ B <;> by_cases h2 : tau k ∈ B <;> simp [h1, h2]
    · rw [mem_blockGroup.mp htau k hk]
  -- so the row weights differ by the entries carried in and out of the upper block
  have hsum : rowWeight t (tau • S) + ∑ k ∈ B, (S.rowOf k : ℕ) =
      rowWeight t S + ∑ k ∈ Z, (S.rowOf k : ℕ) := by
    have hboth := Finset.sum_congr rfl fun k (_ : k ∈ (univ : Finset (Fin n))) => by
      simpa [add_mul, ite_mul] using congrArg (fun m => m * (S.rowOf k : ℕ)) (hshift k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.filter_univ_mem, ← rowWeight_smul t tau S] at hboth
    exact hboth
  -- the two blocks separate the entries of `S`
  have hlow : ∀ a ∈ A, (S.rowOf i : ℕ) ≤ (S.rowOf a : ℕ) := by
    intro a ha
    obtain ⟨hcolumn, hrowle⟩ := mem_lowerBlock.mp ha
    rcases eq_or_lt_of_le hrowle with heq | hlt
    · rw [t.row_column_injective (Prod.ext (heq.symm.trans hr) (hcolumn.trans hc))]
    · exact le_of_lt (hS i a (hc.symm.trans hcolumn.symm) hlt)
  have hup : ∀ b ∈ B, (S.rowOf b : ℕ) ≤ (S.rowOf j : ℕ) := by
    intro b hb
    obtain ⟨hcolumn, hrowle⟩ := mem_upperBlock.mp hb
    rcases eq_or_lt_of_le hrowle with heq | hlt
    · rw [t.row_column_injective (Prod.ext (heq.trans hrow) (hcolumn.trans hcol.symm))]
    · exact le_of_lt (hS b j (hcolumn.trans hcol.symm) (hrow ▸ hlt))
  -- the labels moved into the upper block come from the lower one
  have hZX : Z ⊆ A ∪ B := by
    intro k hk
    by_contra hout
    exact hout ((mem_blockGroup.mp htau k hout) ▸
      Finset.mem_union_right A (Finset.mem_filter.mp hk).2)
  have hZB : Z \ B ⊆ A := fun k hk =>
    (Finset.mem_union.mp (hZX (Finset.mem_sdiff.mp hk).1)).resolve_right (Finset.mem_sdiff.mp hk).2
  have hcards : Z.card = B.card := Finset.card_bijective tau tau.bijective fun k => by
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsdiff : (Z \ B).card = (B \ Z).card := Finset.card_sdiff_comm hcards
  have hpos : 0 < (Z \ B).card := by
    rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : Z ⊆ B := fun k hk => by
      by_contra hkB
      exact absurd (Finset.mem_sdiff.mpr ⟨hk, hkB⟩) (hempty ▸ Finset.notMem_empty k)
    refine hne fun a => ?_
    have hiff := Finset.ext_iff.mp (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcards.symm)) a
    simpa only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] using hiff
  -- the entries entering the upper block outweigh those leaving it
  have hstrict : ∑ k ∈ B \ Z, (S.rowOf k : ℕ) < ∑ k ∈ Z \ B, (S.rowOf k : ℕ) :=
    calc ∑ k ∈ B \ Z, (S.rowOf k : ℕ) ≤ (B \ Z).card * (S.rowOf j : ℕ) := by
          simpa using Finset.sum_le_card_nsmul _ _ _ fun k hk => hup k (Finset.mem_sdiff.mp hk).1
      _ < (Z \ B).card * (S.rowOf i : ℕ) := by
          rw [hsdiff]
          exact Nat.mul_lt_mul_of_pos_left (by exact_mod_cast hval) (hsdiff ▸ hpos)
      _ ≤ ∑ k ∈ Z \ B, (S.rowOf k : ℕ) := by
          simpa using Finset.card_nsmul_le_sum _ _ _ fun k hk => hlow k (hZB hk)
  have hsplitB := Finset.sum_inter_add_sum_diff B Z fun k => (S.rowOf k : ℕ)
  have hsplitZ := Finset.sum_inter_add_sum_diff Z B fun k => (S.rowOf k : ℕ)
  rw [Finset.inter_comm] at hsplitZ
  omega

/-- **Sagan's Lemma 2.10.7.**  If an equivariant map out of the Specht module does not kill the
polytabloid of `t`, then its value there has a nonzero coefficient at a semistandard tabloid.

Among the tabloids of largest row weight in the support, take one of largest column weight.  A
column descent would be removed by a transposition of the column group, which reverses the sign of
the coefficient while raising the column weight.  A row descent would contradict the Garnir
relation, which rewrites the coefficient at the maximiser as a positive multiple of itself. -/
theorem exists_semistandard_apply_ne_zero (t : YoungTableau lam)
    (F : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu)))
    (hF : F (spechtPolytabloid t) ≠ 0) :
    ∃ S : Tabloid mu, Semistandard t S ∧ F (spechtPolytabloid t) S ≠ 0 := by
  classical
  set x := F (spechtPolytabloid t) with hxdef
  have hsq : ∀ sigma : SymmetricGroup n,
      ((Equiv.Perm.sign sigma : ℤ) : ℂ) * ((Equiv.Perm.sign sigma : ℤ) : ℂ) = 1 := fun sigma => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign sigma) with hone | hone <;> rw [hone] <;> norm_num
  -- the value is a sign eigenvector for the column group of `t`
  have hsign : ∀ pi ∈ t.columnGroup, ∀ S : Tabloid mu,
      x (pi • S) = ((Equiv.Perm.sign pi : ℤ) : ℂ) * x S := by
    intro pi hpi S
    have heigen : Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu) pi x =
        ((Equiv.Perm.sign pi : ℤ) : ℂ) • x := by
      rw [hxdef, ← F.isIntertwining,
        show (spechtSubrepresentation lam).toRepresentation pi (spechtPolytabloid t) =
          ((Equiv.Perm.sign pi : ℤ) : ℂ) • spechtPolytabloid t from
          Subtype.ext (smul_polytabloid_of_mem_columnGroup t hpi), map_smul]
    have hval := congrArg (fun y : Tabloid mu →₀ ℂ => y (pi • S)) heigen
    simp only [Representation.ofMulAction_apply, inv_smul_smul, Finsupp.smul_apply,
      smul_eq_mul] at hval
    rw [hval, ← mul_assoc, hsq, one_mul]
  -- two labels of one column of `t` sharing a row of `S` kill the coefficient at `S`
  have hcolzero : ∀ (S : Tabloid mu) (a b : Fin n), a ≠ b → t.column a = t.column b →
      S.rowOf a = S.rowOf b → x S = 0 := by
    intro S a b hab hcol hrowOf
    have hfix : Equiv.swap a b • S = S := by
      refine Tabloid.ext (funext fun i => ?_)
      rw [Tabloid.smul_rowOf, Equiv.swap_inv]
      rcases eq_or_ne i a with rfl | hia
      · rw [Equiv.swap_apply_left, hrowOf]
      · rcases eq_or_ne i b with rfl | hib
        · rw [Equiv.swap_apply_right, hrowOf]
        · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
    have hself := hsign (Equiv.swap a b) (swap_mem_columnGroup hcol) S
    rw [hfix, Equiv.Perm.sign_swap hab] at hself
    have htwo : (2 : ℂ) * x S = 0 := by push_cast at hself; linear_combination hself
    exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
  -- the Garnir relation transports along `F`
  have hblock : ∀ X : Finset (Fin n), blockAntisymmetriser X lam (polytabloid t) = 0 →
      blockAntisymmetriser X mu x = 0 := by
    intro X hzero
    have hsum : (∑ sigma : blockGroup X,
        ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
          (spechtSubrepresentation lam).toRepresentation (sigma : SymmetricGroup n)
            (spechtPolytabloid t)) = 0 := by
      refine Subtype.ext ?_
      rw [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finset_sum, ← hzero,
        blockAntisymmetriser_apply]
      exact Finset.sum_congr rfl fun sigma _ => rfl
    rw [blockAntisymmetriser_apply, hxdef]
    calc ∑ sigma : blockGroup X, ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
          Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu)
            (sigma : SymmetricGroup n) (F (spechtPolytabloid t))
        = ∑ sigma : blockGroup X, F (((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
            (spechtSubrepresentation lam).toRepresentation (sigma : SymmetricGroup n)
              (spechtPolytabloid t)) :=
          Finset.sum_congr rfl fun sigma _ => by rw [map_smul, F.isIntertwining]
      _ = F (∑ sigma : blockGroup X, ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) •
            (spechtSubrepresentation lam).toRepresentation (sigma : SymmetricGroup n)
              (spechtPolytabloid t)) := (map_sum F _ _).symm
      _ = 0 := by rw [hsum, map_zero]
  have heval : ∀ (X : Finset (Fin n)) (S : Tabloid mu),
      blockAntisymmetriser X mu x S = ∑ sigma : blockGroup X,
        ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) *
          x ((sigma : SymmetricGroup n) • S) := by
    intro X S
    rw [blockAntisymmetriser_apply, Finsupp.finset_sum_apply]
    refine Fintype.sum_equiv (Equiv.inv (blockGroup X)) _ _ fun sigma => ?_
    rw [Finsupp.smul_apply, Representation.ofMulAction_apply, smul_eq_mul,
      show ((Equiv.inv (blockGroup X) sigma : blockGroup X) : SymmetricGroup n) =
        (sigma : SymmetricGroup n)⁻¹ from rfl, Equiv.Perm.sign_inv, inv_inv]
  -- a tabloid of the support with the largest row weight, then the largest column weight
  obtain ⟨S₁, hS₁mem, hS₁max⟩ := Finset.exists_max_image x.support (rowWeight t)
    (Finsupp.support_nonempty_iff.mpr hF)
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image
    (x.support.filter fun T => rowWeight t T = rowWeight t S₁) (colWeight t)
    ⟨S₁, Finset.mem_filter.mpr ⟨hS₁mem, rfl⟩⟩
  have hSne : x S ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hSmem).1
  have hSrow : rowWeight t S = rowWeight t S₁ := (Finset.mem_filter.mp hSmem).2
  have hrowmax : ∀ T : Tabloid mu, x T ≠ 0 → rowWeight t T ≤ rowWeight t S := fun T hT => by
    rw [hSrow]
    exact hS₁max T (Finsupp.mem_support_iff.mpr hT)
  have hcolmax : ∀ T : Tabloid mu, x T ≠ 0 → rowWeight t T = rowWeight t S →
      colWeight t T ≤ colWeight t S := fun T hT hw =>
    hSmax T (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hT, hw.trans hSrow⟩)
  -- a column descent would raise the column weight without changing the row weight
  have hcolstrict : ColStrict t S := by
    intro a b hcol hrow
    have hab : a ≠ b := fun h => absurd hrow (by rw [h]; exact lt_irrefl _)
    rcases lt_trichotomy (S.rowOf a) (S.rowOf b) with h | h | h
    · exact h
    · exact absurd (hcolzero S a b hab hcol h) hSne
    · refine absurd (hcolmax (Equiv.swap a b • S) ?_
        (rowWeight_smul_of_mem_columnGroup t (swap_mem_columnGroup hcol) S))
        (not_le.mpr (colWeight_lt_swap t S hrow h))
      rw [hsign _ (swap_mem_columnGroup hcol) S, Equiv.Perm.sign_swap hab]
      simpa using hSne
  -- a row descent would contradict the Garnir relation
  have hrowinc : RowIncreasing t S := by
    refine rowIncreasing_of_adjacent t S fun i j hrow hcol => ?_
    by_contra hle
    set X := lowerBlock t (t.row i) (t.column i) ∪ upperBlock t (t.row i) (t.column i) with hX
    have hgarnir : ∑ sigma : blockGroup X,
        ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) *
          x ((sigma : SymmetricGroup n) • S) = 0 := by
      rw [← heval X S, hblock X (blockAntisymmetriser_polytabloid t
        (fun a ha => (mem_lowerBlock.mp ha).1) (fun b hb => (mem_upperBlock.mp hb).1)
        (colLen_lt_card_block t hrow hcol))]
      rfl
    have hterm : ∀ sigma : blockGroup X,
        ((Equiv.Perm.sign (sigma : SymmetricGroup n) : ℤ) : ℂ) *
            x ((sigma : SymmetricGroup n) • S) =
          if ∀ a, (sigma : SymmetricGroup n) a ∈ upperBlock t (t.row i) (t.column i) ↔
            a ∈ upperBlock t (t.row i) (t.column i) then x S else 0 := by
      intro sigma
      by_cases hp : ∀ a, (sigma : SymmetricGroup n) a ∈ upperBlock t (t.row i) (t.column i) ↔
          a ∈ upperBlock t (t.row i) (t.column i)
      · rw [if_pos hp, hsign _ (mem_columnGroup_of_preserves_upperBlock t sigma.2 hp) S,
          ← mul_assoc, hsq, one_mul]
      · rw [if_neg hp, mul_eq_zero]
        refine Or.inr (by_contra fun hne => ?_)
        exact absurd (hrowmax _ hne)
          (not_le.mpr (rowWeight_lt_of_mem_blockGroup t hcolstrict hrow hcol (not_le.mp hle)
            sigma.2 hp))
    rw [Finset.sum_congr rfl fun sigma _ => hterm sigma, Finset.sum_ite, Finset.sum_const_zero,
      add_zero, Finset.sum_const, nsmul_eq_mul, mul_eq_zero] at hgarnir
    refine hSne (hgarnir.resolve_left ?_)
    have hone : (1 : blockGroup X) ∈ Finset.univ.filter
        fun sigma : blockGroup X => ∀ a, (sigma : SymmetricGroup n) a ∈
          upperBlock t (t.row i) (t.column i) ↔ a ∈ upperBlock t (t.row i) (t.column i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => by simp⟩
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hone)
  exact ⟨S, ⟨hrowinc, hcolstrict⟩, hSne⟩

end YoungTableau
