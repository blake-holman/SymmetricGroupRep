import SymmetricGroupRep.Branching

/-! # The class sum of the transpositions and the Jucys–Murphy operators

Two families of operators act on every representation of `S_n`: the sum of all
transpositions, which is central and therefore scalar on a Specht module, and
the partial sums `∑_{j < k} (j k)`, the Jucys–Murphy operators. Removing the
largest label splits the class sum into the class sum of the smaller group and
the last Jucys–Murphy operator, which is what turns the branching rule into a
statement about eigenvalues.

See Vershik and Okounkov, *A New Approach to the Representation Theory of the
Symmetric Groups II*, Section 1.
-/

open CategoryTheory

/-- The adjacent transposition exchanging `i` and `i + 1`. -/
def SymmetricGroup.adjacentTransposition {n : ℕ} (i : Fin n) :
    SymmetricGroup (n + 1) :=
  Equiv.swap (Fin.castSucc i) i.succ

@[simp]
theorem SymmetricGroup.adjacentTransposition_apply_left {n : ℕ} (i : Fin n) :
    SymmetricGroup.adjacentTransposition i (Fin.castSucc i) = i.succ :=
  Equiv.swap_apply_left _ _

@[simp]
theorem SymmetricGroup.adjacentTransposition_apply_right {n : ℕ} (i : Fin n) :
    SymmetricGroup.adjacentTransposition i i.succ = Fin.castSucc i :=
  Equiv.swap_apply_right _ _

@[simp]
theorem SymmetricGroup.adjacentTransposition_apply_of_ne {n : ℕ}
    (i : Fin n) (j : Fin (n + 1))
    (hleft : j ≠ Fin.castSucc i) (hright : j ≠ i.succ) :
    SymmetricGroup.adjacentTransposition i j = j :=
  Equiv.swap_apply_of_ne_of_ne hleft hright

/-- An equivariant map moves the action of the group across itself. -/
theorem FDRep.hom_apply_rho {n : ℕ} {W V : SymmetricGroupRepresentation n} (f : W ⟶ V)
    (g : SymmetricGroup n) (v : W.V) :
    f.hom.hom.hom (W.ρ g v) = V.ρ g (f.hom.hom.hom v) := by
  simpa using congrArg (fun h : W.V ⟶ V.V => (ModuleCat.Hom.hom h.hom) v) (f.comm g)

/-- Only the pair `i, i + 1` is inverted by the adjacent transposition. -/
theorem SymmetricGroup.adjacentTransposition_lt {n : ℕ} (i : Fin n) {x y : Fin (n + 1)}
    (hxy : x < y)
    (hne : ¬(x = Fin.castSucc i ∧ y = i.succ)) :
    SymmetricGroup.adjacentTransposition i x < SymmetricGroup.adjacentTransposition i y := by
  simp only [SymmetricGroup.adjacentTransposition]
  have hcast : (Fin.castSucc i : Fin (n + 1)).val = i.val := rfl
  have hsucc : (i.succ : Fin (n + 1)).val = i.val + 1 := rfl
  rcases eq_or_ne x (Fin.castSucc i) with rfl | hxa
  · have hyb : y ≠ i.succ := fun h => hne ⟨rfl, h⟩
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxy.ne' hyb]
    have h1 : i.val < y.val := hxy
    have h2 : y.val ≠ i.val + 1 := fun h => hyb (Fin.ext (by omega))
    exact Fin.lt_def.mpr (by omega)
  · rcases eq_or_ne x i.succ with rfl | hxb
    · have hya : y ≠ Fin.castSucc i := fun h => absurd (h ▸ hxy) (by simp [Fin.lt_def])
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hya hxy.ne']
      have h1 : i.val + 1 < y.val := hxy
      exact Fin.lt_def.mpr (by omega)
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      rcases eq_or_ne y (Fin.castSucc i) with rfl | hya
      · rw [Equiv.swap_apply_left]
        have h1 : x.val < i.val := hxy
        exact Fin.lt_def.mpr (by omega)
      · rcases eq_or_ne y i.succ with rfl | hyb
        · rw [Equiv.swap_apply_right]
          have h1 : x.val < i.val + 1 := hxy
          have h2 : x.val ≠ i.val := fun h => hxa (Fin.ext (by omega))
          exact Fin.lt_def.mpr (by omega)
        · rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
          exact hxy

/-- Every pair of distinct labels, listed once, in increasing order. -/
def transpositionPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

@[simp]
theorem mem_transpositionPairs {n : ℕ} {p : Fin n × Fin n} :
    p ∈ transpositionPairs n ↔ p.1 < p.2 := by
  simp [transpositionPairs]

/-- The sum of all transpositions, acting on a representation. -/
noncomputable def classSum {n : ℕ} (V : SymmetricGroupRepresentation n) :
    V.V →ₗ[ℂ] V.V :=
  ∑ p ∈ transpositionPairs n, V.ρ (Equiv.swap p.1 p.2)

theorem classSum_apply {n : ℕ} (V : SymmetricGroupRepresentation n) (v : V.V) :
    classSum V v = ∑ p ∈ transpositionPairs n, V.ρ (Equiv.swap p.1 p.2) v := by
  rw [classSum, LinearMap.sum_apply]

/-- The sum of the transpositions of the smaller symmetric group, acting
through the standard inclusion. -/
noncomputable def restrictedClassSum {n : ℕ} (V : SymmetricGroupRepresentation (n + 1)) :
    V.V →ₗ[ℂ] V.V :=
  ∑ p ∈ transpositionPairs n, V.ρ (Equiv.swap (Fin.castSucc p.1) (Fin.castSucc p.2))

theorem restrictedClassSum_apply {n : ℕ} (V : SymmetricGroupRepresentation (n + 1))
    (v : V.V) :
    restrictedClassSum V v =
      ∑ p ∈ transpositionPairs n,
        V.ρ (Equiv.swap (Fin.castSucc p.1) (Fin.castSucc p.2)) v := by
  rw [restrictedClassSum, LinearMap.sum_apply]

/-- The `k`-th Jucys–Murphy operator: the sum of the transpositions that move
`k` to a smaller label. -/
noncomputable def jucysMurphy {n : ℕ} (V : SymmetricGroupRepresentation n) (k : Fin n) :
    V.V →ₗ[ℂ] V.V :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), V.ρ (Equiv.swap j k)

theorem jucysMurphy_apply {n : ℕ} (V : SymmetricGroupRepresentation n) (k : Fin n)
    (v : V.V) :
    jucysMurphy V k v =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), V.ρ (Equiv.swap j k) v := by
  rw [jucysMurphy, LinearMap.sum_apply]

section Central

variable {n : ℕ} (V : SymmetricGroupRepresentation n)

/-- Conjugation permutes the transpositions, so it fixes their sum over ordered
pairs of distinct labels. -/
private theorem sum_offDiag_swap_conj (g : SymmetricGroup n) (v : V.V) :
    ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, V.ρ (Equiv.swap (g p.1) (g p.2)) v =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, V.ρ (Equiv.swap p.1 p.2) v := by
  refine Finset.sum_nbij' (fun p => (g p.1, g p.2)) (fun p => (g⁻¹ p.1, g⁻¹ p.2))
    (fun p hp => ?_) (fun p hp => ?_) (fun p _ => ?_) (fun p _ => ?_) (fun p _ => rfl)
  · simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
    exact fun h => hp (g.injective h)
  · simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
    exact fun h => hp (g⁻¹.injective h)
  · simp
  · simp

/-- The sum over ordered pairs counts every transposition twice. -/
private theorem two_smul_classSum_apply (v : V.V) :
    (2 : ℂ) • classSum V v =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, V.ρ (Equiv.swap p.1 p.2) v := by
  classical
  have hlow : (Finset.univ : Finset (Fin n)).offDiag.filter (fun p => p.1 < p.2) =
      transpositionPairs n := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      mem_transpositionPairs]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  have hhigh : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag.filter (fun p => ¬ p.1 < p.2),
        V.ρ (Equiv.swap p.1 p.2) v =
      ∑ p ∈ transpositionPairs n, V.ρ (Equiv.swap p.1 p.2) v := by
    refine Finset.sum_nbij' Prod.swap Prod.swap (fun p hp => ?_) (fun p hp => ?_)
      (fun p _ => rfl) (fun p _ => rfl) (fun p _ => ?_)
    · simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        mem_transpositionPairs] at hp ⊢
      exact lt_of_le_of_ne (not_lt.mp hp.2) (Ne.symm hp.1)
    · simp only [mem_transpositionPairs, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_univ, true_and] at hp ⊢
      exact ⟨Ne.symm hp.ne, not_lt.mpr hp.le⟩
    · rw [Equiv.swap_comm]
      rfl
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin n)).offDiag) (fun p => p.1 < p.2), hlow, hhigh,
    classSum_apply, two_smul]

/-- **The class sum is central.** It commutes with the action of the group. -/
theorem classSum_comm (g : SymmetricGroup n) (v : V.V) :
    classSum V (V.ρ g v) = V.ρ g (classSum V v) := by
  have hconj : ∀ p : Fin n × Fin n,
      V.ρ (Equiv.swap (g p.1) (g p.2)) (V.ρ g v) = V.ρ g (V.ρ (Equiv.swap p.1 p.2) v) := by
    intro p
    rw [Equiv.swap_apply_apply]
    simp [map_mul, mul_assoc]
  have hdouble : (2 : ℂ) • classSum V (V.ρ g v) = (2 : ℂ) • V.ρ g (classSum V v) := by
    rw [two_smul_classSum_apply V (V.ρ g v), ← map_smul, two_smul_classSum_apply V v, map_sum]
    exact (sum_offDiag_swap_conj V g (V.ρ g v)).symm.trans
      (Finset.sum_congr rfl fun p _ => hconj p)
  exact smul_right_injective _ two_ne_zero hdouble

end Central

section Restriction

variable {n : ℕ} (V : SymmetricGroupRepresentation (n + 1))

/-- The standard inclusion carries a transposition to the transposition of the
included labels. -/
theorem SymmetricGroup.inclusion_swap (i j : Fin n) :
    SymmetricGroup.inclusion n (Equiv.swap i j) =
      Equiv.swap (Fin.castSucc i) (Fin.castSucc j) := by
  apply Equiv.ext
  intro x
  rcases eq_or_ne x (Fin.last n) with rfl | hx
  · rw [SymmetricGroup.inclusion_apply_last, Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.castSucc_lt_last i).ne'
    · exact (Fin.castSucc_lt_last j).ne'
  · obtain ⟨y, rfl⟩ : ∃ y : Fin n, Fin.castSucc y = x :=
      ⟨x.castPred hx, Fin.castSucc_castPred x hx⟩
    rw [SymmetricGroup.inclusion_apply_castSucc]
    rcases eq_or_ne y i with rfl | hyi
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · rcases eq_or_ne y j with rfl | hyj
      · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hyi hyj,
          Equiv.swap_apply_of_ne_of_ne (by simpa using hyi) (by simpa using hyj)]

/-- The standard inclusion carries an adjacent transposition to an adjacent
transposition. -/
theorem SymmetricGroup.inclusion_adjacentTransposition {m : ℕ} (j : Fin m) :
    SymmetricGroup.inclusion (m + 1) (SymmetricGroup.adjacentTransposition j) =
      SymmetricGroup.adjacentTransposition (Fin.castSucc j) := by
  rw [SymmetricGroup.adjacentTransposition, SymmetricGroup.adjacentTransposition,
    SymmetricGroup.inclusion_swap, Fin.succ_castSucc]

/-- **Splitting the class sum.** Removing the largest label separates the
transpositions that fix it from those that move it. -/
theorem classSum_eq_restricted_add_jucysMurphy_last (v : V.V) :
    classSum V v = restrictedClassSum V v + jucysMurphy V (Fin.last n) v := by
  classical
  rw [classSum_apply, restrictedClassSum_apply, jucysMurphy_apply]
  have hsplit : transpositionPairs (n + 1) =
      (transpositionPairs n).image (fun p => (Fin.castSucc p.1, Fin.castSucc p.2)) ∪
        (Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.last n)).image
          (fun j => (j, Fin.last n)) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_image, mem_transpositionPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hp
      rcases eq_or_ne p.2 (Fin.last n) with hlast | hlast
      · exact Or.inr ⟨p.1, hlast ▸ hp, by rw [← hlast]⟩
      · have h2 : p.2 < Fin.last n := lt_of_le_of_ne (Fin.le_last _) hlast
        have h1 : p.1 < Fin.last n := hp.trans h2
        refine Or.inl ⟨(p.1.castPred h1.ne, p.2.castPred h2.ne), hp, ?_⟩
        exact Prod.ext (Fin.castSucc_castPred p.1 h1.ne) (Fin.castSucc_castPred p.2 h2.ne)
    · rintro (⟨q, hq, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact hq
      · exact hj
  have hdisj : Disjoint
      ((transpositionPairs n).image (fun p => (Fin.castSucc p.1, Fin.castSucc p.2)))
      ((Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.last n)).image
        (fun j => (j, Fin.last n))) := by
    refine Finset.disjoint_left.mpr ?_
    rintro p hp hq
    simp only [Finset.mem_image] at hp hq
    obtain ⟨a, -, rfl⟩ := hp
    obtain ⟨j, -, hj⟩ := hq
    exact absurd (congrArg Prod.snd hj).symm (Fin.castSucc_lt_last a.2).ne
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_image ?_
    intro a _ b _ hab
    exact Prod.ext (Fin.castSucc_injective n (congrArg Prod.fst hab))
      (Fin.castSucc_injective n (congrArg Prod.snd hab))
  · exact Finset.sum_image fun a _ b _ hab => congrArg Prod.fst hab

variable {W : SymmetricGroupRepresentation n}
  (f : W ⟶ (SymmetricGroupRepresentation.restriction n).obj V)

/-- An equivariant map from the smaller group intertwines the class sums. -/
theorem restrictedClassSum_hom_apply (v : W.V) :
    restrictedClassSum V (f.hom.hom.hom v) = f.hom.hom.hom (classSum W v) := by
  rw [restrictedClassSum_apply, classSum_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← SymmetricGroup.inclusion_swap]
  exact (FDRep.hom_apply_rho f (Equiv.swap p.1 p.2) v).symm

/-- An equivariant map from the smaller group intertwines the Jucys–Murphy
operators away from the largest label. -/
theorem jucysMurphy_castSucc_hom_apply (i : Fin n) (v : W.V) :
    jucysMurphy V (Fin.castSucc i) (f.hom.hom.hom v) =
      f.hom.hom.hom (jucysMurphy W i v) := by
  classical
  have hindex : (Finset.univ.filter fun j : Fin (n + 1) => j < Fin.castSucc i) =
      (Finset.univ.filter fun j : Fin n => j < i).map Fin.castSuccEmb := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castSuccEmb_apply]
    constructor
    · intro hj
      have hlast : j < Fin.last n := hj.trans (Fin.castSucc_lt_last i)
      exact ⟨j.castPred hlast.ne, hj, Fin.castSucc_castPred j hlast.ne⟩
    · rintro ⟨k, hk, rfl⟩
      exact hk
  rw [jucysMurphy_apply, hindex, Finset.sum_map, jucysMurphy_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show V.ρ (Equiv.swap (Fin.castSucc j) (Fin.castSucc i)) (f.hom.hom.hom v) = _
  rw [← SymmetricGroup.inclusion_swap]
  exact (FDRep.hom_apply_rho f (Equiv.swap j i) v).symm

end Restriction

theorem FDRep.rho_mul_apply {n : ℕ} (V : SymmetricGroupRepresentation n)
    (σ τ : SymmetricGroup n) (v : V.V) : V.ρ (σ * τ) v = V.ρ σ (V.ρ τ v) := by
  rw [map_mul]
  rfl

section AdjacentRelations

variable {n : ℕ} (V : SymmetricGroupRepresentation (n + 1)) (i : Fin n)

/-- The labels below `i + 1` are `i` together with the labels below `i`. -/
private theorem filter_lt_succ :
    (Finset.univ.filter fun j : Fin (n + 1) => j < i.succ) =
      insert (Fin.castSucc i) (Finset.univ.filter fun j : Fin (n + 1) => j < Fin.castSucc i) := by
  classical
  ext j
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
    Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
  omega

private theorem castSucc_notMem_filter_lt :
    (Fin.castSucc i) ∉ (Finset.univ.filter fun j : Fin (n + 1) => j < Fin.castSucc i) := by
  simp

/-- Conjugating a transposition into `i` by the adjacent transposition moves it
to `i + 1`. -/
private theorem swap_castSucc_mul_adjacent {j : Fin (n + 1)} (hj : j < Fin.castSucc i) :
    Equiv.swap j (Fin.castSucc i) * SymmetricGroup.adjacentTransposition i =
      SymmetricGroup.adjacentTransposition i * Equiv.swap j i.succ := by
  have hja : j ≠ Fin.castSucc i := hj.ne
  have hjb : j ≠ i.succ := (hj.trans (Fin.castSucc_lt_succ (i := i))).ne
  have hconj := Equiv.swap_apply_apply (SymmetricGroup.adjacentTransposition i) j i.succ
  rw [SymmetricGroup.adjacentTransposition_apply_of_ne i j hja hjb,
    SymmetricGroup.adjacentTransposition_apply_right] at hconj
  rw [hconj, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

/-- Conjugating a transposition into `i + 1` by the adjacent transposition moves
it to `i`. -/
private theorem swap_succ_mul_adjacent {j : Fin (n + 1)} (hj : j < Fin.castSucc i) :
    Equiv.swap j i.succ * SymmetricGroup.adjacentTransposition i =
      SymmetricGroup.adjacentTransposition i * Equiv.swap j (Fin.castSucc i) := by
  have hja : j ≠ Fin.castSucc i := hj.ne
  have hjb : j ≠ i.succ := (hj.trans (Fin.castSucc_lt_succ (i := i))).ne
  have hconj := Equiv.swap_apply_apply (SymmetricGroup.adjacentTransposition i) j (Fin.castSucc i)
  rw [SymmetricGroup.adjacentTransposition_apply_of_ne i j hja hjb,
    SymmetricGroup.adjacentTransposition_apply_left] at hconj
  rw [hconj, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

theorem adjacentTransposition_mul_self :
    SymmetricGroup.adjacentTransposition i * SymmetricGroup.adjacentTransposition i = 1 :=
  Equiv.swap_mul_self _ _

/-- **The first Jucys–Murphy relation.** -/
theorem jucysMurphy_castSucc_adjacent (v : V.V) :
    jucysMurphy V (Fin.castSucc i) (V.ρ (SymmetricGroup.adjacentTransposition i) v) =
      V.ρ (SymmetricGroup.adjacentTransposition i) (jucysMurphy V i.succ v) - v := by
  classical
  rw [jucysMurphy_apply, jucysMurphy_apply, filter_lt_succ,
    Finset.sum_insert (castSucc_notMem_filter_lt i), map_add, map_sum]
  have hfirst : V.ρ (SymmetricGroup.adjacentTransposition i)
      (V.ρ (Equiv.swap (Fin.castSucc i) i.succ) v) = v := by
    rw [← FDRep.rho_mul_apply]
    rw [show SymmetricGroup.adjacentTransposition i * Equiv.swap (Fin.castSucc i) i.succ = 1 from
      adjacentTransposition_mul_self i, map_one]
    rfl
  rw [hfirst, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < Fin.castSucc i := by simpa using hj
  rw [← FDRep.rho_mul_apply, ← FDRep.rho_mul_apply, swap_castSucc_mul_adjacent i hjlt]

/-- **The second Jucys–Murphy relation.** -/
theorem jucysMurphy_succ_adjacent (v : V.V) :
    jucysMurphy V i.succ (V.ρ (SymmetricGroup.adjacentTransposition i) v) =
      V.ρ (SymmetricGroup.adjacentTransposition i) (jucysMurphy V (Fin.castSucc i) v) + v := by
  classical
  rw [jucysMurphy_apply, jucysMurphy_apply, filter_lt_succ,
    Finset.sum_insert (castSucc_notMem_filter_lt i), map_sum]
  have hfirst : V.ρ (Equiv.swap (Fin.castSucc i) i.succ)
      (V.ρ (SymmetricGroup.adjacentTransposition i) v) = v := by
    rw [← FDRep.rho_mul_apply]
    rw [show Equiv.swap (Fin.castSucc i) i.succ * SymmetricGroup.adjacentTransposition i = 1 from
      adjacentTransposition_mul_self i, map_one]
    rfl
  have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.castSucc i),
        V.ρ (Equiv.swap j i.succ) (V.ρ (SymmetricGroup.adjacentTransposition i) v) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.castSucc i),
        V.ρ (SymmetricGroup.adjacentTransposition i) (V.ρ (Equiv.swap j (Fin.castSucc i)) v) :=
    Finset.sum_congr rfl fun j hj => by
      have hjlt : j < Fin.castSucc i := by simpa using hj
      rw [← FDRep.rho_mul_apply, ← FDRep.rho_mul_apply, swap_succ_mul_adjacent i hjlt]
  rw [hfirst, hsum]
  exact add_comm _ _

/-- **The third Jucys–Murphy relation.** Away from `i` and `i + 1` the adjacent
transposition commutes with the operator. -/
theorem jucysMurphy_adjacent_comm {k : Fin (n + 1)} (hka : k ≠ Fin.castSucc i)
    (hkb : k ≠ i.succ) (v : V.V) :
    jucysMurphy V k (V.ρ (SymmetricGroup.adjacentTransposition i) v) =
      V.ρ (SymmetricGroup.adjacentTransposition i) (jucysMurphy V k v) := by
  classical
  have hstable : ∀ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j < k),
      SymmetricGroup.adjacentTransposition i j ∈
        Finset.univ.filter (fun j : Fin (n + 1) => j < k) := by
    intro j hj
    have hjk : j < k := by simpa using hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases eq_or_ne j (Fin.castSucc i) with rfl | hja
    · rw [SymmetricGroup.adjacentTransposition_apply_left]
      have h₁ : (Fin.castSucc i : Fin (n + 1)).val < k.val := hjk
      have h₂ : k.val ≠ i.succ.val := fun h => hkb (Fin.ext h)
      exact Fin.lt_def.mpr (by simp only [Fin.val_succ, Fin.val_castSucc] at *; omega)
    · rcases eq_or_ne j i.succ with rfl | hjb
      · rw [SymmetricGroup.adjacentTransposition_apply_right]
        exact (Fin.castSucc_lt_succ (i := i)).trans hjk
      · rwa [SymmetricGroup.adjacentTransposition_apply_of_ne i j hja hjb]
  rw [jucysMurphy_apply, jucysMurphy_apply, map_sum]
  refine (Finset.sum_nbij' (SymmetricGroup.adjacentTransposition i)
    (SymmetricGroup.adjacentTransposition i) hstable hstable (fun j _ => ?_) (fun j _ => ?_)
    (fun j _ => ?_)).symm
  · exact Equiv.swap_apply_self _ _ _
  · exact Equiv.swap_apply_self _ _ _
  · rw [← FDRep.rho_mul_apply, ← FDRep.rho_mul_apply]
    congr 1
    have hconj := Equiv.swap_apply_apply (SymmetricGroup.adjacentTransposition i) j k
    rw [SymmetricGroup.adjacentTransposition_apply_of_ne i k hka hkb] at hconj
    rw [hconj, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

end AdjacentRelations
