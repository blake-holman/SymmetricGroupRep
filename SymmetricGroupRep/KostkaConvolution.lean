import SymmetricGroupRep.KostkaInverse
import SymmetricGroupRep.Kronecker
import SymmetricGroupRep.LittlewoodRichardsonBridge
import SymmetricGroupRep.YoungPermutationProduct

/-! # The Kostka convolution of Littlewood-Richardson coefficients

Multiplying the products of one-row Schur polynomials attached to two weights
convolves the Kostka matrix with the Littlewood-Richardson coefficients.
-/

open Finset

/-- The empty diagram is the only shape of size zero. -/
theorem YoungDiagram.eq_bot_of_card_eq_zero {μ : YoungDiagram} (h : μ.card = 0) : μ = ⊥ :=
  YoungDiagram.ext (by rw [YoungDiagram.cells_bot, ← Finset.card_eq_zero]; exact h)

noncomputable instance (q : ℕ) : Unique (BoundedSemistandardTableau q ⊥) where
  default := ⟨SemistandardYoungTableau.highestWeight ⊥, fun cell hcell =>
    absurd (show cell ∈ (⊥ : YoungDiagram) from hcell) (YoungDiagram.notMem_bot cell)⟩
  uniq T := BoundedSemistandardTableau.ext fun i j => by
    rw [T.tableau.zeros (YoungDiagram.notMem_bot _),
      (SemistandardYoungTableau.highestWeight ⊥).zeros (YoungDiagram.notMem_bot _)]

/-- The Schur polynomial of the empty shape is one. -/
theorem schurPoly_bot (q : ℕ) : schurPoly q ⊥ = 1 := by
  rw [schurPoly, Finset.univ_unique, Finset.sum_singleton]
  have hweight : (default : BoundedSemistandardTableau q ⊥).weight = 0 := by
    ext i
    rw [BoundedSemistandardTableau.weight_apply, SemistandardYoungTableau.weight,
      YoungDiagram.cells_bot, Finset.filter_empty, Finset.card_empty, Finsupp.coe_zero,
      Pi.zero_apply]
  rw [hweight, ← MvPolynomial.C_apply, map_one]

/-! ## One-row shapes -/

theorem singleRowPartition_rowLen (r i : ℕ) :
    (singleRowPartition r).val.rowLen i = if i = 0 then r else 0 := by
  rw [singleRowPartition, twoRowPartition_rowLen]
  rcases i with _ | i <;> simp

theorem mem_singleRowPartition {r i c : ℕ} :
    (i, c) ∈ (singleRowPartition r).val ↔ i = 0 ∧ c < r := by
  rw [YoungDiagram.mem_iff_lt_rowLen, singleRowPartition_rowLen]
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · simp [hi]

theorem colLen_singleRowPartition (r : ℕ) : (singleRowPartition r).val.colLen 0 ≤ 1 := by
  by_contra hcon
  have hmem : ((1, 0) : ℕ × ℕ) ∈ (singleRowPartition r).val :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact absurd (mem_singleRowPartition.mp hmem).1 one_ne_zero

theorem singleRowPartition_zero : (singleRowPartition 0).val = ⊥ :=
  YoungDiagram.eq_bot_of_card_eq_zero (singleRowPartition 0).property

/-! ## One-row tableaux

A tableau of one-row shape is a weakly increasing word, so it is determined by
its weight, and every weight of the right size occurs. -/

/-- A value above the bound occurs in no cell. -/
private theorem weight_eq_zero_of_le {N : ℕ} {lam : YoungDiagram}
    (T : BoundedSemistandardTableau N lam) {v : ℕ} (hv : N ≤ v) : T.tableau.weight v = 0 := by
  rw [SemistandardYoungTableau.weight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun cell hcell hval => absurd (hval ▸ T.entry_lt cell hcell) (by omega)

/-- The row content of a one-row tableau is its weight. -/
private theorem rowContent_singleRow {N r : ℕ}
    (T : BoundedSemistandardTableau N (singleRowPartition r).val) (v : ℕ) :
    SkewFilling.rowContent ⊥ (singleRowPartition r).val T.tableau 0 v = T.tableau.weight v := by
  have hsum := GoodTableau.sum_rowContent_eq_rowPrefix
    (nu := (singleRowPartition r).val) T.tableau v 1
  rw [Finset.sum_range_one] at hsum
  rw [hsum, GoodTableau.rowPrefix_eq_weight T.tableau v (colLen_singleRowPartition r)]

/-- **A one-row tableau is determined by its weight.** -/
private theorem singleRow_ext {N r : ℕ}
    {T U : BoundedSemistandardTableau N (singleRowPartition r).val}
    (h : ∀ v, T.tableau.weight v = U.tableau.weight v) : T = U := by
  have hfill : ∀ V : BoundedSemistandardTableau N (singleRowPartition r).val, ∀ c, c < r →
      rowFill N (fun v => V.tableau.weight v) c = V.tableau 0 c := by
    intro V c hc
    have hbound : ∀ x d, (⊥ : YoungDiagram).rowLen x ≤ d →
        d < (singleRowPartition r).val.rowLen x → V.tableau x d < N := fun x d _ hd =>
      V.entry_lt (x, d) (YoungDiagram.mem_iff_lt_rowLen.mpr hd)
    have hweak : ∀ x d d', (⊥ : YoungDiagram).rowLen x ≤ d → d ≤ d' →
        d' < (singleRowPartition r).val.rowLen x → V.tableau x d ≤ V.tableau x d' :=
      fun x d d' _ hdd hd' =>
        V.tableau.row_weak_of_le hdd (YoungDiagram.mem_iff_lt_rowLen.mpr hd')
    have hrow : (singleRowPartition r).val.rowLen 0 = r := by
      rw [singleRowPartition_rowLen, if_pos rfl]
    have hkey := SkewFilling.eq_rowFill_rowContent (mu := ⊥)
      (xi := (singleRowPartition r).val) (f := V.tableau) (B := N) hbound hweak
      (r := 0) (c := c) (by rw [YoungDiagram.rowLen_bot]; exact Nat.zero_le c) (by omega)
    rw [YoungDiagram.rowLen_bot, Nat.sub_zero,
      funext fun v => rowContent_singleRow V v] at hkey
    exact hkey
  refine BoundedSemistandardTableau.ext fun x c => ?_
  by_cases hcell : (x, c) ∈ (singleRowPartition r).val
  · obtain ⟨rfl, hc⟩ := mem_singleRowPartition.mp hcell
    rw [← hfill T c hc, ← hfill U c hc, funext h]
  · rw [T.tableau.zeros hcell, U.tableau.zeros hcell]

/-- **Every weight of the right size occurs on a one-row shape.** -/
private theorem exists_singleRow_weight {N r : ℕ} (hr : r ≤ N) {m : ℕ → ℕ}
    (hzero : ∀ v, N ≤ v → m v = 0) (hsum : ∑ v ∈ range N, m v = r) :
    ∃ T : BoundedSemistandardTableau N (singleRowPartition r).val,
      ∀ v, T.tableau.weight v = m v := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + r := ⟨N - r, by omega⟩
  set M : ℕ → ℕ → ℕ := fun v i => if i = 0 then m v else 0 with hM
  have h1 : ∀ v i, a + r ≤ v → M v i = 0 := fun v i hv => by simp [hM, hzero v hv]
  have h2 : ∀ i, ∑ v ∈ range (a + r), M v i = (singleRowPartition r).val.rowLen i := by
    intro i
    rw [singleRowPartition_rowLen]
    rcases eq_or_ne i 0 with rfl | hi
    · simpa [hM] using hsum
    · simp [hM, hi]
  have h3 : ∀ v i, ∑ v' ∈ range (v + 1), M v' (i + 1) ≤ ∑ v' ∈ range v, M v' i := by
    intro v i
    simp [hM]
  refine ⟨GoodTableau.ofMatrix (a := a) (nu := singleRowPartition r) h1 h2 h3, fun v => ?_⟩
  rw [← GoodTableau.rowPrefix_eq_weight _ v (colLen_singleRowPartition r),
    GoodTableau.sum_rowPrefix_ofMatrix, Finset.sum_range_one]
  simp [hM]

/-! ## The one-row product rule -/

/-- A tableau is good for `kap` as soon as each value is scarce enough. -/
private theorem isGood_of_weight_le {N : ℕ} {lam kap : YoungDiagram}
    (T : BoundedSemistandardTableau N lam)
    (h : ∀ i, kap.rowLen (i + 1) + T.tableau.weight (i + 1) ≤ kap.rowLen i) :
    Stembridge.IsGood kap.rowLen T :=
  (Stembridge.isGood_iff T).mpr fun i _ j => by
    have hsplit := T.tableau.weight_eq_restrictCols_add_colWeight j (i + 1)
    have := h i
    omega

/-- Conversely, on a one-row shape goodness makes each value scarce: cutting the
row just before its first entry above `i` leaves no `i` and every `i + 1`. -/
private theorem weight_le_of_isGood {N r : ℕ} {kap : YoungDiagram}
    {T : BoundedSemistandardTableau N (singleRowPartition r).val}
    (hgood : Stembridge.IsGood kap.rowLen T) {i : ℕ} (hi : i + 1 < N) :
    kap.rowLen (i + 1) + T.tableau.weight (i + 1) ≤ kap.rowLen i := by
  obtain ⟨j, hjspec, hjmin⟩ : ∃ j, (r ≤ j ∨ i < T.tableau 0 j) ∧
      ∀ c, c < j → c < r ∧ T.tableau 0 c ≤ i := by
    classical
    have hex : ∃ c, r ≤ c ∨ i < T.tableau 0 c := ⟨r, Or.inl le_rfl⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, fun c hc => ?_⟩
    have := Nat.find_min hex hc
    rw [not_or, not_le, not_lt] at this
    exact this
  have hzero : T.tableau.colWeight j i = 0 := by
    rw [SemistandardYoungTableau.colWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨x, c⟩ hcell
    rw [YoungDiagram.mem_cells, mem_singleRowPartition] at hcell
    obtain ⟨rfl, hc⟩ := hcell
    rintro ⟨hjc, hval⟩
    have hvalc : T.tableau 0 c = i := hval
    have hjcc : j ≤ c := hjc
    rcases hjspec with hjr | hlt
    · omega
    · have hle : T.tableau 0 j ≤ T.tableau 0 c :=
        T.tableau.row_weak_of_le hjcc (mem_singleRowPartition.mpr ⟨rfl, hc⟩)
      omega
  have hfull : T.tableau.colWeight j (i + 1) = T.tableau.weight (i + 1) := by
    rw [SemistandardYoungTableau.colWeight, SemistandardYoungTableau.weight]
    refine congrArg Finset.card (Finset.filter_congr fun c hcell => ?_)
    obtain ⟨x, d⟩ := c
    rw [YoungDiagram.mem_cells, mem_singleRowPartition] at hcell
    obtain ⟨rfl, hd⟩ := hcell
    refine ⟨fun hmem => hmem.2, fun hval => ⟨?_, hval⟩⟩
    have hvald : T.tableau 0 d = i + 1 := hval
    by_contra hlt
    have := (hjmin d (by omega)).2
    omega
  have := (Stembridge.isGood_iff T).mp hgood i hi j
  omega

/-- `xi` grows out of `nu` by a horizontal strip: it contains `nu`, and no column
gains a cell twice. -/
private def IsHorizontalStrip (nu xi : YoungDiagram) : Prop :=
  nu ≤ xi ∧ ∀ i, xi.rowLen (i + 1) ≤ nu.rowLen i

open scoped Classical in
/-- **The one-row Pieri rule.**  Multiplying by the Schur polynomial of a one-row
shape adds a horizontal strip. -/
private theorem schurPoly_mul_schurPoly_singleRow {n r N : ℕ} (nu : YoungDiagramOfSize n)
    (hN : n + r ≤ N) :
    schurPoly N nu.val * schurPoly N (singleRowPartition r).val =
      ∑ xi : YoungDiagramOfSize (n + r),
        MvPolynomial.C (if IsHorizontalStrip nu.val xi.val then (1 : ℤ) else 0) *
          schurPoly N xi.val := by
  have hnu : nu.val.colLen 0 ≤ N :=
    le_trans (YoungDiagramOfSize.colLen_zero_le nu) (by omega)
  have hxicol : ∀ xi : YoungDiagramOfSize (n + r), xi.val.colLen 0 ≤ N := fun xi =>
    le_trans (YoungDiagramOfSize.colLen_zero_le xi) hN
  have hrowLen : ∀ T : BoundedSemistandardTableau N (singleRowPartition r).val,
      Stembridge.IsGood nu.val.rowLen T → ∀ v,
        (Stembridge.addWeight nu.val T).rowLen v = nu.val.rowLen v + T.tableau.weight v := by
    intro T hgood v
    rcases lt_or_ge v N with hv | hv
    · exact Stembridge.rowLen_addWeight hgood ⟨v, hv⟩
    · rw [YoungDiagram.rowLen_eq_zero (Stembridge.colLen_addWeight hgood) hv,
        YoungDiagram.rowLen_eq_zero hnu hv, weight_eq_zero_of_le T hv]
  have hcard : ∀ T : BoundedSemistandardTableau N (singleRowPartition r).val,
      Stembridge.IsGood nu.val.rowLen T → (Stembridge.addWeight nu.val T).card = n + r := by
    intro T hgood
    rw [Stembridge.card_addWeight hgood hnu, nu.property, (singleRowPartition r).property]
  have hrhs : ∑ xi : YoungDiagramOfSize (n + r),
      MvPolynomial.C (if IsHorizontalStrip nu.val xi.val then (1 : ℤ) else 0) *
          schurPoly N xi.val =
      ∑ xi ∈ univ.filter fun xi : YoungDiagramOfSize (n + r) =>
        IsHorizontalStrip nu.val xi.val, schurPoly N xi.val := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun xi _ => ?_
    by_cases h : IsHorizontalStrip nu.val xi.val
    · rw [if_pos h, if_pos h, map_one, one_mul]
    · rw [if_neg h, if_neg h, map_zero, zero_mul]
  rw [hrhs, Stembridge.schurPoly_mul_schurPoly hnu]
  refine Finset.sum_bij
    (fun T hT => (⟨Stembridge.addWeight nu.val T, hcard T (mem_filter.mp hT).2⟩ :
      YoungDiagramOfSize (n + r)))
    (fun T hT => mem_filter.mpr ⟨mem_univ _, ?_, fun i => ?_⟩) (fun T hT U hU heq => ?_)
    (fun xi hxi => ?_) (fun T hT => rfl)
  · exact YoungDiagram.le_of_rowLen_le fun i => by
      rw [hrowLen T (mem_filter.mp hT).2 i]
      omega
  · rcases lt_or_ge (i + 1) N with hi | hi
    · rw [hrowLen T (mem_filter.mp hT).2 (i + 1)]
      exact weight_le_of_isGood (mem_filter.mp hT).2 hi
    · rw [YoungDiagram.rowLen_eq_zero
        (Stembridge.colLen_addWeight (mem_filter.mp hT).2) hi]
      exact Nat.zero_le _
  · have hshape : Stembridge.addWeight nu.val T = Stembridge.addWeight nu.val U :=
      congrArg Subtype.val heq
    refine singleRow_ext fun v => ?_
    have h1 := hrowLen T (mem_filter.mp hT).2 v
    have h2 := hrowLen U (mem_filter.mp hU).2 v
    rw [hshape] at h1
    omega
  · obtain ⟨hle, hstrip⟩ := (mem_filter.mp hxi).2
    have hrowle : ∀ v, nu.val.rowLen v ≤ xi.val.rowLen v := YoungDiagram.rowLen_le_of_le hle
    have hzero : ∀ v, N ≤ v → xi.val.rowLen v - nu.val.rowLen v = 0 := fun v hv => by
      rw [YoungDiagram.rowLen_eq_zero (hxicol xi) hv, Nat.zero_sub]
    have hsum : ∑ v ∈ range N, (xi.val.rowLen v - nu.val.rowLen v) = r := by
      have h1 : ∑ v ∈ range N, xi.val.rowLen v = n + r := by
        rw [← YoungDiagram.card_eq_sum_rowLen (hxicol xi), xi.property]
      have h2 : ∑ v ∈ range N, nu.val.rowLen v = n := by
        rw [← YoungDiagram.card_eq_sum_rowLen hnu, nu.property]
      have h3 : ∑ v ∈ range N, ((xi.val.rowLen v - nu.val.rowLen v) + nu.val.rowLen v) =
          ∑ v ∈ range N, xi.val.rowLen v :=
        Finset.sum_congr rfl fun v _ => by have := hrowle v; omega
      rw [Finset.sum_add_distrib] at h3
      omega
    obtain ⟨T, hT⟩ := exists_singleRow_weight (r := r) (by omega) hzero hsum
    have hwt : ∀ v, T.tableau.weight v = xi.val.rowLen v - nu.val.rowLen v := hT
    have hgood : Stembridge.IsGood nu.val.rowLen T := isGood_of_weight_le T fun i => by
      rw [hwt (i + 1)]
      have := hstrip i
      have := hrowle (i + 1)
      omega
    refine ⟨T, mem_filter.mpr ⟨mem_univ _, hgood⟩, Subtype.ext ?_⟩
    refine YoungDiagram.ext_of_rowLen fun v => ?_
    rw [hrowLen T hgood v, hwt v]
    have := hrowle v
    omega

/-! ## Peeling the top value off a tableau -/

open scoped Classical in
/-- The tableaux of shape `xi` bounded by `ℓ + 1` with weight `w` are, for each
shape `nu` that `xi` reaches by a horizontal strip, the tableaux of shape `nu`
bounded by `ℓ` with the truncated weight. -/
private theorem card_weight_fiber {ℓ m : ℕ} (w : ℕ → ℕ) (hm : ∑ i ∈ range ℓ, w i = m)
    (xi : YoungDiagramOfSize (m + w ℓ)) :
    Nat.card {T : BoundedSemistandardTableau (ℓ + 1) xi.val // T.weight = expo (ℓ + 1) w} =
      ∑ nu : YoungDiagramOfSize m,
        if IsHorizontalStrip nu.val xi.val then
          Nat.card {S : BoundedSemistandardTableau ℓ nu.val // S.weight = expo ℓ w} else 0 := by
  have hcomp : ∀ T : BoundedSemistandardTableau (ℓ + 1) xi.val,
      T.weight = expo (ℓ + 1) w ↔ ∀ v, v < ℓ + 1 → T.tableau.weight v = w v :=
    fun T => ⟨fun h v hv => congrArg (fun d : Fin (ℓ + 1) →₀ ℕ => d ⟨v, hv⟩) h,
      fun h => Finsupp.ext fun i => h i i.isLt⟩
  have hbelowcard : ∀ T : BoundedSemistandardTableau (ℓ + 1) xi.val,
      T.weight = expo (ℓ + 1) w → (T.tableau.below ℓ).card = m := by
    intro T hT
    rw [YoungDiagram.card,
      show (T.tableau.below ℓ).cells = xi.val.cells.filter fun c => T.tableau c.1 c.2 < ℓ from rfl,
      Finset.card_eq_sum_card_fiberwise (f := fun c : ℕ × ℕ => T.tableau c.1 c.2) (t := range ℓ)
        fun c hc => mem_range.mpr (mem_filter.mp hc).2]
    refine Eq.trans (Finset.sum_congr rfl fun v hv => ?_) hm
    rw [Finset.filter_filter, ← (hcomp T).mp hT v (by have := mem_range.mp hv; omega),
      SemistandardYoungTableau.weight]
    exact congrArg Finset.card (Finset.filter_congr fun c _ =>
      ⟨fun h => h.2, fun h => ⟨by show T.tableau c.1 c.2 < ℓ; rw [h]; exact mem_range.mp hv, h⟩⟩)
  have hres : ∀ (T : BoundedSemistandardTableau (ℓ + 1) xi.val) {nu : YoungDiagram}
      (h : T.tableau.below ℓ = nu) (v : ℕ), v < ℓ →
      (BoundedSemistandardTableau.restrict T h).tableau.weight v = T.tableau.weight v := by
    intro T nu h v hv
    have hmem : ∀ c : ℕ × ℕ, c ∈ nu.cells ↔ (c ∈ xi.val.cells ∧ T.tableau c.1 c.2 < ℓ) := by
      intro c
      rw [← h, YoungDiagram.mem_cells, SemistandardYoungTableau.mem_below,
        YoungDiagram.mem_cells]
    rw [SemistandardYoungTableau.weight, SemistandardYoungTableau.weight]
    refine congrArg Finset.card (Finset.ext fun c => ?_)
    rw [Finset.mem_filter, Finset.mem_filter, hmem c,
      BoundedSemistandardTableau.restrict_apply]
    constructor
    · rintro ⟨⟨hcell, hlt⟩, hval⟩
      rw [if_pos hlt] at hval
      exact ⟨hcell, hval⟩
    · rintro ⟨hcell, hval⟩
      have hlt : T.tableau c.1 c.2 < ℓ := by rw [hval]; exact hv
      exact ⟨⟨hcell, hlt⟩, by rw [if_pos hlt]; exact hval⟩
  have hiff : ∀ (T : BoundedSemistandardTableau (ℓ + 1) xi.val) {nu : YoungDiagram}
      (h : T.tableau.below ℓ = nu),
      (T.weight = expo (ℓ + 1) w ↔ (BoundedSemistandardTableau.restrict T h).weight = expo ℓ w) := by
    intro T nu h
    constructor
    · intro hT
      refine Finsupp.ext fun i => ?_
      show (BoundedSemistandardTableau.restrict T h).tableau.weight i = w i
      rw [hres T h i i.isLt]
      exact (hcomp T).mp hT i (by omega)
    · intro hS
      have hlow : ∀ v, v < ℓ → T.tableau.weight v = w v := by
        intro v hv
        rw [← hres T h v hv]
        exact congrArg (fun d : Fin ℓ →₀ ℕ => d ⟨v, hv⟩) hS
      refine (hcomp T).mpr fun v hv => ?_
      rcases lt_or_ge v ℓ with hvl | hvl
      · exact hlow v hvl
      · have hsum : ∑ v ∈ range (ℓ + 1), T.tableau.weight v = m + w ℓ := by
          rw [BoundedSemistandardTableau.sum_weight T, xi.property]
        rw [Finset.sum_range_succ,
          Finset.sum_congr rfl (fun v hv' => hlow v (mem_range.mp hv')), hm] at hsum
        rw [show v = ℓ by omega]
        omega
  have hkey : ∀ nu : YoungDiagramOfSize m,
      Nat.card {x : {T : BoundedSemistandardTableau (ℓ + 1) xi.val //
            T.weight = expo (ℓ + 1) w} //
          (⟨x.1.tableau.below ℓ, hbelowcard x.1 x.2⟩ : YoungDiagramOfSize m) = nu} =
        if IsHorizontalStrip nu.val xi.val then
          Nat.card {S : BoundedSemistandardTableau ℓ nu.val // S.weight = expo ℓ w} else 0 := by
    intro nu
    by_cases hstrip : IsHorizontalStrip nu.val xi.val
    · obtain ⟨hle, hstr⟩ := hstrip
      rw [if_pos ⟨hle, hstr⟩]
      refine Nat.card_congr ⟨fun x => ⟨BoundedSemistandardTableau.restrict x.1.1
          (congrArg Subtype.val x.2), (hiff x.1.1 (congrArg Subtype.val x.2)).mp x.1.2⟩,
        fun S => ⟨⟨BoundedSemistandardTableau.extend hle hstr S.1,
          (hiff (BoundedSemistandardTableau.extend hle hstr S.1)
            (BoundedSemistandardTableau.below_extend hle hstr S.1)).mpr
            (by rw [BoundedSemistandardTableau.restrict_extend]; exact S.2)⟩,
          Subtype.ext (BoundedSemistandardTableau.below_extend hle hstr S.1)⟩,
        fun x => ?_, fun S => ?_⟩
      · exact Subtype.ext (Subtype.ext (BoundedSemistandardTableau.extend_restrict hle hstr
          x.1.1 (congrArg Subtype.val x.2)))
      · exact Subtype.ext (BoundedSemistandardTableau.restrict_extend hle hstr S.1)
    · rw [if_neg hstrip]
      have hempty : IsEmpty {x : {T : BoundedSemistandardTableau (ℓ + 1) xi.val //
          T.weight = expo (ℓ + 1) w} //
          (⟨x.1.tableau.below ℓ, hbelowcard x.1 x.2⟩ : YoungDiagramOfSize m) = nu} := by
        refine ⟨fun x => hstrip ?_⟩
        have hb : x.1.1.tableau.below ℓ = nu.val := congrArg Subtype.val x.2
        exact ⟨hb ▸ x.1.1.tableau.below_le ℓ, fun i => hb ▸
          SemistandardYoungTableau.rowLen_le_rowLen_below x.1.1.entry_lt i⟩
      exact Nat.card_of_isEmpty
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun x : {T : BoundedSemistandardTableau (ℓ + 1) xi.val // T.weight = expo (ℓ + 1) w} =>
        (⟨x.1.tableau.below ℓ, hbelowcard x.1 x.2⟩ : YoungDiagramOfSize m))),
    Nat.card_sigma]
  exact Finset.sum_congr rfl fun nu _ => hkey nu

/-! ## Products of one-row Schur polynomials -/

open scoped Classical in
/-- **The product of one-row Schur polynomials counts tableaux by weight.**  The
coefficient of `s_ξ` in `s_(w 0) ⋯ s_(w (ℓ-1))` is the number of tableaux of shape
`ξ` with entries below `ℓ` and weight `w`. -/
private theorem prod_schurPoly_singleRow {N ℓ n : ℕ} (w : ℕ → ℕ)
    (hn : ∑ i ∈ range ℓ, w i = n) (hN : n ≤ N) :
    ∏ i ∈ range ℓ, schurPoly N (singleRowPartition (w i)).val =
      ∑ ξ : YoungDiagramOfSize n,
        MvPolynomial.C (Nat.card {T : BoundedSemistandardTableau ℓ ξ.val //
          T.weight = expo ℓ w} : ℤ) * schurPoly N ξ.val := by
  induction ℓ generalizing n with
  | zero =>
    rw [Finset.sum_range_zero] at hn
    subst hn
    have hbot : (⊥ : YoungDiagram).card = 0 := by
      rw [YoungDiagram.card, YoungDiagram.cells_bot, Finset.card_empty]
    have hcard : Nat.card {T : BoundedSemistandardTableau 0 (⊥ : YoungDiagram) //
        T.weight = expo 0 w} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩,
        ⟨⟨default, Finsupp.ext fun i => i.elim0⟩⟩⟩
    rw [Finset.prod_range_zero, Finset.sum_eq_single (⟨⊥, hbot⟩ : YoungDiagramOfSize 0)
      (fun ξ _ hne => absurd (Subtype.ext (YoungDiagram.eq_bot_of_card_eq_zero ξ.property)) hne)
      fun h => absurd (mem_univ _) h, hcard, schurPoly_bot, mul_one, Nat.cast_one, map_one]
  | succ ℓ ih =>
    have hsplit : (∑ i ∈ range ℓ, w i) + w ℓ = n := by rw [← hn, Finset.sum_range_succ]
    subst hsplit
    have hterm : ∀ ν : YoungDiagramOfSize (∑ i ∈ range ℓ, w i),
        MvPolynomial.C (Nat.card {S : BoundedSemistandardTableau ℓ ν.val //
              S.weight = expo ℓ w} : ℤ) * schurPoly N ν.val *
            schurPoly N (singleRowPartition (w ℓ)).val =
          ∑ ξ : YoungDiagramOfSize ((∑ i ∈ range ℓ, w i) + w ℓ),
            MvPolynomial.C (if IsHorizontalStrip ν.val ξ.val then
              (Nat.card {S : BoundedSemistandardTableau ℓ ν.val //
                S.weight = expo ℓ w} : ℤ) else 0) * schurPoly N ξ.val := by
      intro ν
      rw [mul_assoc, schurPoly_mul_schurPoly_singleRow ν hN, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      by_cases h : IsHorizontalStrip ν.val ξ.val
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.prod_range_succ, ih rfl (by omega), Finset.sum_mul,
      Finset.sum_congr rfl fun ν (_ : ν ∈ univ) => hterm ν, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [← Finset.sum_mul, ← map_sum, card_weight_fiber w rfl ξ, Nat.cast_sum]
    exact congrArg (fun z : ℤ => MvPolynomial.C z * schurPoly N ξ.val)
      (Finset.sum_congr rfl fun ν _ => by split <;> simp)
