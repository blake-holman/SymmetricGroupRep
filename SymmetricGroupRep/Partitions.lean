import SymmetricGroupRep.Basic
import SymmetricGroupRep.PaddedDiagrams
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-! # Young diagrams, partitions of `n`, and conjugacy classes of `S_n`

Counting the irreducible representations of `S_n` needs two classical bijections, of each of
which mathlib has only the ingredients. A Young diagram of size `n` is its multiset of row
lengths, recovered by sorting; a conjugacy class of `S_n` is the partition attached to any of
its members by `Equiv.Perm.partition`, with `Equiv.Perm.partition_eq_of_isConj` for injectivity
and `Equiv.Perm.exists_with_cycleType_iff` for surjectivity.
-/

attribute [local instance] IsConj.setoid

/-- The row lengths of a Young diagram of size `n`, as a partition of `n`. -/
def YoungDiagramOfSize.partition {n : ℕ} (μ : YoungDiagramOfSize n) : n.Partition where
  parts := ↑μ.val.rowLens
  parts_pos h := μ.val.pos_of_mem_rowLens _ (Multiset.mem_coe.mp h)
  parts_sum := by
    rw [Multiset.sum_coe, ← YoungDiagram.card_eq_rowLens_sum, μ.property]

theorem Nat.Partition.sortedGE_sort {n : ℕ} (p : n.Partition) :
    (p.parts.sort (· ≥ ·)).SortedGE :=
  List.sortedGE_iff_pairwise.mpr (p.parts.pairwise_sort _)

/-- The Young diagram whose rows are the parts of `p`, listed in decreasing order. -/
def Nat.Partition.toYoungDiagram {n : ℕ} (p : n.Partition) : YoungDiagramOfSize n :=
  ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) p.sortedGE_sort,
    by rw [YoungDiagram.card_ofRowLens, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]⟩

theorem Nat.Partition.rowLens_toYoungDiagram {n : ℕ} (p : n.Partition) :
    p.toYoungDiagram.val.rowLens = p.parts.sort (· ≥ ·) :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := p.sortedGE_sort)
    fun x hx => p.parts_pos (by simpa using hx)

theorem YoungDiagramOfSize.parts_partition {n : ℕ} (μ : YoungDiagramOfSize n) :
    μ.partition.parts = ↑μ.val.rowLens := rfl

theorem Nat.Partition.partition_toYoungDiagram {n : ℕ} (p : n.Partition) :
    p.toYoungDiagram.partition = p := by
  refine Nat.Partition.ext ?_
  rw [YoungDiagramOfSize.parts_partition, Nat.Partition.rowLens_toYoungDiagram, Multiset.sort_eq]

theorem YoungDiagramOfSize.partition_injective {n : ℕ} :
    Function.Injective (YoungDiagramOfSize.partition (n := n)) := fun μ ν h =>
  Subtype.ext (YoungDiagram.equivListRowLens.injective (Subtype.ext
    (List.Perm.eq_of_pairwise' μ.val.rowLens_sorted.pairwise ν.val.rowLens_sorted.pairwise
      (Multiset.coe_eq_coe.mp (congrArg Nat.Partition.parts h)))))

/-- Young diagrams of size `n` are the partitions of `n`. -/
def YoungDiagramOfSize.equivPartition (n : ℕ) : YoungDiagramOfSize n ≃ n.Partition where
  toFun := YoungDiagramOfSize.partition
  invFun := Nat.Partition.toYoungDiagram
  left_inv μ := partition_injective μ.partition.partition_toYoungDiagram
  right_inv := Nat.Partition.partition_toYoungDiagram

/-- The cycle type of a permutation of `Fin n`, with its fixed points, as a partition of `n`. -/
def SymmetricGroup.partition {n : ℕ} (σ : SymmetricGroup n) : n.Partition where
  parts := (Equiv.Perm.partition σ).parts
  parts_pos := (Equiv.Perm.partition σ).parts_pos
  parts_sum := by rw [(Equiv.Perm.partition σ).parts_sum, Fintype.card_fin]

/-- Every partition of `n` is the partition of some permutation of `Fin n`.

The parts of size at least two are realised as a cycle type, and the parts equal to one are the
fixed points that `Equiv.Perm.partition` appends to it. -/
theorem SymmetricGroup.exists_partition_eq {n : ℕ} (p : n.Partition) :
    ∃ σ : SymmetricGroup n, SymmetricGroup.partition σ = p := by
  set cycles := p.parts.filter (fun a => 2 ≤ a) with hcycles
  set fixed := p.parts.filter (fun a => ¬ 2 ≤ a) with hfixed
  have hsplit : cycles + fixed = p.parts := Multiset.filter_add_not _ _
  have hones : fixed = Multiset.replicate (Multiset.card fixed) 1 :=
    Multiset.eq_replicate_card.mpr fun b hb => by
      have hpos := p.parts_pos (Multiset.mem_of_mem_filter (hfixed ▸ hb))
      have hsmall := Multiset.of_mem_filter (hfixed ▸ hb)
      omega
  have hparts := congrArg Multiset.sum hsplit
  rw [Multiset.sum_add, p.parts_sum] at hparts
  have hcard : Multiset.card fixed = fixed.sum := by
    conv_rhs => rw [hones]
    simp
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n) (m := cycles)).mpr
    ⟨by rw [Fintype.card_fin]; omega, fun a ha => Multiset.of_mem_filter (hcycles ▸ ha)⟩
  refine ⟨σ, Nat.Partition.ext (Eq.trans ?_ hsplit)⟩
  show (Equiv.Perm.partition σ).parts = _
  rw [Equiv.Perm.parts_partition, hσ, ← Equiv.Perm.sum_cycleType, hσ, Fintype.card_fin,
    show n - cycles.sum = Multiset.card fixed by omega, ← hones]

/-- Two permutations have the same partition exactly when they are conjugate. -/
theorem SymmetricGroup.partition_eq_iff_isConj {n : ℕ} (σ τ : SymmetricGroup n) :
    SymmetricGroup.partition σ = SymmetricGroup.partition τ ↔ IsConj σ τ := by
  rw [Equiv.Perm.partition_eq_of_isConj, Nat.Partition.ext_iff, Nat.Partition.ext_iff]
  rfl

/-- Conjugacy classes of `S_n` are the partitions of `n`. -/
noncomputable def SymmetricGroup.conjClassesEquivPartition (n : ℕ) :
    ConjClasses (SymmetricGroup n) ≃ n.Partition :=
  Equiv.ofBijective
    (Quotient.lift SymmetricGroup.partition fun σ τ h =>
      (SymmetricGroup.partition_eq_iff_isConj σ τ).mpr h)
    ⟨fun q q' => Quotient.inductionOn₂ q q' fun σ τ h =>
        Quotient.sound ((SymmetricGroup.partition_eq_iff_isConj σ τ).mp h),
      fun p => (SymmetricGroup.exists_partition_eq p).elim fun σ h => ⟨Quotient.mk _ σ, h⟩⟩
