import SymmetricGroupRep.Basic
import SymmetricGroupRep.YoungDiagrams
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RepresentationTheory.Basic

/-! # Tabloids and Young permutation modules

Tabloids are represented by the row containing each label.  This avoids a
quotient by row equivalence while retaining the usual permutation action.
-/

/-- A tabloid of shape `mu`, represented by the row containing each label. -/
@[ext]
structure Tabloid {n : ℕ} (mu : YoungDiagramOfSize n) where
  rowOf : Fin n → Fin n
  row_nonempty : ∀ i, 0 < mu.val.rowLen (rowOf i)
  content : ∀ row : ℕ,
    (Finset.univ.filter fun i => (rowOf i : ℕ) = row).card = mu.val.rowLen row

namespace Tabloid

noncomputable instance {n : ℕ} (mu : YoungDiagramOfSize n) : Finite (Tabloid mu) :=
  Finite.of_injective rowOf fun T U h => by
    apply Tabloid.ext
    exact h

/-- A row index of a cell is below the number of cells. -/
theorem cell_fst_lt {n : ℕ} {mu : YoungDiagramOfSize n} (c : ↥mu.val.cells) : c.1.1 < n := by
  have hc : c.1.1 < mu.val.card :=
    (YoungDiagram.mem_iff_lt_colLen.mp c.2).trans_le <| by
      rw [YoungDiagram.colLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
  simpa [mu.property] using hc

/-- The tabloid recording the row of each label under a bijective filling of the cells. -/
def ofCellEquiv {n : ℕ} {mu : YoungDiagramOfSize n} (e : Fin n ≃ ↥mu.val.cells) :
    Tabloid mu where
  rowOf i := ⟨(e i).1.1, cell_fst_lt (e i)⟩
  row_nonempty := fun i => by
    have hc := YoungDiagram.mem_iff_lt_rowLen.mp (e i).2
    change 0 < mu.val.rowLen (e i).1.1
    exact lt_of_le_of_lt (Nat.zero_le _) hc
  content := by
    intro row
    let target := mu.val.cells.attach.filter fun c => c.1.1 = row
    calc
      (Finset.univ.filter fun i => ((⟨(e i).1.1, cell_fst_lt (e i)⟩ : Fin n) : ℕ) = row).card
          = target.card := by
        apply Finset.card_bijective e e.bijective
        intro i
        simp [target]
      _ = (mu.val.row row).card := by
        change (mu.val.cells.attach.filter fun c => c.1.1 = row).card =
          (mu.val.cells.filter fun c => c.1 = row).card
        rw [Finset.filter_attach (fun c : ℕ × ℕ => c.1 = row) mu.val.cells]
        simp
      _ = mu.val.rowLen row := (YoungDiagram.rowLen_eq_card mu.val).symm

@[simp]
theorem ofCellEquiv_rowOf {n : ℕ} {mu : YoungDiagramOfSize n} (e : Fin n ≃ ↥mu.val.cells)
    (i : Fin n) : ((ofCellEquiv e).rowOf i : ℕ) = (e i).1.1 :=
  rfl

/-- Every Young diagram admits a tabloid. -/
theorem nonempty {n : ℕ} (mu : YoungDiagramOfSize n) : Nonempty (Tabloid mu) :=
  ⟨ofCellEquiv (mu.val.cells.equivFinOfCardEq mu.property).symm⟩

end Tabloid

instance {n : ℕ} (mu : YoungDiagramOfSize n) :
    MulAction (SymmetricGroup n) (Tabloid mu) where
  smul sigma T := {
    rowOf := fun i => T.rowOf (sigma⁻¹ i)
    row_nonempty := fun i => T.row_nonempty _
    content := fun row => by
      rw [← T.content row]
      symm
      apply Finset.card_bijective sigma sigma.bijective
      intro i
      simp }
  one_smul T := by
    apply Tabloid.ext
    funext i
    change T.rowOf ((1 : SymmetricGroup n)⁻¹ i) = T.rowOf i
    rw [inv_one]
    rfl
  mul_smul sigma tau T := by
    apply Tabloid.ext
    funext i
    change T.rowOf ((sigma * tau)⁻¹ i) = T.rowOf (tau⁻¹ (sigma⁻¹ i))
    rw [mul_inv_rev]
    rfl

@[simp]
theorem Tabloid.smul_rowOf {n : ℕ} {mu : YoungDiagramOfSize n}
    (sigma : SymmetricGroup n) (T : Tabloid mu) (i : Fin n) :
    (sigma • T).rowOf i = T.rowOf (sigma⁻¹ i) :=
  rfl

/-- Two tabloids of the same shape place the same number of labels in each row, so some
permutation carries one to the other. -/
instance {n : ℕ} (mu : YoungDiagramOfSize n) :
    MulAction.IsPretransitive (SymmetricGroup n) (Tabloid mu) where
  exists_smul_eq T U := by
    have card_row : ∀ (V : Tabloid mu) (row : Fin n),
        Fintype.card {i : Fin n // V.rowOf i = row} = mu.val.rowLen row := fun V row => by
      rw [Fintype.card_subtype, ← V.content (row : ℕ)]
      simp [Fin.ext_iff]
    let fibers : (Σ row : Fin n, {i : Fin n // T.rowOf i = row}) ≃
        Σ row : Fin n, {i : Fin n // U.rowOf i = row} :=
      Equiv.sigmaCongrRight fun row =>
        Fintype.equivOfCardEq ((card_row T row).trans (card_row U row).symm)
    let sigma : SymmetricGroup n := (Equiv.sigmaFiberEquiv T.rowOf).symm.trans
      (fibers.trans (Equiv.sigmaFiberEquiv U.rowOf))
    have key : ∀ j : Fin n, U.rowOf (sigma j) = T.rowOf j := fun j =>
      (fibers ((Equiv.sigmaFiberEquiv T.rowOf).symm j)).2.2
    refine ⟨sigma, Tabloid.ext (funext fun i => ?_)⟩
    rw [Tabloid.smul_rowOf, ← key (sigma⁻¹ i)]
    simp

/-- The Young permutation module with its tabloid basis. -/
noncomputable def youngPermutationModule {n : ℕ} (mu : YoungDiagramOfSize n) :
    SymmetricGroupRepresentation n :=
  FDRep.of (Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid mu))

/-- The symmetric group permutes the tabloid basis in the usual way. -/
@[simp]
theorem youngPermutationModule_rho_single {n : ℕ} (mu : YoungDiagramOfSize n)
    (sigma : SymmetricGroup n) (T : Tabloid mu) (c : ℂ) :
    (youngPermutationModule mu).ρ sigma (Finsupp.single T c) =
      Finsupp.single (sigma • T) c :=
  Representation.ofMulAction_single sigma T c
