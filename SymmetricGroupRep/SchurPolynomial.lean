import SymmetricGroupRep.BenderKnuth
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! # Schur polynomials

The Schur polynomial of a shape in `q` variables is the generating function of
the semistandard tableaux of that shape with entries below `q`.  The
Bender-Knuth involution exchanges the numbers of two consecutive entries, and
adjacent transpositions generate the symmetric group, so the Schur polynomial is
symmetric.
-/

open Finset

namespace BoundedSemistandardTableau

variable {q : ℕ} {μ : YoungDiagram}

/-- How often each entry occurs in a bounded semistandard tableau. -/
noncomputable def weight (T : BoundedSemistandardTableau q μ) : Fin q →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => T.tableau.weight i

@[simp]
theorem weight_apply (T : BoundedSemistandardTableau q μ) (i : Fin q) :
    T.weight i = T.tableau.weight i := rfl

/-- The Bender-Knuth involution on tableaux with bounded entries. -/
def bk (T : BoundedSemistandardTableau q μ) {k : ℕ} (hk : k + 1 < q) :
    BoundedSemistandardTableau q μ where
  tableau := T.tableau.benderKnuth k
  entry_lt := fun cell hcell => by
    show T.tableau.bkEntry k cell.1 cell.2 < q
    simp only [SemistandardYoungTableau.bkEntry]
    split_ifs
    · omega
    · omega
    · exact T.entry_lt cell hcell

theorem bk_bk (T : BoundedSemistandardTableau q μ) {k : ℕ} (hk : k + 1 < q) :
    (T.bk hk).bk hk = T := by
  ext i j
  exact congrFun (congrFun (congrArg DFunLike.coe
    (SemistandardYoungTableau.benderKnuth_benderKnuth (T := T.tableau) (k := k))) i) j

/-- The Bender-Knuth involution exchanges the number of `k`s with the number of
`k + 1`s and leaves the other entry counts alone. -/
theorem weight_bk (T : BoundedSemistandardTableau q μ) {k : ℕ} (hk : k + 1 < q) :
    (T.bk hk).weight =
      Finsupp.equivMapDomain (Equiv.swap (⟨k, by omega⟩ : Fin q) ⟨k + 1, hk⟩) T.weight := by
  ext i
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap, weight_apply, weight_apply]
  rcases eq_or_ne i (⟨k, by omega⟩ : Fin q) with hi | hi
  · subst hi
    rw [Equiv.swap_apply_left]
    exact SemistandardYoungTableau.weight_benderKnuth_self
  rcases eq_or_ne i (⟨k + 1, hk⟩ : Fin q) with hi1 | hi1
  · subst hi1
    rw [Equiv.swap_apply_right]
    exact SemistandardYoungTableau.weight_benderKnuth_succ
  · rw [Equiv.swap_apply_of_ne_of_ne hi hi1]
    exact SemistandardYoungTableau.weight_benderKnuth_of_ne
      (fun h => hi (Fin.ext h)) (fun h => hi1 (Fin.ext h))

end BoundedSemistandardTableau

/-- The Schur polynomial of the shape `μ` in `q` variables. -/
noncomputable def schurPoly (q : ℕ) (μ : YoungDiagram) : MvPolynomial (Fin q) ℤ :=
  ∑ T : BoundedSemistandardTableau q μ, MvPolynomial.monomial T.weight 1

variable {q : ℕ} {μ : YoungDiagram}

open scoped Classical in
theorem coeff_schurPoly (m : Fin q →₀ ℕ) :
    (schurPoly q μ).coeff m =
      ((univ.filter fun T : BoundedSemistandardTableau q μ => T.weight = m).card : ℤ) := by
  rw [schurPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_boole]

/-- Swapping two consecutive variables leaves a Schur polynomial alone: the
Bender-Knuth involution matches up the monomials. -/
theorem rename_swap_schurPoly {k : ℕ} (hk : k + 1 < q) :
    MvPolynomial.rename (Equiv.swap (⟨k, by omega⟩ : Fin q) ⟨k + 1, hk⟩) (schurPoly q μ) =
      schurPoly q μ := by
  have hinv : ∀ T : BoundedSemistandardTableau q μ, (T.bk hk).bk hk = T :=
    fun T => T.bk_bk hk
  let e : BoundedSemistandardTableau q μ ≃ BoundedSemistandardTableau q μ :=
    ⟨fun T => T.bk hk, fun T => T.bk hk, hinv, hinv⟩
  rw [schurPoly, map_sum,
    ← Equiv.sum_comp e fun T : BoundedSemistandardTableau q μ =>
      MvPolynomial.monomial T.weight (1 : ℤ)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [MvPolynomial.rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain]
  exact congrArg (fun d => MvPolynomial.monomial d (1 : ℤ)) (T.weight_bk hk).symm

/-- Schur polynomials are symmetric. -/
theorem schurPoly_isSymmetric : (schurPoly q μ).IsSymmetric := by
  intro e
  cases q with
  | zero =>
    rw [Subsingleton.elim e (Equiv.refl (Fin 0))]
    exact MvPolynomial.rename_id_apply _
  | succ n =>
    have hmem : e ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top e
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact rename_swap_schurPoly (k := (i : ℕ)) (by omega)
    | one => exact MvPolynomial.rename_id_apply _
    | mul x y _ _ hx hy =>
      rw [show ⇑(x * y) = ⇑x ∘ ⇑y from rfl, ← MvPolynomial.rename_rename, hy, hx]
