# Littlewood-Richardson Completion Guide

## 1. Mission

Finish the sole remaining in-scope axiom in
`SymmetricGroupRep/LittlewoodRichardson.lean`:

```lean
axiom spechtModule_littlewoodRichardson {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b) :
  Nonempty
    ((SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (spechtOuterTensor μ ν) ≅
        ⨁ fun ξ : YoungDiagramOfSize (a + b) =>
          ⨁ fun _ : Fin (littlewoodRichardsonCoefficient μ ν ξ) =>
            spechtModule ξ)
```

Replace only `axiom` by `theorem` and a checked proof. Preserve every binder,
binder order, universe, result type, and mathematical convention.

The repository is `/home/blake/projects/SymmetricGroupRep`, branch
`agent/complete-symmetric-group-roadmap`. This guide was prepared against clean
commit `12d3c9b76056eb503fbd842d824ac226d17b6642`.

`twoRowKroneckerCoefficient_eq_roundTrip_sub` in `Kronecker.lean` is explicitly
deferred and out of scope. Do not use it, prove it, edit its statement, or make
the LR proof depend on it.

## 2. Current State

The difficult tableau and symmetric-polynomial portions of LR are already
proved. The current branch builds successfully and has 25 of the original 27
axioms eliminated. The only in-scope gap is the representation bridge.

Important completed declarations:

| Declaration | Location | Use |
|---|---|---|
| `littlewoodRichardsonCoefficient_eq_stembridgeCount` | `LittlewoodRichardsonBridge.lean:1132` | Frozen tableau count equals Stembridge's count |
| `schurPoly_mul_schurPoly_eq_littlewoodRichardson` | `LittlewoodRichardsonBridge.lean:1140` | Full polynomial LR identity |
| `coeff_schurPoly_eq_kostkaNumber` | `SchurKostka.lean:139` | Schur monomial coefficient is a Kostka number |
| `kostkaNumber_self` | `SchurKostka.lean:147` | Kostka diagonal is one |
| `kostkaNumber_eq_zero_of_not_dominates` | `SchurKostka.lean:155` | Kostka vanishes outside dominance |
| `YoungTableau.finrank_hom_eq_kostkaNumber` | `Kostka.lean:144` | Specht-to-permutation Hom dimension |
| `youngsRule` | `Kostka.lean:163` | Young permutation module decomposition |
| `FDRep.exists_iso_biproduct_multiplicity` | `Decomposition.lean:233` | Assemble a representation from simple multiplicities |
| `FDRep.nonempty_iso_of_finrank_hom_eq` | `Decomposition.lean:272` | Equal simple multiplicities imply an isomorphism |
| `FDRep.finrank_hom_symm` | `Decomposition.lean:342` | Reverse Hom variance for semisimple complex representations |
| `FDRep.indResHomEquiv` | `Induction.lean:71` | Frobenius reciprocity |
| `FDRep.outerTensor_character` | `OuterTensor.lean:34` | Character of an outer tensor product |
| `FDRep.finrank_hom_outerTensor` | `OuterTensor.lean:85` | Product-group Hom factorization when both objects split |
| `FDRep.ofMulActionEquiv` | `YoungPermutation.lean:78` | Equivariant finite-set equivalence gives a representation isomorphism |
| `FDRep.indTrivialIso` | `YoungPermutation.lean:97` | Transitive permutation module as induced trivial representation |
| `youngPermutationModule_twoRow_induction` | `YoungPermutation.lean:369` | Worked stabilizer/induction template |

The source tree also contains working Specht classification, self-duality,
branching, Pieri for two boxes, Young's rule, Schur-Weyl, and semistandard Hom
machinery. Those are useful inputs, but none already states general LR.

Read before editing:

1. `AGENTS.md`
2. `DESIGN_PRINCIPLES.md`
3. `docs/lr-implementation-brief.md`
4. This guide
5. `LittlewoodRichardson.lean`, `LittlewoodRichardsonBridge.lean`
6. `Kostka.lean`, `SchurKostka.lean`, `YoungPermutation.lean`
7. `Decomposition.lean`, `Induction.lean`, `OuterTensor.lean`

The older implementation brief remains the detailed source for tableau
conventions and test examples. Its Layer A-C work is now complete. Treat its
Layer D as a design record, refined by the route below.

## 3. Route Decision

The shortest credible route is a finite multiplicity comparison using Young
permutation modules and unitriangular Kostka inversion. It avoids constructing
a Frobenius characteristic, a representation ring, virtual modules, a general
Mackey theorem, or a basis of LR intertwiners.

The target amount of new Lean is roughly 800-1100 lines. Most of the risk is in
one explicit permutation-module induction theorem and the bookkeeping for the
two Kostka convolution identities.

Use this architecture:

1. Define the representation multiplicity
   `finrank (spechtModule ξ ⟶ Ind (spechtOuterTensor μ ν))`.
2. Prove an identity for these multiplicities after convolution by two Kostka
   matrices, using induced Young permutation modules.
3. Prove the identical convolution identity for LR coefficients from the
   already compiled Schur-polynomial LR theorem.
4. Cancel the two unitriangular Kostka matrices over `ℤ`.
5. Feed the resulting pointwise multiplicity equality into the existing
   semisimple decomposition shell.

The key optimization is on the representation side: use Frobenius reciprocity
and character scalar products to expand Young's-rule biproducts. Do not first
prove that both `outerTensor` and `Ind` distribute over arbitrary finite
biproducts.

## 4. The Fixed Endpoint

Establish a helper with the exact content needed by assembly:

```lean
theorem finrank_hom_ind_spechtOuterTensor_eq_lr {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b)
    (ξ : YoungDiagramOfSize (a + b)) :
    Module.finrank ℂ
      (spechtModule ξ ⟶
        (SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
          (spechtOuterTensor μ ν)) =
      littlewoodRichardsonCoefficient μ ν ξ := by
  ...
```

Then copy the proven assembly pattern from `youngsRule`:

```lean
theorem spechtModule_littlewoodRichardson {a b : ℕ}
    (μ : YoungDiagramOfSize a) (ν : YoungDiagramOfSize b) : Nonempty (...) := by
  obtain ⟨e⟩ := FDRep.exists_iso_biproduct_multiplicity
    spechtModule spechtModule_irreducible
    (fun ξ ξ' h => (spechtModule_iso_iff_eq ξ ξ').mp h)
    (fun T hT => @exists_iso_spechtModule (a + b) T hT)
    ((SymmetricGroupRepresentation.youngSubgroupInduction a b).obj
      (spechtOuterTensor μ ν))
  exact ⟨e ≪≫ biproduct.mapIso fun ξ =>
    biproduct.reindex
      (finCongr (finrank_hom_ind_spechtOuterTensor_eq_lr μ ν ξ))
      fun _ => spechtModule ξ⟩
```

Do not leave this until the end as an untested idea. Create a scratch theorem
or exact local skeleton early so every helper is shaped for the final types.

## 5. Work Package A: Shapes and Permutation Induction

### A1. Combine weights intrinsically

For `α : YoungDiagramOfSize a` and `β : YoungDiagramOfSize b`, construct the
Young diagram of size `a+b` whose row-length multiset is the multiset sum of
the row-length multisets of `α` and `β`. Use
`YoungDiagramOfSize.equivPartition` and partition `parts`; do not introduce a
bespoke merge sort.

Choose one clear public definition and prove immediately:

- total size is `a+b`;
- commutativity if needed by simplification;
- row blocks and their label offsets are well typed;
- enough extensional lemmas to rewrite Kostka weights and base tabloids.

Avoid proving a large general algebra of combined diagrams. Add only lemmas
used by the induction theorem and convolution identities.

### A2. Linearize a product action

Prove the focused isomorphism

```text
M^α ⊠ M^β  ≅  C[Tabloid α × Tabloid β]
```

using the existing linearization and tensor-product APIs. Search mathlib for
`Representation.LinearizeMonoidal.μ`, `μ_apply_single_single`, and
`Rep.linearizationOfMulActionIso` before writing coordinate maps. If wrapping
those declarations in `FDRep` becomes more work than a direct map, implement a
small `Action.mkIso` and prove it on `Finsupp.single` generators.

### A3. Induce the product tabloid action

Prove only the theorem needed here:

```text
Ind_{S_a × S_b}^{S_{a+b}} C[Tabloid α × Tabloid β]
  ≅ C[Tabloid (combined weight α β)].
```

There are two acceptable implementations:

1. Generalize the private `indTrivialToFinsupp` / `indTrivialFinsuppEquiv`
   construction in `YoungPermutation.lean` to induction of a finite
   permutation representation.
2. Specialize the coinvariants construction directly to product tabloids if
   the generic interface causes substantial dependent-type overhead.

Prefer the generic lemma only when it shortens the specialized proof. Its
mathematical content is the finite-set equivalence
`S_{a+b} ×_{S_a×S_b} (Tabloid α × Tabloid β) ≃ Tabloid (combined weight α β)`.

Use `Representation.Coinvariants.lift`, `Representation.IndV.mk`, and
`Representation.IndV.hom_ext`, following `FDRep.indTrivialIso`. Prove inverse
identities on induced generators and permutation-basis singletons rather than
by arbitrary quotient induction when possible.

### A4. Base tabloid and stabilizer

Model this on:

- `twoRowBaseTabloid` at `YoungPermutation.lean:322`;
- `smul_twoRowBaseTabloid_eq_self_iff` at line 335;
- `SymmetricGroup.mem_youngSubgroupInclusion_range_iff`.

The merged base tabloid places the first `a` labels in the rows inherited from
`α` and the last `b` labels in the rows inherited from `β`. The crucial proof
must identify the permitted changes of the two input tabloids exactly with
the restriction of an `S_{a+b}` relabeling to the two standard blocks.

Prove transitivity using the existing `MulAction.IsPretransitive` instance for
tabloids. Keep all inverses consistent with mathlib induction: the established
convention sends the generator indexed by `g` to `g⁻¹` acting on the base
point.

### A5. Public endpoint

Package A2-A4 as a single FDRep isomorphism:

```text
Ind_{S_a × S_b}^{S_{a+b}} (M^α ⊠ M^β)
  ≅ M^(combined weight α β).
```

This is the highest-risk theorem. Build and audit it before investing heavily
in the inversion layer. If it fails, reduce the failing point to a minimal
scratch example and repair the set-level equivalence or generator equation.
Do not respond by building general induction transitivity.

## 6. Work Package B: Representation-Side Convolution

Define, or use the expression directly if a definition adds no clarity,

```text
cRep(μ,ν,ξ) = finrank_C Hom(S^ξ, Ind(S^μ ⊠ S^ν)).
```

For arbitrary `α`, `β`, and `ξ`, prove

```text
sum over μ,ν of
  K(μ,α) * K(ν,β) * cRep(μ,ν,ξ)
  = K(ξ, combined weight α β).
```

Use this chain:

1. Rewrite the right side with
   `YoungTableau.finrank_hom_eq_kostkaNumber`.
2. Transport across the induced-permutation isomorphism from Work Package A.
3. Apply `FDRep.finrank_hom_symm` before Frobenius reciprocity.
4. Rewrite with `FDRep.indFunctor_obj` and
   `(FDRep.indResHomEquiv ...).finrank_eq`.
5. Expand the characters of `M^α` and `M^β` using the two `youngsRule` isos.
6. Use `FDRep.outerTensor_character` and distribute finite sums inside the
   character scalar product.
7. Convert each scalar product back to
   `finrank Hom(S^μ ⊠ S^ν, Res S^ξ)` with
   `FDRep.scalar_product_char_eq_finrank_equivariant`.
8. Reverse Frobenius reciprocity and Hom symmetry to identify `cRep`.

The variance order is important:

```lean
rw [FDRep.finrank_hom_symm, FDRep.indFunctor_obj,
  (FDRep.indResHomEquiv
    (SymmetricGroup.youngSubgroupInclusion a b)
    (spechtOuterTensor μ ν) (spechtModule ξ)).finrank_eq]
```

The likely small missing API is `FDRep.character_biproduct`. The underlying
linear equivalence already exists privately as
`FDRep.biproductLinearEquivPi` in `Decomposition.lean:311`. Expose or restate
only what is necessary to show the trace, hence the character, of a finite
biproduct is the sum of the characters. Follow existing `FDRep.char_iso` and
trace lemmas.

This character calculation is local. Do not implement a formula for the
character of an induced representation and do not define a global Frobenius
characteristic.

Keep casts disciplined. Prove the natural-number identity first when
possible, and move to `ℤ` only for subtraction and inversion.

## 7. Work Package C: Polynomial-Side Convolution

The endpoint is the same identity with LR coefficients:

```text
sum over μ,ν of
  K(μ,α) * K(ν,β) * littlewoodRichardsonCoefficient μ ν ξ
  = K(ξ, combined weight α β).
```

### C1. Complete-homogeneous products

Use a single-row Schur polynomial as the complete homogeneous polynomial.
Prove the finite identity

```text
product over the row lengths of α of s_(row length)
  = sum over μ of K(μ,α) * s_μ.
```

The preferred proof is induction over the parts of `α`, using the existing
semistandard-tableau peeling equivalence
`BoundedSemistandardTableau.fiberEquiv` from `SchurWeyl.lean` and its summed
form nearby. The alternative is repeated one-row Pieri derived from the
compiled Schur product theorem. Choose whichever yields fewer new coercion and
reindexing lemmas after a small prototype.

Keep the common variable count fixed at `a+b`. Do not shrink it to the number
of nonzero rows. Zero row lengths should simplify harmlessly.

### C2. Multiply and compare

Apply the C1 identity to `α`, `β`, and their combined weight. Use:

- multiplication of the two row-products;
- the definition of combined weight as multiset addition;
- finite-sum distributivity;
- `schurPoly_mul_schurPoly_eq_littlewoodRichardson`.

Regroup the result by `ξ`. Compare Schur coefficients to obtain the polynomial
convolution identity.

If a reusable linear-independence theorem for the fixed-degree Schur family is
not present, prove the focused finite version from
`coeff_schurPoly_eq_kostkaNumber`, `kostkaNumber_self`, and
`kostkaNumber_eq_zero_of_not_dominates`. Do not build a general symmetric
function basis library.

An acceptable alternative is to compare monomial coefficients and apply the
same finite Kostka inverse in the output index. Use it only if it is clearly
shorter in Lean than proving the fixed-degree Schur-family independence.

## 8. Work Package D: Kostka Cancellation

The current repository already proves the diagonal and dominance vanishing.
Complete the finite unitriangular cancellation needed to recover an individual
coefficient from the double convolution.

Target a theorem equivalent to:

```text
for each μ there is z : YoungDiagramOfSize n -> ℤ such that
  for every λ,
    sum over α of z α * K(λ,α) = if λ = μ then 1 else 0.
```

Before implementing recursion, search mathlib for inversion of a finite
unitriangular matrix or incidence-algebra element. Use it only if its hypotheses
match the existing dominance relation without a larger translation layer.

Otherwise use well-founded recursion on strict dominance:

```text
delta_μ = multiplicity column for μ
          - sum over λ strictly dominating μ of K(λ,μ) * delta_λ.
```

Required ingredients are finite:

- reflexivity and transitivity of `YoungDiagram.Dominates`;
- antisymmetry or an equality consequence in fixed size;
- irreflexivity/transitivity of strict dominance;
- `Finite.wellFounded_of_trans_of_irrefl` or an equivalent finite order;
- `kostkaNumber_self`;
- `kostkaNumber_eq_zero_of_not_dominates`.

Keep the inverse over `ℤ`. State helper sum identities so that `ring` or
`linear_combination` can finish arithmetic after finite-sum reindexing.

Apply the inverse first in the `α` index and then in the `β` index to the
difference between the representation and polynomial convolution identities.
The result is pointwise

```text
cRep(μ,ν,ξ) = littlewoodRichardsonCoefficient μ ν ξ.
```

Convert back to `ℕ` only at the boundary. Avoid reasoning with truncated
natural subtraction.

## 9. Work Package E: Final Assembly and Audit

Once the pointwise equality compiles:

1. Prove `finrank_hom_ind_spechtOuterTensor_eq_lr` with the exact orientation
   expected by `FDRep.exists_iso_biproduct_multiplicity`.
2. Replace the frozen LR axiom with a theorem using the assembly in Section 4.
3. Add `#print axioms spechtModule_littlewoodRichardson` to
   `SymmetricGroupRep/AxiomAudit.lean` with the same `#guard_msgs` discipline as
   neighboring declarations.
4. Confirm the theorem's closure contains only standard Lean axioms such as
   propositional extensionality, quotient soundness, and classical choice. It
   must not contain the deferred Kronecker axiom or any project axiom.
5. Update `docs/axiom-elimination-status.md` and the relevant LR node in
   `docs/proof-dag.json` only after the proof and full build pass.

## 10. Routes Already Audited and Rejected

Do not restart these investigations unless a new local theorem materially
changes the premises.

### Direct LR intertwiners

`SemistandardHom.lean` computes Homs from Specht modules into permutation
modules. The induced outer tensor of two Specht modules is not such a target.
Adapting it requires skew symmetrizers, an induced model, equivariance,
straightening, independence, and spanning. Estimated cost: 2000-4000 lines.

### Iterated branching or existing Pieri

One-box branching records standard paths but does not impose the full `S_b`
action. The two-box implementation works by the two eigenspaces of the last
transposition and is hard-wired to `S_2`. General `ν` requires decomposing the
entire `S_b` multiplicity representation, which is LR itself.

### Principal-specialization Schur-Weyl

Pairing against tensor-power permutation modules for varying alphabet size
only gives `s_λ(1^q)`. These polynomials are linearly dependent as `λ` varies.
For size six, for example,

```text
3 K_(5,1)(q) - 5 K_(4,2)(q) + 3 K_(4,1,1)(q) = 0.
```

Adding torus-weighted trace operators could restore all Schur variables, but
the required trace naturality and equivariant Hom tensor basis are absent and
would cost at least as much as the chosen bridge.

### Induced-character or full Frobenius characteristic

Mathlib has no character formula for `Ind`, no character ring, and no
Frobenius characteristic map for symmetric groups. Implementing coset traces
plus compatibility with induction is longer than the finite convolution route.

### Jacobi-Trudi or a representation Grothendieck ring

There is no graded representation ring in the project. This route would need
induction transitivity, distributivity, virtual subtraction, and a
representation-valued determinant before reaching LR.

### Searching other worktrees or installed libraries

The current repo history, unreachable local commits, sibling project copies,
and installed mathlib sources were searched. They all retain the LR axiom and
contain no reusable representation-level LR theorem.

## 11. Convention Hazards

1. LR tableau entries are zero-based.
2. Cell coordinates are `(row,column)`, both zero-based.
3. The reading order is top to bottom and right to left within a row. Its
   prefix includes the current cell.
4. The first Young-subgroup block carries `μ`; the second carries `ν`.
5. The LR skew shape is `ξ/μ` and its content is `ν`.
6. `kostkaNumber shape weight` takes the shape first.
7. `YoungDiagram.Dominates shape weight` means the first argument dominates
   the second.
8. Keep Schur polynomials in `a+b` variables throughout.
9. `FDRep.indResHomEquiv` maps Homs out of the induced module. Apply
   `FDRep.finrank_hom_symm` first when starting from `Hom(S^ξ, Ind ...)`.
10. Mathlib's induced generators use the inverse action convention already
    encoded in `FDRep.indTrivialIso`.
11. Handle `a=0`, `b=0`, and empty diagrams deliberately rather than assuming
    a positive row or alphabet.
12. Do not appeal to commutativity of LR coefficients. No suitable theorem is
    available, and the frozen tableau count is oriented.

## 12. File Strategy

Prefer small focused modules over enlarging `LittlewoodRichardson.lean`, whose
role is the frozen public definition and theorem.

A reasonable split is:

```text
SymmetricGroupRep/YoungPermutationProduct.lean
  combined weight
  product linearization
  induced product-tabloid isomorphism

SymmetricGroupRep/KostkaInverse.lean
  fixed-size unitriangular inverse/cancellation

SymmetricGroupRep/LittlewoodRichardsonRepresentation.lean
  representation convolution
  polynomial convolution
  coefficient equality
```

Use fewer files if the declarations remain short. Preserve import direction:
the bridge may import completed combinatorics and representation infrastructure,
while foundational files must not import `LittlewoodRichardson.lean` merely to
gain the target axiom.

Never make a helper depend directly or transitively on
`spechtModule_littlewoodRichardson`.

## 13. Lean Working Method

1. Inspect exact declaration types with `#check` in a scratch file.
2. Prototype the hardest generator equation or finite-sum rewrite before
   committing to a public abstraction.
3. Use `lean-lsp` after each meaningful edit. Fix the earliest diagnostic
   first.
4. Run `lake env lean <changed-file>` for every changed Lean module.
5. Run dependency files before the final target.
6. Keep comments short and mathematical. Do not narrate obvious tactics.
7. Do not weaken signatures, add assumptions, or hide assumptions in
   structures, instances, opaque constants, generated code, or foreign code.
8. Never introduce `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`, or a
   placeholder proof in committed source.
9. Preserve unrelated work. Inspect `git status` and `git diff` before every
   edit and commit.
10. Commit only coherent layers that pass focused checks. Do not push.

When a proof stalls, record the exact theorem, goal, attempted declarations,
and Lean error in `docs/lr-fable-ultracode-progress.md`. On the next loop turn,
resume from that state rather than redoing repository reconnaissance.

## 14. Verification Gate

The task is complete only when all checks pass together:

```bash
cd /home/blake/projects/SymmetricGroupRep

# Frozen signatures, including the LR target.
python3 docs/verify_frozen_signatures.py

# Focused compilation for every new or changed module.
lake env lean SymmetricGroupRep/LittlewoodRichardson.lean
lake env lean SymmetricGroupRep/AxiomAudit.lean

# Whole package.
lake build

# The LR declaration is no longer an axiom. The deferred Kronecker axiom may
# remain and is the only allowed project axiom.
rg -n '^\s*axiom\s+' --glob '*.lean' SymmetricGroupRep

# No proof placeholders or assumption-smuggling constructs in the changed
# implementation.
rg -n '\b(sorry|admit|native_decide)\b|^\s*unsafe\b' \
  --glob '*.lean' SymmetricGroupRep

git diff --check
git status --short
```

Also compare the final declaration directly to the frozen baseline:

```bash
git show 5f00453e209977aa0a6a8845e646e080b4a45676:\
SymmetricGroupRep/LittlewoodRichardson.lean
```

The final audit must establish:

- `spechtModule_littlewoodRichardson` is a theorem with the frozen signature;
- `#print axioms spechtModule_littlewoodRichardson` contains no project axiom;
- the theorem does not depend on
  `twoRowKroneckerCoefficient_eq_roundTrip_sub`;
- `lake build` succeeds from a clean process invocation;
- all intended work is committed locally;
- no push occurred.

## 15. Loop Operating Rules

The Fable Ultracode loop should continue until the verification gate passes.
Each turn should:

1. Read the current progress journal and `git status`/`git diff`.
2. Select the lowest unresolved dependency on the critical path.
3. Use Ultracode dynamic workflows for bounded research or review, while
   keeping exactly one writer in the main worktree.
4. Implement and verify one meaningful step rather than only planning.
5. Update the progress journal with checked facts and the next exact goal.
6. Commit a layer only after focused compilation and relevant audits pass.

Do not stop because an approach is tedious or because the first abstraction
choice fails. Reduce the blocker, switch to the documented specialized variant
when appropriate, and keep going. Stop the recurring loop only when the LR
theorem and all checks above are complete, or when a precise checked
inconsistency in the frozen statement has been demonstrated.
