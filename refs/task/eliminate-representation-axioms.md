# Eliminate every SymmetricGroupRep axiom

## Objective

Eliminate every explicit axiom in this repository by formal proof, continuing
across `/loop` iterations until the completion checks below all pass. Work in
`/home/blake/projects/SymmetricGroupRep` on branch
`agent/complete-symmetric-group-roadmap`, whose frozen baseline is commit
`5f00453e209977aa0a6a8845e646e080b4a45676`.

Read `AGENTS.md`, `DESIGN_PRINCIPLES.md`, `ROADMAP.md`, all relevant Lean
modules, and `.claude/reference-pdfs/README.md` first.

## Hard constraints

1. Preserve the exact name, universe parameters, binders, binder order,
   hypotheses, result type, and mathematical meaning of every existing axiom.
   Compare each conversion to the frozen baseline with `git show` before
   accepting it. Do not weaken, strengthen, generalize, specialize, restate,
   split, or rename any target.
2. For every proposition-valued target, replace only the `axiom` declaration
   form with a `theorem` and a checked proof.
3. Lean does not permit `theorem` for data-valued declarations. Replace the
   three data-valued targets `spechtModule`, `twoRowKostkaIndexEquiv`, and
   `spechtBranchingBasisData` with `noncomputable def`, preserving their exact
   signatures. This is the sole declaration-form exception.
4. A proof may use mathlib and project results already converted to checked
   definitions or theorems. It may not reference any project declaration that
   is still declared as an axiom, directly or transitively. In particular,
   never prove a target by referring to its old axiom or by creating a renamed
   equivalent axiom.
5. Never introduce or retain `axiom`, `sorry`, `admit`, `unsafe`,
   `native_decide`, placeholder proofs, mock objects, or unproved foreign
   constants. Do not hide assumptions in new typeclasses, structures,
   instances, opaque declarations, generated files, or dependencies.
6. Supporting definitions, lemmas, imports, and tests may be added when needed.
   Keep them narrowly scoped and preserve unrelated code and documentation.
7. Do not change the Lean toolchain or dependency revisions. Do not push.
   Commit each fully verified dependency layer locally with a clear message.

## Phase 1: dependency graph, before Lean edits

Do not edit any `.lean` file until this phase is complete.

1. Inventory every explicit project axiom, its full frozen signature, defining
   module, imports, referenced definitions, cited results, and dependencies on
   other targets.
2. Read enough of every relevant local PDF to audit the mathematical
   dependency edges and source locations. Use the supplied extractor as
   `~/.local/bin/uv run --with pypdf python .claude/tools/pdf_text.py ...`
   for page extraction and focused searches rather than guessing from comments.
3. Create `docs/axiom-dependency-graph.json` in `dependency-graph.v1` format.
   Include every target exactly once. Edges point from prerequisite to result;
   distinguish explicit, inferred, and uncertain edges and include source page
   references.
4. Create `docs/axiom-elimination-status.md` containing the frozen signatures,
   topological layers, proof strategy for each node, verification state, and
   blockers. Record the three data-valued declarations explicitly.
5. Audit the graph for completeness and cycles. Resolve apparent cycles by
   identifying a common lower-level construction rather than letting one axiom
   justify another. Record the verified topological order. Only then begin
   Phase 2.

The baseline currently contains 27 targets. Confirm that count independently;
do not treat this list as a substitute for inventory:

`spechtModule`, `spechtModule_irreducible`, `spechtModule_iso_iff_eq`,
`exists_iso_spechtModule`, `exists_spechtTableauBasis`,
`standardYoungTableau_card_mul_hookProduct`, `spechtModule_branching`,
`spechtModule_induction_branching`, `spechtBranchingBasisData`,
`youngPermutationModule_twoRow_induction`, `youngsRule`,
`twoRowKostkaIndexEquiv`, `twoRowKostkaIndexEquiv_shape`,
`spechtModule_littlewoodRichardson`, `spechtModule_pieri_horizontal`,
`spechtModule_pieri_vertical`, `existsUnique_iso_spechtOuterTensor`,
`spechtModule_kronecker`, `spechtModule_singleRow`,
`spechtModule_tensor_sign`,
`twoRowKroneckerCoefficient_eq_roundTrip_sub`,
`spechtOrthogonalBasis_adjacentTransposition`, `spechtModule_selfDual`,
`symmetricGroupLeftRegular_decomposition`,
`symmetricGroupBiregular_decomposition`, `tensorPower_schurWeyl`, and
`schurWeylMultiplicity_mul_hookProduct`.

## Phase 2: prove in graph order

1. Work on the lowest ready dependency layer. Build foundational Specht-module
   constructions before classification or decomposition results. If a target
   needs mathematics absent from mathlib, formalize the required lower-level
   definitions and lemmas rather than assuming the result.
2. Use Lean LSP searches and small scratch examples before editing production
   declarations. Prefer existing mathlib representation, module, character,
   tensor, induction, restriction, tableau, and finite-sum APIs.
3. Convert one graph node or one tightly coupled foundational layer at a time.
   Run focused diagnostics, then `lake build` before marking it complete.
4. For every converted declaration, run `#print axioms <name>` in an audit
   file and record the result. Reject any proof closure containing one of the
   project's still-axiomatized declarations or a newly introduced assumption.
5. Update both graph and status files after each verified layer. Record source
   passages, Lean dependencies, exact build command, and commit.
6. When blocked, keep researching mathlib and the local sources, reduce the
   obstacle to smaller proved lemmas, and continue. Do not alter a target to
   make it easier.

## Completion checks

Continue the self-paced loop until all of these pass together:

- Every one of the 27 frozen targets has the identical signature and is a
  checked theorem or, for the three data-valued targets, a checked
  `noncomputable def`.
- `rg -n '^\\s*axiom\\s+' --glob '*.lean' .` returns no project declaration.
- A source audit finds no `sorry`, `admit`, `unsafe`, `native_decide`, or other
  assumption-smuggling mechanism in the implementation.
- The recorded `#print axioms` closure of every converted target contains no
  project-defined axiom.
- `lake build` succeeds from a clean process invocation.
- The dependency graph and status ledger mark every node verified and preserve
  the frozen signatures.
- All intentional changes are committed locally and `git status --short` is
  clean.

Stop `/loop` only after every completion check passes. If a genuine theorem is
inconsistent or unprovable from the definitions, produce a minimal checked
counterexample or precise formal obstruction while preserving the target, then
continue on every independent graph node.
