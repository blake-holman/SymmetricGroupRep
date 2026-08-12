# SymmetricGroupRep source pack

These are the primary sources for the axiom-elimination task. The task
specification and the PDF text extractor are under `refs/task/`.

Corrections found while auditing these sources, recorded in full under
`source_pack_issues` in `docs/axiom-dependency-graph.json`:

- `rosmanis-2014-thesis.pdf` is the 22-page arXiv paper, NOT the thesis. The
  real 181-page thesis is `rosmanis-2014-thesis-FULL-181pp.pdf`; the six
  Rosmanis citations in the Lean docstrings resolve only in that one.
- Rosmanis Lemma 1.12 is stated WITHOUT PROOF, and the Ballantine-Orellana
  theorem proposed as a replacement is strictly narrower than the Lean
  statement. That target must be proved unaided.
- `etingof-et-al-introduction-representation-theory.pdf` is the 2011 draft with
  flat numbering, in which the docstrings' labels do not resolve. Use
  `...-ams-2011-published.pdf`.
- Pieri is never named anywhere in Sagan 2e.
- Sagan Theorem 3.11.1 is CIRCULAR as a citation for the shared hook lemma: he
  derives the determinantal formula FROM the hook formula.
- Srinivasan's content convention is row minus column, the OPPOSITE of this
  project. Conjugate every diagram when transcribing.

All PDF files in this directory were validated locally with PDFInfo before
transfer. Use these copies for focused source reconstruction.

The server uses a local Python extractor rather than Poppler. Examples:

```bash
~/.local/bin/uv run --with pypdf python .claude/tools/pdf_text.py \
  .claude/reference-pdfs/sagan-the-symmetric-group-2e.pdf --pages 55-60
~/.local/bin/uv run --with pypdf python .claude/tools/pdf_text.py \
  .claude/reference-pdfs/sagan-the-symmetric-group-2e.pdf --search "Theorem 2.4.6"
```

| File | Source | Principal targets |
|---|---|---|
| `sagan-the-symmetric-group-2e.pdf` | Bruce Sagan, *The Symmetric Group*, 2nd ed. | Specht construction/classification, tableaux, branching, Young's rule, hook length, Littlewood-Richardson, Pieri |
| `etingof-et-al-introduction-representation-theory.pdf` | Etingof et al., *Introduction to Representation Theory* | regular and biregular decompositions, self-duality, product-group classification |
| `vershik-okounkov-new-approach-ii.pdf` | Vershik and Okounkov, *A New Approach to the Representation Theory of the Symmetric Groups II* | coherent branching and Gelfand-Tsetlin basis |
| `geetha-prasad-gelfand-tsetlin-bases.pdf` | Geetha and Prasad, *Comparison of Gelfand-Tsetlin Bases for Alternating and Symmetric Groups* | coherent embeddings and orthogonal basis conventions |
| `frame-robinson-thrall-hook-graphs.pdf` | Frame, Robinson, and Thrall, *The Hook Graphs of the Symmetric Group* | hook-length formula |
| `tomczak-representation-theory-symmetric-groups.pdf` | Tomczak, *Representation Theory of Symmetric Groups* | Young permutation modules, Young's rule, Kostka conventions |
| `bowman-de-visscher-orellana-kronecker.pdf` | Bowman, De Visscher, and Orellana, *The Partition Algebra and the Kronecker Coefficients* | Kronecker decomposition |
| `rosmanis-2014-thesis.pdf` | Rosmanis, *Lower Bounds on Quantum Query and Learning Graph Complexities* | one-row Specht module and two-row Kronecker reduction |
| `james-1978-representation-theory-symmetric-groups.pdf` | James, *The Representation Theory of the Symmetric Groups* | tensoring with the sign representation |
| `armon-halverson-transition-matrices.pdf` | Armon and Halverson, *Transition Matrices Between Young's Natural and Seminormal Representations* | adjacent-transposition orthogonal action |
| `kowalski-representation-theory.pdf` | Kowalski, *Representation Theory* | irreducibles of direct-product groups |
| `magee-2022-random-unitary-representations.pdf` | Magee, *Random Unitary Representations of Surface Groups I* | Schur-Weyl decomposition and hook-content formula |

Source URLs are recorded in the Lean comments and the repository's
`refs/README.md`; arXiv and publisher copies were used where available.
