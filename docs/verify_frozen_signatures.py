#!/usr/bin/env python3
"""Check that every frozen target still has its baseline signature.

Completion check 1 of .claude/commands/eliminate-representation-axioms.md asks
that all retained targets keep the identical signature and differ from the
frozen baseline only in the leading declaration keyword. Doing that by eye does
not scale across many targets and commits, so this script does it mechanically.

For each target it extracts the declaration from the baseline commit and from
the working tree, strips the leading keyword, normalises whitespace, and
requires that the working-tree text equal the baseline text followed by nothing
but a `:=` or `:= by` body marker.

Usage:  python3 docs/verify_frozen_signatures.py
Exit status is non-zero if any target drifted.
"""

from __future__ import annotations

import re
import subprocess
import sys

BASELINE = "5f00453e209977aa0a6a8845e646e080b4a45676"

# target -> module, in the order they appear in docs/axiom-dependency-graph.json
TARGETS = {
    "spechtModule": "Classification.lean",
    "spechtModule_irreducible": "Classification.lean",
    "spechtModule_iso_iff_eq": "Classification.lean",
    "exists_iso_spechtModule": "Classification.lean",
    "exists_spechtTableauBasis": "Tableaux.lean",
    "standardYoungTableau_card_mul_hookProduct": "HookLength.lean",
    "spechtModule_branching": "Branching.lean",
    "spechtModule_induction_branching": "Branching.lean",
    "spechtBranchingBasisData": "BranchingBasis.lean",
    "youngPermutationModule_twoRow_induction": "YoungPermutation.lean",
    "youngsRule": "Kostka.lean",
    "twoRowKostkaIndexEquiv": "Kostka.lean",
    "twoRowKostkaIndexEquiv_shape": "Kostka.lean",
    "spechtModule_littlewoodRichardson": "LittlewoodRichardson.lean",
    "spechtModule_pieri_horizontal": "Pieri.lean",
    "spechtModule_pieri_vertical": "Pieri.lean",
    "existsUnique_iso_spechtOuterTensor": "ProductClassification.lean",
    "spechtModule_kronecker": "Kronecker.lean",
    "spechtModule_singleRow": "Kronecker.lean",
    "spechtModule_tensor_sign": "Kronecker.lean",
    "spechtOrthogonalBasis_adjacentTransposition": "Orthogonal.lean",
    "spechtModule_selfDual": "SelfDuality.lean",
    "symmetricGroupLeftRegular_decomposition": "RegularDecomposition.lean",
    "symmetricGroupBiregular_decomposition": "Biregular.lean",
    "tensorPower_schurWeyl": "SchurWeyl.lean",
    "schurWeylMultiplicity_mul_hookProduct": "SchurWeyl.lean",
}

KEYWORDS = ("axiom", "theorem", "noncomputable def", "def", "lemma")
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(axiom|theorem|noncomputable def|def|lemma|structure|"
    r"abbrev|instance|noncomputable instance|private|end|namespace|open|/-)"
)


def read(path: str, revision: str | None) -> str:
    if revision is None:
        with open(path, encoding="utf-8") as handle:
            return handle.read()
    return subprocess.run(
        ["git", "show", f"{revision}:{path}"],
        check=True, capture_output=True, text=True,
    ).stdout


def extract(source: str, name: str) -> tuple[str, str]:
    """Return (keyword, declaration text) for `name`, body excluded."""
    lines = source.splitlines()
    start = None
    keyword = None
    for index, line in enumerate(lines):
        for candidate in KEYWORDS:
            if line.startswith(f"{candidate} {name}") and (
                len(line) == len(candidate) + 1 + len(name)
                or not line[len(candidate) + 1 + len(name)].isalnum()
                and line[len(candidate) + 1 + len(name)] not in "_'"
            ):
                start, keyword = index, candidate
                break
        if start is not None:
            break
    if start is None:
        raise LookupError(f"declaration {name} not found")

    collected = []
    for line in lines[start:]:
        if collected and DECL_START.match(line):
            break
        if not line.strip() and collected:
            break
        collected.append(line)
    return keyword, "\n".join(collected)


def strip_keyword(text: str, keyword: str) -> str:
    assert text.startswith(keyword + " ")
    return text[len(keyword) + 1:]


def normalise(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def check_against(current: str, baseline: str) -> str | None:
    """Return None if `current` is `baseline` plus only a body, else a reason.

    A converted declaration must reproduce the frozen signature verbatim and
    then start its body immediately, so the frozen text has to be a prefix and
    everything after it has to begin with the `:=` body marker.
    """
    if not current.startswith(baseline):
        return "signature is not the frozen text"
    remainder = current[len(baseline):].strip()
    if remainder == "":
        return "no body: still an unproved declaration"
    if not remainder.startswith(":="):
        return f"extra text before the body: {remainder[:60]!r}"
    return None


def main() -> int:
    failures: list[str] = []
    converted = 0
    for name, module in TARGETS.items():
        path = f"SymmetricGroupRep/{module}"
        try:
            base_keyword, base_text = extract(read(path, BASELINE), name)
        except LookupError as error:
            failures.append(f"{name}: baseline: {error}")
            continue
        if base_keyword != "axiom":
            failures.append(f"{name}: baseline declaration is {base_keyword}, expected axiom")
            continue
        base_signature = normalise(strip_keyword(base_text, base_keyword))

        try:
            keyword, text = extract(read(path, None), name)
        except LookupError as error:
            failures.append(f"{name}: working tree: {error}")
            continue

        current = normalise(strip_keyword(text, keyword))

        if keyword == "axiom":
            if current != base_signature:
                failures.append(
                    f"{name}: SIGNATURE DRIFT while still an axiom\n"
                    f"    baseline: {base_signature}\n"
                    f"    current : {current}"
                )
                continue
            print(f"ok  {name:<46} axiom (not yet converted)")
            continue

        if keyword not in ("theorem", "noncomputable def"):
            failures.append(f"{name}: converted to disallowed form {keyword!r}")
            continue

        reason = check_against(current, base_signature)
        if reason is not None:
            failures.append(
                f"{name}: SIGNATURE DRIFT ({reason})\n"
                f"    baseline: {base_signature}\n"
                f"    current : {current[:len(base_signature) + 40]}"
            )
            continue

        converted += 1
        print(f"ok  {name:<46} {keyword}")

    print(f"\n{converted}/{len(TARGETS)} converted; "
          f"{len(TARGETS) - converted} still axioms")

    if failures:
        print("\nFAILURES:")
        for failure in failures:
            print("  " + failure)
        return 1
    print("all frozen signatures preserved")
    return 0


if __name__ == "__main__":
    sys.exit(main())
