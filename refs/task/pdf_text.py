#!/usr/bin/env python3
"""Extract selected PDF pages or search their text with pypdf."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from pypdf import PdfReader


def page_numbers(spec: str, count: int) -> list[int]:
    if not spec:
        return list(range(count))

    selected: set[int] = set()
    for part in spec.split(","):
        bounds = part.strip().split("-", maxsplit=1)
        start = int(bounds[0])
        end = int(bounds[-1])
        if start < 1 or end < start or end > count:
            raise ValueError(f"page range {part!r} is outside 1-{count}")
        selected.update(range(start - 1, end))
    return sorted(selected)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("pdf", type=Path)
    parser.add_argument("--pages", default="", help="one-based ranges, e.g. 3-5,9")
    parser.add_argument("--search", help="case-insensitive regular expression")
    args = parser.parse_args()

    reader = PdfReader(args.pdf)
    indices = page_numbers(args.pages, len(reader.pages))
    pattern = re.compile(args.search, re.IGNORECASE) if args.search else None

    for index in indices:
        text = reader.pages[index].extract_text() or ""
        if pattern is not None and pattern.search(text) is None:
            continue
        print(f"\n===== PDF page {index + 1} =====\n")
        if pattern is None:
            print(text)
            continue
        for line_number, line in enumerate(text.splitlines(), start=1):
            if pattern.search(line):
                print(f"{line_number}: {line}")


if __name__ == "__main__":
    main()
