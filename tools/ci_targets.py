#!/usr/bin/env python3
"""What the CI test groups load besides their own theories, read from theory script headers."""

from __future__ import annotations

import argparse
import os
import re
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

GENERATED_TESTS = Path("tests/generated")
TEST_COVERAGE_REPORT = Path("tests/vyperTestCoverageReportScript.sml")

COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
THEORY = re.compile(r"^Theory\s+([\w']+)", re.MULTILINE)
NAME = re.compile(r"[A-Za-z_][\w']*")
ATTRIBUTES = re.compile(r"\[[^]]*\]")


@dataclass(frozen=True)
class Header:
    """The `Theory`, `Ancestors` and `Libs` lines of a theory script."""

    name: str
    ancestors: tuple[str, ...]
    libs: tuple[str, ...]

    @classmethod
    def read(cls, script: Path) -> Header:
        """Parse the header of `script`.

        Raises:
            ValueError: `script` has no `Theory` line.
        """
        text = COMMENT.sub("", script.read_text())
        theory = THEORY.search(text)
        if theory is None:
            raise ValueError(f"{script} has no 'Theory <name>' line")
        # A section is its keyword line plus the indented lines after it; the
        # first other unindented line starts the theory body.
        sections: dict[str, list[str]] = {"Ancestors": [], "Libs": []}
        current: list[str] | None = None
        for line in text[theory.end():].splitlines()[1:]:
            words = line.split(maxsplit=1)
            if not words:
                continue
            if words[0] in sections:
                current = sections[words[0]]
                line = words[1] if len(words) > 1 else ""
            elif current is None or not line[0].isspace():
                break
            current += NAME.findall(ATTRIBUTES.sub("", line))
        return cls(theory[1], tuple(sections["Ancestors"]), tuple(sections["Libs"]))


class Project:
    """The project's theory scripts and SML libraries, by the name holbuild gives them."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.theories: dict[str, Path] = {}
        self.libs: set[str] = set()
        self.headers: dict[str, Header] = {}
        for directory, subdirs, files in os.walk(root):
            subdirs[:] = [d for d in subdirs if not d.startswith(".")]
            for file in files:
                if file.endswith("Script.sml"):
                    self.theories[file.removesuffix("Script.sml")] = Path(directory, file)
                elif file.endswith((".sml", ".sig")):
                    self.libs.add(file.rsplit(".", 1)[0])

    def header(self, theory: str) -> Header:
        """The header of the project's `theory`, read once."""
        if theory not in self.headers:
            self.headers[theory] = Header.read(self.theories[theory])
        return self.headers[theory]

    def targets(self, theories: Iterable[str], libs: Iterable[str]) -> list[str]:
        """holbuild targets for the project's own `theories` and `libs`; HOL's are left out."""
        return sorted({f"{name}Theory" for name in theories if name in self.theories}
                      | {name for name in libs if name in self.libs})


def test_dependencies(project: Project) -> list[str]:
    """Project theories and libraries the generated tests and the coverage report load.

    Building these first lets the test groups start before the rest of the
    project is built; a test group then builds only its own test theories.
    """
    headers = [Header.read(script) for script in sorted(project.root.joinpath(GENERATED_TESTS).glob("*Script.sml"))]
    headers.append(Header.read(project.root / TEST_COVERAGE_REPORT))
    generated = {header.name for header in headers}
    return project.targets((name for header in headers for name in header.ancestors if name not in generated),
                           (name for header in headers for name in header.libs))


def main() -> None:
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(" ".join(test_dependencies(Project(Path.cwd()))))


if __name__ == "__main__":
    main()
