"""Check Lean's axiom report and reject proof placeholders in the library."""

from pathlib import Path
import re
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ENTRY = re.compile(
    r"'([^\n]*?)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
)
FORBIDDEN = re.compile(r"\b(?:sorry|axiom|native_decide)\b|\+native")


def verify(audit: Path, report: Path) -> int:
    expected = re.findall(r"^#print axioms (\S+)", audit.read_text(), re.MULTILINE)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError("The audit must name a nonempty set of distinct declarations")
    output = report.read_text()
    entries = list(ENTRY.finditer(output))
    if [entry[1] for entry in entries] != expected:
        raise ValueError("The report does not match the audit declarations in order")
    for entry in entries:
        axioms = {item.strip() for item in (entry[2] or "").split(",") if item.strip()}
        if extra := axioms - ALLOWED:
            raise ValueError(f"{entry[1]} uses forbidden axioms: {sorted(extra)}")
    if ENTRY.sub("", output).strip():
        raise ValueError("The report contains diagnostics or unexpected output")
    root = audit.resolve().parent
    sources = list((root / "Ninegates").rglob("*.lean")) + [root / "Ninegates.lean"]
    for source in sources:
        for number, line in enumerate(source.read_text().splitlines(), 1):
            if FORBIDDEN.search(line):
                raise ValueError(f"Forbidden proof token at {source}:{number}")
    return len(entries)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("Usage: check_axioms.py Audit.lean axioms.log")
    try:
        count = verify(Path(sys.argv[1]), Path(sys.argv[2]))
    except ValueError as error:
        raise SystemExit(str(error)) from error
    print(f"Verified {count} declarations; only standard axioms.")
