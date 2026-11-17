"""Check the ordered public-paper correspondence, independently of proof checking."""

from collections import Counter
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
FOLDER = ROOT / "ComparatorChallenges"
KINDS = {"Theorem": 1, "Proposition": 27, "Definition": 9, "Example": 3,
         "Problem": 2, "Conjecture": 1}
MARKER = re.compile(r"^/\-! Paper (\w+) (\d+\.\d+)\b", re.MULTILINE)
DECL = re.compile(r"^theorem (\w+)(.*?)(?=^theorem |^def |^end ComparatorChallenges|\Z)",
                  re.MULTILINE | re.DOTALL)
FORBIDDEN = re.compile(r"\b(?:sorry|axiom|native_decide)\b|\+native")
SHARED = {"Ninegates.Hand.Defs", "Ninegates.Meldable.Defs", "Ninegates.Wait.Defs",
          "Ninegates.Minimal.Defs"}


def declaration_header(body: str) -> str:
    """Find the declaration assignment, keeping named arguments in its type."""
    delimiters = {"(": ")", "[": "]", "{": "}", "«": "»"}
    stack = []
    i = 0
    while i < len(body):
        if body.startswith("--", i):
            end = body.find("\n", i)
            i = len(body) if end == -1 else end + 1
            continue
        if body.startswith("/-", i):
            nesting = 1
            i += 2
            while nesting and i < len(body):
                if body.startswith("/-", i):
                    nesting += 1
                    i += 2
                elif body.startswith("-/", i):
                    nesting -= 1
                    i += 2
                else:
                    i += 1
            if nesting:
                raise ValueError("Unclosed comment in theorem header")
            continue
        char = body[i]
        if char == '"':
            i += 1
            while i < len(body) and body[i] != '"':
                i += 2 if body[i] == "\\" else 1
            if i == len(body):
                raise ValueError("Unclosed string in theorem header")
        elif char in delimiters:
            stack.append(delimiters[char])
        elif char in delimiters.values():
            if not stack or stack.pop() != char:
                raise ValueError("Unbalanced delimiter in theorem header")
        elif not stack and body.startswith(":=", i):
            return body[:i]
        i += 1
    raise ValueError("Missing declaration assignment")


def signatures(source: str) -> dict[str, str]:
    result = {}
    for match in DECL.finditer(source):
        name = "ComparatorChallenges." + match[1]
        if name in result:
            raise ValueError(f"Repeated theorem: {name}")
        result[name] = " ".join(declaration_header(match[2]).split())
    return result


def verify() -> tuple[int, int]:
    paper = json.loads((FOLDER / "paper.json").read_text())
    config = json.loads((FOLDER / "config.json").read_text())
    if paper["version_id"] != "2611.06944v1" or paper["submitted_utc"] != "2026-11-02T06:23:21Z":
        raise ValueError("The pinned public-paper version needs an explicit source re-audit")
    for field in ["abstract_url", "pdf_url", "html_url", "source_url"]:
        if not paper[field].endswith("2611.06944v1"):
            raise ValueError(f"Unpinned paper reference: {field}")
    if paper["sha256"]["2611.06944v1.pdf"] != (
        "174b9a8be2f5c01fe31550a7d4695e35d70047597b328064abaaa86b49eb8b50"
    ):
        raise ValueError("The public PDF identity changed")
    items = paper["numbered_items"]
    if Counter(item["kind"] for item in items) != Counter(KINDS):
        raise ValueError("The public v1 inventory must contain all 43 numbered items")
    expected = [(item["kind"], item["number"]) for item in items]
    numbers = ["1.1", "2.1", "2.2"] + [
        f"{section}.{number}" for section, last in [(3, 10), (4, 11), (5, 10), (6, 9)]
        for number in range(1, last + 1)
    ]
    definitions = {"2.2", "3.1", "3.3", "3.5", "4.1", "4.3", "4.7", "5.4", "6.3"}
    examples = {"4.5", "6.5", "6.6"}
    def kind(number: str) -> str:
        if number == "1.1": return "Theorem"
        if number in definitions: return "Definition"
        if number in examples: return "Example"
        if number in {"6.1", "6.4"}: return "Problem"
        if number == "6.9": return "Conjecture"
        return "Proposition"
    if expected != [(kind(number), number) for number in numbers]:
        raise ValueError("The inventory differs from the pinned public v1 order")
    challenge = (FOLDER / "Challenge.lean").read_text()
    solution = (FOLDER / "Solution.lean").read_text()
    for label, source in [("challenge", challenge), ("solution", solution)]:
        if MARKER.findall(source) != expected:
            raise ValueError(f"The {label} does not follow every published label in order")
        if "arXiv:2611.06944v1" not in source or "submitted 2026-11-02" not in source:
            raise ValueError(f"The {label} lacks pinned version metadata")
    challenge_types, solution_types = signatures(challenge), signatures(solution)
    selected = []
    deferred = []
    for item in items:
        kind, number, status = item["kind"], item["number"], item["status"]
        names = item["declarations"]
        if kind == "Problem":
            if status != "open_problem" or names:
                raise ValueError(f"Open problem {number} is being counted as a proof")
        elif kind == "Conjecture":
            if status != "open_conjecture" or names:
                raise ValueError(f"Open conjecture {number} is being counted as a proof")
            if "def conjecture_6_9 : Prop :=" not in challenge or "def conjecture_6_9 : Prop :=" not in solution:
                raise ValueError("The conjecture statement must remain visible as a proposition")
        elif status == "deferred_expensive_computation":
            deferred.append((kind, number))
            if names != ["ComparatorChallenges.example_6_6"]:
                raise ValueError("Unexpected deferred result")
            if names[0] not in challenge_types or names[0] in solution_types:
                raise ValueError("The deferred result needs a challenge goal and no claimed solution")
        else:
            if kind == "Definition":
                if status != "definition" or not item.get("model_declarations"):
                    raise ValueError(f"Definition {number} lacks its model correspondence")
            elif status != "formalized" or not names:
                raise ValueError(f"Unaccounted result: {kind} {number}")
            selected.extend(names)
    if deferred != [("Example", "6.6")]:
        raise ValueError("Only the explicitly deferred Example 6.6 may be unchecked")
    selected.extend(paper["additional_declarations"])
    if config["theorem_names"] != selected or len(selected) != len(set(selected)):
        raise ValueError("Comparator targets do not match the ordered proved inventory")
    if set(solution_types) != set(selected):
        raise ValueError("Solution theorems and configured targets differ")
    remarks = paper["unnumbered_remarks"]
    if [(remark["after"], remark["anchor"]) for remark in remarks] != [
        ("4.11", "Thmremarkx1"), ("5.6", "Thmremarkx2"), ("5.8", "Thmremarkx3"),
        ("5.9", "Thmremarkx4"), ("5.10", "Thmremarkx5")
    ]:
        raise ValueError("The five public v1 remarks must remain in published order")
    remark_names = []
    for remark in remarks:
        after, names = remark["after"], remark["declarations"]
        if remark["status"] != "formalized" or not names:
            raise ValueError(f"Unverified remark after {after}")
        remark_names.extend(names)
        for label, source in [("challenge", challenge), ("solution", solution)]:
            markers = list(MARKER.finditer(source))
            parent = next(i for i, marker in enumerate(markers) if marker[2] == after)
            block = source[markers[parent].end():markers[parent + 1].start()]
            if f"-- Unnumbered remark after {after}: formalized." not in block:
                raise ValueError(f"Missing remark marker after {after} in {label}")
            for name in names:
                if f"theorem {name.removeprefix('ComparatorChallenges.')} :" not in block:
                    raise ValueError(f"Misplaced remark declaration in {label}: {name}")
    if len(remark_names) != len(set(remark_names)) or not set(remark_names) <= set(selected):
        raise ValueError("Remark declarations must be distinct verified targets")
    for name in selected:
        if challenge_types.get(name) != solution_types[name]:
            raise ValueError(f"Challenge and solution source signatures differ: {name}")
    if set(config["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("Unexpected permitted axioms")
    for file in ["Model.lean", "Bridges.lean", "Solution.lean"]:
        if FORBIDDEN.search((FOLDER / file).read_text()):
            raise ValueError(f"Forbidden proof token in {file}")
    model = (FOLDER / "Model.lean").read_text()
    imports = re.findall(r"^public import (Ninegates\.\S+)", model, re.MULTILINE)
    if set(imports) != SHARED:
        raise ValueError("The trusted model imports more than the shared foundational definitions")
    for module in imports:
        source = ROOT.joinpath(*module.split(".")).with_suffix(".lean").read_text()
        if re.search(r"^(?:public )?(?:lemma|theorem|axiom)\b", source, re.MULTILINE):
            raise ValueError(f"The shared model module contains project theorem declarations: {module}")
        if re.search(r"^public import Ninegates\.", source, re.MULTILINE):
            dependencies = re.findall(r"^public import (Ninegates\.\S+)", source, re.MULTILINE)
            if not set(dependencies) <= SHARED:
                raise ValueError(f"Unexpected trusted-model dependency: {module}")
    if "ComparatorChallenges.Bridges" in challenge or "public import Ninegates" in challenge:
        raise ValueError("The challenge must not import project proofs")
    return len(items), len(selected)


if __name__ == "__main__":
    try:
        count, targets = verify()
    except (ValueError, KeyError) as error:
        raise SystemExit(str(error)) from error
    print(f"Verified {count} ordered public-paper entries and {targets} Comparator targets.")
    print("All five unnumbered remarks have ordered, selected proof targets.")
    print("Example 6.6 is deferred; Problems 6.1/6.4 and Conjecture 6.9 remain open.")
