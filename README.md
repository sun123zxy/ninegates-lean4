<div align="center">

# 🀇🀇🀇🀈🀉🀊🀋🀌🀍🀎🀏🀏🀏
# Beyond Nine Gates

Classification of Full-Sided Mahjong Waits with 3n Ranks  
Structural formalization in Lean 4

[![arXiv](https://img.shields.io/badge/arXiv-2611.06944-b31b1b?style=flat-square&logo=arxiv&logoColor=white)](https://arxiv.org/abs/2611.06944)

</div>

This is the structural rewrite on the `v3` branch, aligned with the public paper
[arXiv:2611.06944v1](https://arxiv.org/abs/2611.06944v1), submitted 2 November 2026.
The previous implementation is archived on [`v2`](https://github.com/lunaluteus/ninegates-lean4/tree/v2).
The new library replaces its API completely and proves the classification
structurally, without enumerating candidate hands or using `native_decide`.

## The model

Nine Gates is the one-suit Mahjong wait `1112345678999`: drawing any of the nine
ranks makes a winning hand. We study the same question on `3*n` ranks, allowing
the order `n`, number of melds `m`, and copy bound `cap` to vary independently.
A full-sided wait has `3*m+1` tiles; every possible draw completes `m` melds
and a pair. Liveness additionally requires every draw to respect the copy bound.

`Mahjong.VirtualHand n` is an integer multiplicity vector on `Fin (3*n)`.
`Nonnegative` specifies actual hands. Integer subtraction lets us express
removing a pair or meld directly. A placement has one coefficient for each
legal sequence start and each triplet rank; nonnegative coefficients describe
actual meld decompositions, while integer coefficients describe virtual ones.

Lean indices are zero-based. The rank used in the paper's weighted sum and
congruences is `i.val+1`. The last two ranks are excluded from the sequence-start
type, and both final scan states are checked in the meldability criterion.

## Results proved

The main declarations are in the `Mahjong.VirtualHand` namespace:

- [`Classification`](Ninegates/Classification.lean): for `n>=2`, full-sided
  waits with `m=n+1` are exactly the eight families `A`, `B`, `B'`, `C`, `C'`,
  `D`, `D'`, and `E`. With live draws under copy bound four, only `A` remains.
- [`Standard/One`](Ninegates/Standard/One.lean): at order one and meld count
  two, the six full-sided waits are `(3,1,3)`, `(2,3,2)`, `(3,3,1)`,
  `(1,3,3)`, `(3,2,2)`, and `(2,2,3)`. All are live.
- [`Wait/Bounds`](Ninegates/Wait/Bounds.lean): every full-sided wait satisfies
  `m>n`, without a copy bound.
- [`Wait/Abundance`](Ninegates/Wait/Abundance.lean): sufficiently abundant hands
  of the required size are full-sided; adding any meldable hand preserves
  full-sidedness. At order one the sufficient threshold improves to `(2,2,2)`.
- [`Minimal`](Ninegates/Minimal/Defs.lean): minimality excludes removal of any
  nonzero meldable hand leaving a full-sided wait. Every full wait at `m=n+1`
  is minimal, and all order-one minimal waits are among the six above.
- [`Minimal/Maximum`](Ninegates/Minimal/Maximum.lean) and
  [`Minimal/Double/Minimal`](Ninegates/Minimal/Double/Minimal.lean): the largest
  minimal meld count `M(n)` exists for every positive order, `M(1)=2`, and
  `2*n <= M(n) < 8*n`. The minimal family `(3,2,...,2)` gives the first lower bound;
  the alternating families strengthen it to `9*n/2-3 <= M(n)` (integer division).
- [`Minimal/Alternating/Minimal`](Ninegates/Minimal/Alternating/Minimal.lean): both
  stronger even/odd alternating constructions are minimal full-sided waits, with
  meld counts `9*a+6` and `9*a+10`. Their canonical sequence coefficients have
  an exact formula for arbitrary order, draw, and pair. Critical draws rule out
  each elementary removal and hence every nonzero meldable removal.

[`Cardinality`](Ninegates/Cardinality.lean) proves the exact counts: eight
full-sided and minimal waits at `m=n+1` for `n>=2`, exactly one of them live;
six full-sided, minimal, and live waits at order one and meld count two.
There are no full-sided waits for `m<=n`, and no other minimal waits at order one.
The eight named families are proved distinct at every `n>=2`.

[`Wait/OrderOne`](Ninegates/Wait/OrderOne.lean) also characterizes order-one
full waits for every meld count: the required size together with at least
one tile at the fixed rank and two at each other rank is sufficient and
necessary. [`Numerical/OrderOne`](Ninegates/Numerical/OrderOne.lean) gives the
exact count `choose(3*m-2,2)` for `m>=2`, and zero for `m<=1`, with unrestricted
multiplicities. A class-dependent five-tile translation gives a bijection
with the nonnegative triples summing to `3*m-4`; stars and bars supplies the count.

[`Minimal/Next`](Ninegates/Minimal/Next.lean) characterizes every nonminimal
full-sided `(n,n+2)` wait for `n>=2` as a standard hand plus one elementary meld.
[`Numerical/Taiwanese`](Ninegates/Numerical/Taiwanese.lean) consequently proves
that exactly 122 Taiwanese `(3,5)` waits are nonminimal. The paper's total,
live, and minimal counts `149/11/27` remain to be formalized.

[`Minimal/LiveNext`](Ninegates/Minimal/LiveNext.lean) sharpens the nonminimal
classification under copy bound four: for `n>=2`, the live nonminimal
`(n,n+2)` waits are exactly `A_n` plus one sequence avoiding both boundary
ranks. There are exactly `3*n-4` of them, hence five in the Taiwanese case.
Every live `(n,n+2)` wait missing a boundary rank is minimal. In particular,
the class-bound sharpness family `(0,3,3,3,1^(3n-5),3)` is both minimal and live.
These are structural consequences beyond the paper's numbered results.

All 27 numbered propositions and Theorem 1.1 have proofs, as do Examples 4.5
and 6.5. Example 6.6 (`149/11/27`) is deferred because the direct kernel
computation was too expensive in the current prototype. All five unnumbered
remarks now have proofs as well, including the general class-bound sharpness
family and the fixed-class partition of the eight families. Problems 6.1 and 6.4
and Conjecture 6.9 remain open; see
[DEVELOPMENT.md](DEVELOPMENT.md#remaining-paper-statements).
The exact general formula for `M(n)` is neither assumed nor presented as proved.

## Proof structure

Virtual meldability is characterized by size and rank sum modulo three.
Each virtual meldable hand has a unique canonical placement, with sequence
coefficients in `{0,1,2}`. Its triplet coefficients decide actual meldability.
This gives the scan criterion, local tile-moving rules, and interval properties.

The draw-pair relation records which pair can accompany each winning draw.
Missing-rank splits and class bounds force exact class sizes when `m=n+1`.
Two distinguished ranks then supply the only possible pairs. Counting the
sequence starts required by their moves determines the eight families.
Their explicit constructions prove sufficiency, and their coordinate patterns
exclude every live family except Nine Gates.

Minimality is defined for arbitrary meldable removals. A separate theorem
reduces it to single triplet and sequence removals; the latter may either use
a canonical sequence or borrow three covered triplets. No bound on the number
of ranks or candidate hands is used in these arguments.

## Build and validate

Use the pinned **Lean 4.35.0** toolchain and Mathlib revision in
[`lake-manifest.json`](lake-manifest.json):

```sh
lake exe cache get
lake build --wfail
lake env lean -j2 -M4096 -DwarningAsError=true Audit.lean > axioms.log
python3 scripts/check_axioms.py Audit.lean axioms.log
```

The default library target is `Ninegates`. [`Ninegates.lean`](Ninegates.lean)
imports the complete library. The axiom audit covers the foundational results,
classification, bounds, constructions, and explicit examples; it checks the
expected declarations and rejects extra diagnostics or forbidden axioms.

The library has no placeholder proofs and uses only `propext`,
`Classical.choice`, and `Quot.sound`. Small explicit examples and fixed prefix
states use `decide +kernel`; no proof uses native evaluation.

### Comparator

The challenge and solution list all **43 numbered items in published order**,
including definitions, examples, open problems, and the conjecture. Split
statements stay together under their paper number. The public version, links,
source hashes, declaration mapping, and gaps are recorded in
[`paper.json`](ComparatorChallenges/paper.json). There are **120 verified
Comparator targets**, including additional unnumbered constructions and bounds.

```sh
python3 scripts/check_paper_coverage.py
lake build --wfail ComparatorChallenges.Solution
lake comparator --config=ComparatorChallenges/config.json
```

This uses the Comparator bundled with the pinned Lean toolchain and requires
`bubblewrap` with working user namespaces on Linux. The normal command keeps
the sandbox enabled. No external checker is enabled by this configuration.

[`Challenge.lean`](ComparatorChallenges/Challenge.lean) fixes the theorem
statements and imports [`Model.lean`](ComparatorChallenges/Model.lean). The model
shares only the foundational hand, placement, wait, and minimality definitions
with the library; it defines derived objects independently and imports no
project proof modules. Intentional theorem holes are confined to the challenge
and excluded from the default library build.
[`Solution.lean`](ComparatorChallenges/Solution.lean) supplies the library's
proofs, using [`Bridges.lean`](ComparatorChallenges/Bridges.lean) to connect the
derived definitions. Example 6.6 has a visible challenge goal and an explicit
deferred entry in the solution, and is excluded from the verified targets.
The open problems and conjecture are not proof assumptions.
Comparator exports and checks the proofs,
compares their statements against the challenge, and permits only the three
standard axioms above. This complements the larger axiom audit; it does not
claim to certify unfinished results or replace review of the definitions.
The statements use ordinary function notation and explicit zero-based rank
indices. Redundant generated coercions and function-type annotations have been
removed; cast locations and the claims themselves are unchanged. The companion
checker verifies the pinned inventory, order, full source signatures (including
named arguments), and target list with
[`check_paper_coverage.py`](scripts/check_paper_coverage.py).

See the [Lean proof-validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for the meaning and trust assumptions of these checks.

## Library map and conventions

| Path | Contents |
| --- | --- |
| `Hand/` | Vectors, elementary patterns, sums, classes, intervals, reversal |
| `Meldable/` | Placements, canonicalization, scan, movement, splitting, removal |
| `Wait/` | Draw-pair graph, positivity, class bounds, pillars, constructions |
| `Standard/` | Eight named families and the six order-one hands |
| `Classification.lean` | Classification and live uniqueness |
| `Minimal/` | Arbitrary removals, maximal meld counts, lower-bound families |
| `Numerical/` | Exact counts from structural bijections or finite reductions |
| `*Examples.lean` | Explicit examples checking boundaries and hypotheses |

We aim for readable structural arguments and reusable local lemmas. Follow the
[Lean `grind` annotation guidance](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Annotating-Libraries-for--grind/):
apply lemmas without conditionals use `@[simp]`; conditional apply lemmas use
`@[grind]`. Avoid redundant annotations. Keep finite sums inside their owning
modules and provide lemmas for downstream use. Definitions and theorem
statements deserve the same care as their proofs.

## Citation

```bibtex
@misc{xue_beyond_2026,
  title = {Beyond Nine Gates: Classification of Full-Sided Mahjong Waits with $3n$ Ranks},
  doi = {10.48550/arXiv.2611.06944},
  number = {{arXiv}:2611.06944},
  publisher = {{arXiv}},
  author = {Xue, Shubin and Zhong, Xingyu},
  eprinttype = {arxiv},
  eprint = {2611.06944},
}
```

## AI disclosure

The `v3` branch was developed by **Luna**, an autonomous agent designed by
[sun123zxy](https://github.com/sun123zxy), running on **Codex + GPT 6.1 Sol**,
based on the work in the `v2` branch.

The recorded elapsed time from the `v3` task request to the commit containing
the non-enumerative eight-family classification proof was **4 hours 47 minutes
41 seconds**, rounded to the nearest second.

| Milestone | Commit | Library Lean LOC | Total Lean LOC |
| --- | --- | ---: | ---: |
| `v2` baseline | [e45fd51](https://github.com/lunaluteus/ninegates-lean4/commit/e45fd512ebb2cd0bac7d69690f3163647bdc3bc8) | 5,426 | 5,466 |
| Eight-family structural classification | [486a557](https://github.com/lunaluteus/ninegates-lean4/commit/486a55762bf812ae0ac44d98bc422d038e68c251) | 6,781 | 7,183 |
| First stable `v3` snapshot | [a001009](https://github.com/lunaluteus/ninegates-lean4/commit/a001009c34b9e8c35fab82c18ffeb67d2f490141) | 10,594 | 13,436 |

Counts are physical lines in tracked `.lean` sources, including comments and
blank lines, and excluding dependencies. Library LOC covers the implementation;
total LOC also includes its Comparator and audit sources. At the eight-family
milestone, the new implementation was under `Ninegates/V3/` with root
`NinegatesV3.lean` and audit `V3Audit.lean`; the unchanged `v2` sources that still
coexisted in that commit are excluded from its counts.

As of November 2026, development through the first stable snapshot used roughly
**10% of the weekly usage limit of a US$100 ChatGPT subscription**, according to
the account holder's estimate.
