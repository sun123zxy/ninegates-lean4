<div align="center">

<h1>
<p>Nine Gates: A Lean 4 Mahjong Game Formalization</p>
<p style="font-size: 200%">🀇🀇🀇🀈🀉🀊🀋🀌🀍🀎🀏🀏🀏</p>
</h1>

Classification of full-sided waits and uniqueness of the *Nine Gates (九蓮宝燈)* live full-sided wait in the generalized *Mahjong* game  
Formally verified in Lean 4

[![Repository](https://img.shields.io/badge/Github-ninegates--lean4-2d4a66?style=flat-square&logo=github&logoColor=white)](https://github.com/sun123zxy/ninegates-lean4 "Github")
[![Documentation](https://img.shields.io/badge/Documentation-ninegates--lean4-2ea44f?style=flat-square&logo=readthedocs&logoColor=white)](https://sun123zxy.github.io/ninegates-lean4/docs "Documentation")
[![Visualization](https://img.shields.io/badge/Visualization-ninegates--viz-6b4a8f?style=flat-square&logo=svg&logoColor=white)](https://sun123zxy.github.io/ninegates-viz/ "Visualization")

</div>

> We are working on a paper that focuses on the mathematical aspects of this project. It will be available on arXiv soon. Note that there have been substantial updates to the paper and the codebase may not be fully synchronized.

## Introduction

### Problem

Nine Gates is the celebrated one-suit Mahjong wait `1112345678999`. With the usual nine ranks, this 13-tile hand wins after drawing *any* rank from `1` through `9`. We consider a generalized version with `3 * n` ordered tile types. In this generalization, `n + 1` melds and a pair are required to win. The uniqueness problem asks whether this pattern is the only legal hand that waits on every tile type. It's long been known that the answer is "yes" for the usual `n = 3` case, mostly with informal reasoning and computer search.

### Our work

Our formalization classifies all full-sided waits, without imposing the four-copy limit, and derives live uniqueness for all `n ≥ 2`.

The main results are in [`Ninegates/Classification.lean`](Ninegates/Classification.lean), in the `Mahjong.Hand` namespace:

- `isFullWait_iff_eightFamily`: for `n ≥ 2`, the full-sided waits are exactly the eight standard families `A`, `B`, `B'`, `C`, `C'`, `D`, `D'`, and `E`.
- `orderOne_isFullWait_iff_isOrderOneFamily`: for `n = 1`, the full-sided waits are exactly the six hands in `Standard.One`; all six are live.
- `liveFullWait_unique`: for every `n ≥ 2`, every *live full-sided wait* is exactly `Standard.A n`. "Live" means that each prospective draw still respects Mahjong's four-copy limit. This follows from the classification by excluding the other seven families with the `<= 4` multiplicity condition. The usual Nine Gates hand is `Standard.A 3`.

Our proof combines

- formal mathematical reasoning: reducing possible counterexamples to a finite set of small-order candidates
- candidate enumeration: verifying ~5000 candidates for $n = 1,2$ and $3 \leq n \leq 7$ respectively, with correctness proofs
- efficient verified computation: fast algorithms for deciding meldability, winning, and waiting, fully verified

With Lean 4, all of these can be expressed in a single language.

We also prioritizes the following design goals:

- **Maintainability**: This repository is a human-written formalization with limited assistance from coding agents. Conscious effort has been made to rewrite the code into a clean and readable structure.

- **Proof Automation**: Smooth `grind` and `simp` automation requires careful design of the library structure and lemma annotations.

- **Program Verification**: We explored how to verify executable algorithms in Lean 4 and use them in a mathematical proof.

## Soundness

- verified in Lean `v4.33.0`

- standard axioms `propext`, `Classical.choice`, `Quot.sound` applied; additional `native_decide` axiom for finite enumeration and meldability / winning / waiting algorithms

- all theorems are verified via a `lake build` with no `sorry`s or additional axioms

- `fullWait_reduction` in [`Ninegates/Counterexample/Reduction.lean`](Ninegates/Counterexample/Reduction.lean) is verified by [Comparator](https://github.com/leanprover/comparator), which is the most mathematically significant part of the proof. We could not verify the main theorem with Comparator due to its lack of support for `native_decide`.

Note that `native_decide` relies on the correctness of Lean 4's compiler. It is a reasonable assumption for our purpose, as enumerating small cases requires efficiency, and verifying executable algorithms is among the goals of this project. Switching to a `decide` version is technically possible, but it does not work smoothly with `ExtHashSet`'s opaque implementation (used by our DP-based winning check algorithm) and could be extremely slow for the program verification purpose.

## Autoformalization, agentic coding and curated formalization

Autoformalization is cool but often produces unmaintainable code. As of Augest 2026, full-auto AI formalization agents like Archon + GPT 5.5 has proven their growing capability of generating mathematically correct Lean code at scale, but they almost always produce redundant glue code and cumbersome proof steps, which can be tedious to maintain and verify. For example, native GPT 5.6 is still ignorant of the `grind` tactic and its automation power, nor can it annotate the code with `@[grind]` and `@[simp]` properly without human guidance. A neat, curated library design and annotation still require human expertise and intervention.

This repository is a human-written formalization with limited assistance from coding agents. We used AI to help us with the following tasks:

- The first run is a complete autoformalization generated by [Archon](https://github.com/frenzymath/Archon) + Codex + GPT 5.5. The counterexample reduction lemma is formally verified, convincing ourselves that the proof is correct. See the archived results in the `v1` branch of this repository.

- The second rewrite is a fresh human-written formalization with limited assistance from coding agents like Codex + GPT 5.6. It is curated to be readable and maintainable. Important definitions are written by humans, structural decisions are made by humans, and proof automation (e.g `simp` / `grind` annotation) is designed by humans. We only sit back and relax ourself a bit for the program verification part, which is generally acceptable and safe. 

To wrap up, AI did the first pass to verify the correctness, and accelerated our exploration of different formalization designs in the second pass. Conscious effort has been made to rewrite the code into a clean and readable structure. As one of the statistical milestones, on the path towards the proof of the counterexample reduction lemma of live full-sided waits, by carefully redesigning, restructuring, and annotating the Archon + GPT 5.5 generated 2604 lines of Lean code, we have reached a 70% reduction in line count, a 770-line Lean codebase that is much more maintainable and readable, while improving the proof structure and automation power. We observed that  clean organization and proper annotation significantly simplifies the proof of trivial lemmas: most of them can be closed by a brainless `ext; simp_all; grind` combo if proper conditions are provided.

Hidden mathematical insights also emerge as we reorganize the codebase. The relationship among the canonical placement, canonicalization of a placement, and the meldability scanning algorithm is discovered during the second pass. It turns out that these ideas are of fundamental importance, if one broaden one's scope to a more general setting of Mahjong hands. This generalization is currently under our active development.

> We report that recent advances in top-tier LLMs has shown their improved ability to generate organized Lean code. In some recent development of this repository, compared to the previous GPT 5.6 Sol model, we observed that GPT 6 Astra could generate neat proofs with significantly improved readability and maintainability, demonstrating its understanding of the `grind` tactic and the overall library structure. A basic SKILL file is used to guide the agent to read the official `grind` / `simp` guideline and follow the library's automation policy. One may expect that future LLMs may spare more human effort in curating the codebase.

## `grind` / `simp` Automation Policy

Smooth `grind` and `simp` automation is the major design goals of this library. Intuitively, `simp` does a normal form reduction, while `grind` is a union-find algorithm that equates terms and splits cases. Respecting the heterogeneous nature of the two tactics' inner mechanisms is crucial to maximize the automation power of both.

In general we follow the [official `grind` annotation guideline](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Annotating-Libraries-for--grind/), which results in the following rules of thumb:

- Make `xxx_apply` lemmas to hide `.mk`.

- `@[simp]` apply lemmas it if it has no `if`.
- `@[grind]` apply lemmas if it has `if`.
- Do not `@[grind]` other apply lemmas if a general `if`-lemma is already `[@grind]`.
- `@[grind]` definitions directly only if they have no corresponding lemma.

- Hide the definition if it contains `∑`: Don't `@[grind]` or `@[simp]` it. Provide lemmas for downstream use. Reserve the responsibility manipulating `∑` on our side.

This set of rules turns out to be effective, resulting a brainless `ext; simp_all; grind` combo almost always works for mathematically trivial lemmas. We have multiple positive examples in this library. Some of them are listed here for reference:

- `Placement.toHand_apply`: For apply lemmas containing `if`. See [`Meldable.Basic`](Ninegates/Meldable/Basic.lean) documentation for a closer look.

- `Hand.size` and `Hand.sum`: For definitions containing `∑`. See [`Ninegates/Operations/Basic.lean`](Ninegates/Operations/Basic.lean) documentation for a closer look.

In practice, as `grind` has a upper limit on the number of case splits (though it is configurable by `grind (splits := 20)`), it is still recommended to manually perform the case split and `simp` with the case conditions before invoking `grind` for the remaining proof obligations.

## Verification & development setup

### Quick start

You'll need a Lean 4 environment with `lake` installed. Then

```sh
lake update
lake exe cache get
```

Above commands download dependencies (such as `Mathlib`) and their cache. Then a quick

```sh
lake build Ninegates
```

serves as a basic verification of the library.

### Comparator

See the guidelines provided by [Comparator](https://github.com/leanprover/comparator) and configure it yourself if the strongest guarantee of correctness is desired. We provide our configuration below for your reference.

- First, you'll have to configure a Linux environment with [`landrun`](https://github.com/Zouuup/landrun) installed. 

  - This is the most convenient way to run Comparator. Otherwise things might go very tricky! Use WSL2 if you are on Windows.
  - `landrun` is a Go program. Very likely, you'll have to install `go` as well.

- Comparator requires `lean4export` executable. We include it as a dependency in our `lakefile`, so build it with
  
  ```sh
  lake build lean4export
  ```
  
  so that you can find it at `.lake/packages/lean4export/.lake/build/bin/lean4export`.

- Set the environment variable `COMPARATOR_LEAN4EXPORT` to point to the executable, that is,
  
  ```sh
  export COMPARATOR_LEAN4EXPORT=".lake/packages/lean4export/.lake/build/bin/lean4export"
  ```

  This tells Comparator where to find the executable.

- Finally, run the following command to verify the main theorem:

  ```sh
  systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c 'lake exe comparator ComparatorChallenges/config.json'
  ```

  If it fails, retreat to a simpler version (less secure) without `systemd-run`:

  ```sh
  lake exe comparator ComparatorChallenges/config.json
  ```

  If you see `Your solution is okay!` in the output, congratulations! Verification is successful.

### Agentic coding

We use [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) + [repl](https://github.com/leanprover-community/repl) for compiler feedback.

- `lean-lsp-mcp` is a MCP server that allows agentic interaction with the Lean theorem prover via the Language Server Protocol, provides a range of tools for LLM agents to understand, analyze and interact with Lean projects.
- `repl` is a Lean 4 REPL. Used by `lean-lsp-mcp` to accelerate the agent-compiler feedback loop.

See their documentation for detail instructions. In short, you'll need to add `lean-lsp-mcp` as an MCP server for your agent. The command to run the server is `uvx lean-lsp-mcp --repl`. Note that `repl` is already included in our dependency list. So just run `lake build repl` to build it before use.

## Reading the code

Rich documentation is provided in the code itself. The following is a brief overview of the library structure.

### Conventions

In general, `Defs` modules contain basic definitions, and `Basic` modules contain basic lemmas directly related to the definitions. (`Algo` / `Spec`), or (`Decide` / `Decidable`) modules contain executable algorithms and their correctness proofs.

The separation of `Defs` and `Basic` modules allows us to state the main results without too many dependencies, imporant for a Comparator verification. As they are closely related, for simplicity, we do not distinguish between `Defs` and `Basic` modules when referencing them in the following map.

### Map

- [`Ninegates/Basic.lean`](Ninegates/Basic.lean) is the foundation: it represents a hand as a counting vector over `3 * n` ordered tile types and defines the elementary patterns, hand size, weighted sum, and four-copy validity.

- [`Ninegates/Operations/`](Ninegates/Operations/) defines useful operations on hands, including insertion and removal of a sequence.

- [`Ninegates/Standard/`](Ninegates/Standard/) concerns the eight full-wait families and six order-one hands.
  
  - `Basic` supplies the eight standard families and 6 order-one hands;
  - `Insert` provides the family insertion lemmas;
  - `Wait` proves their full-wait and liveness properties;

- [`Ninegates/Meldable/`](Ninegates/Meldable/) formalizes decompositions into triplets and sequences. 

  - `Basic` supplies meld placements and `Meldable`;
  - `Split` allows you to split a meldable hand by a zero rank in the middle.
  - `Canonical` defines when a placement is considered canonical.
  - `Decidable` verifies an executable left-to-right scanner that decides whether a hand is meldable, and when it is, produces a canonical placement.

- [`Ninegates/Winning/`](Ninegates/Winning/) defines winning hands as a meldable remainder plus a pair.
    
  - `Decide` and `Decidable` implements a dynamic programming decision procedure for winning hands and proves its correctness.

- [`Ninegates/Wait/`](Ninegates/Wait/) defines waits and live waits.

  - `Decidable/` implements how we decide waiting tiles and waits.
    
    - `Basic` defines some trivial procedures for deciding waits.
    - `Algo` and `Spec` implement the prefix/suffix waiting-tile algorithm and its correctness proof.

- [`Ninegates/Counterexample/`](Ninegates/Counterexample/) contains the counterexample reduction, enumeration and finite elimination:

  - `Basic`: defines a counterexample as a full-sided wait outside the eight standard families.
  - `Reduction`: reduces counterexamples to orders 2 through 7.
  - `EnumAlgo` and `EnumSpec`: implement and verify the unified candidate enumeration for orders 1 through 7, and show that every minimal counterexample is enumerated.
  - `Elimination`: rules out counterexamples among the candidates via `native_decide`.

- [`Ninegates/Classification.lean`](Ninegates/Classification.lean) stores our main results: the classification of full-sided waits and the uniqueness of the live full-sided wait.

## Future work

- Decoupling computation from Mathlib: Mathlib is designed to be noncomputable. The current instantiate-`Decidable` approach has already caused some friction, e.g. deciding `Winning` forces the use of `native_decide`. A canonical computable definition (established with a connection to the Mathlib-based definition) should be fixed. This layer should not be hidden and casually handovered to coding agents.

  We are aware of [Hex](https://github.com/leanprover/hex)'s practice of separating computation from Mathlib, and are considering applying a similar approach in our future work.

- `vcgen`: We are aware of the newly emerged `vcgen` tactic in Lean 4. We tried to use it in our spec modules, but turned out to gain little benefit. Also, currently coding agents are not enough familiar with it.

- Module system: Currently Lean's module system is ported but not fully utilized. Our Mathlib-flavored design of `Hand` relies heavily on its internal representation. Future work should first redesign of `Hand`'s internal representation, then refactor the library to seperate implementation from interface, and finally make good use of the module system.

- A more general algebraic Mahjong theory: As mentioned before, inspired by the properties of canonical placements discovered in the curation process, we are working on a more general framework where the uniqueness of full-sided waits becomes a special case of a general classification problem.
