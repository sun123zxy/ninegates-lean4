# Ninegates Autoformalization

This repository formalizes the structural reduction for generalized pure-suit nine-gates hands in an `n`-rank mahjong model, where `n` is a positive multiple of three.

We use [Archon](https://github.com/frenzymath/Archon) + Codex + GPT 5.5 to formalize the results in Lean 4.

## Structure

- `Ninegates/` — main Lean source
- `blueprint/` — leanblueprint source
- `references/` — source notes (in Chinese) backing the formalization

## Build

```bash
lake exe cache get
lake build
```

## Run the autoformalization loop

```bash
archon loop .
```

