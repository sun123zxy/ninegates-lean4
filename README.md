# Nine Gates: A Mahjong Game Formalization in Lean 4

## Introduction

TODO

## Reading the code

TODO: Order of reading the files.

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

- `Placement.toHand_apply`: For apply lemmas containing `if`. See `Meldable.Basic` documentation for a closer look.

- `Hand.size` and `Hand.sum`: For definitions containing `∑`. See `Basic` documentation for a closer look.

In practice, as `grind` has a upper limit on the number of case splits (though it is configurable by `grind (splits := 20)`), it is still recommended to manually perform the case split and `simp` with the case conditions before invoking `grind` for the remaining proof obligations.

## GitHub configuration (TODO: Clean this up)

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
