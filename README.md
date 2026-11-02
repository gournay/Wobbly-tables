# Balancing non-rectangular tables

Antoine Gournay (TU Dresden)

This repository contains the paper *Balancing non-rectangular tables*, a formalisation of most of its
results in the proof assistant [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), and the Python scripts used for the
computer-assisted parts of the proofs and for the numerical experiments.

## Abstract

Balancing square and rectangular tables by rotation has been an interesting way to illustrate the
intermediate value theorem. This article studies the same question for tables whose feet form a
cyclic quadrilateral, following a conjecture of A. Martin. In the idealised model behind this
conjecture, the balancing act works for every such table and is a nice application of the ergodic
theorem. For the actual rigid table on a Lipschitz terrain, the situation is more subtle. If the
terrain is flattened enough, the table can be stabilised unless an idealised wobbling function
vanishes identically, i.e. unless the terrain is degenerate for the table. Even if this should
happen, the tables whose feet are vertices of a regular polygon and which satisfy a non-degeneracy
condition of their own can still be stabilised on every terrain with a small enough Lipschitz
constant (e.g. a halved regular hexagon as long as the slope is less than 3.7°). On the other hand,
there is an isosceles trapezoid and another table, which are shown to wobble at every angle on
suitable terrains however small the Lipschitz constant is. These counterexamples are fragile: for
every table, if the idealised wobbling function vanishes identically for every position of the
rotation axis in a small disc, then, near the feet, the terrain is a plane or a paraboloid of
revolution with a vertical axis; so in practice a slight move of the axis makes the terrain
non-degenerate. The results are, with minor exceptions, formalised in Lean.

## Contents

| Path | Content |
|---|---|
| `tex/wobbly28.tex` | the paper (LaTeX source) |
| `lean/` | the Lean formalisation; see [`lean/README.md`](lean/README.md) |
| `numerics/` | Python scripts: certified computations and numerical experiments |
| `LICENSE`, `LICENSE-CC-BY-4.0` | the licences (see below) |

## The paper

The source only uses standard LaTeX packages. To compile it:

```
cd tex
pdflatex wobbly28.tex
pdflatex wobbly28.tex   # second run for the cross-references
```

The number in the file name is the version of the paper.

## Lean formalisation

The following statements are formalised in Lean 4 / Mathlib (`v4.34.1`), without `sorry`:

* all the statements of Sections 4 and 5, including Lemma 4.1 (the rotation `S_q` and the
  coordinates of the feet) and Proposition 4.13 for every table, the square included;
* the mathematical statements made in the remarks of Sections 4 and 5, but not their numerical
  observations, the heuristic computation of Remark 4.12, or the list of the degenerate rational
  tables with `n ≤ 12` in Remark 5.13(b), which is a numerical check;
* Theorem 2.2 in the idealised model of Remark 2.3(b).

This includes the computer-assisted Theorem 5.7 and Proposition 5.8. Their Lean proofs are
numerically weaker than the paper: they give `w_AC ≥ ε³` for `0 < ε ≤ 10⁻³` (instead of
`ε ≤ 4·10⁻³`) in Theorem 5.7, and `w_AC ≥ 0.3 ε³` for `0 < ε ≤ 5·10⁻⁴` (instead of `ε ≤ 10⁻³`) in
Proposition 5.8.

To build:

```
cd lean
lake exe cache get   # download the prebuilt Mathlib (optional)
lake build
```

[`lean/README.md`](lean/README.md) lists the files, gives the correspondence between the statements of
the paper and the Lean theorems, and describes the differences with the paper.

## Numerics

The scripts need Python 3 with `mpmath` (for `always_wobbles.py`) and `numpy` (for the others);
`scipy` and `cma` are needed for some options of `physical.py` and `wobble.py`.

| Script | Content |
|---|---|
| `always_wobbles.py` | the computer-assisted part of the proofs of Theorem 5.7 and Proposition 5.8 (tables which wobble at every angle), with interval arithmetic; `--nonlinear` also computes the wobbling function directly |
| `physical.py` | physical size of the effect, and what happens when the rotation axis is moved (Remark 5.9(f)); `--optimise` re-optimises the terrain for a prescribed maximal slope |
| `orbit_slopes.py` | the largest Lipschitz constants allowed by Theorem 5.11 (Remark 5.13(c)) |
| `wobble.py` | floating point experiments: the hexagonal table (Proposition 5.4, Corollary 5.5), a search for terrains on which the hexagonal table wobbles at every angle, and an earlier numerical example of an isosceles trapezoid which wobbles at every angle |

## Use of AI

The Lean code was written and cross-checked with the help of the AI systems Claude (Anthropic,
through Claude Code) and Aristotle (Harmonic). The Python scripts in `numerics/` were written with the
help of Claude.

## Licence

Copyright 2026 Antoine Gournay.

* The code (the Lean formalisation in `lean/` and the Python scripts in `numerics/`) is licensed
  under the [Apache License 2.0](LICENSE), like Mathlib.
* The paper (`tex/`) is licensed under the
  [Creative Commons Attribution 4.0 International licence](LICENSE-CC-BY-4.0) (CC BY 4.0).
