# Lean formalisation of §4 and §5 of the paper

The numbering is that of the current version of the paper, in `tex/`.

**Status: compiles with Lean `v4.34.1` and Mathlib `v4.34.1`, without `sorry` and without
warnings.** All the theorems only depend on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The Lean code was written and cross-checked with the help of the AI systems Claude (Anthropic,
through Claude Code) and Aristotle (Harmonic).

## Build

```
lake exe cache get   # download the prebuilt Mathlib (if cache.mathlib.org is reachable)
lake build
```

Mathlib is pinned to the release `v4.34.1` (Lean `v4.34.1`) through its git URL in
`lakefile.toml`. Without access to the Mathlib cache, `lake build` compiles the needed part of
Mathlib from source (about 2100 files).

## Model

The horizontal plane is `ℂ`; `dot` is the Euclidean inner product and `rot θ = exp (iθ)`.
A position of the table is `(θ, q, c)`; the foot which is at `a` in the frame of the table is at the
horizontal position `foot (rot θ * a) q = rot θ * a - Φ (rot θ * a) q` and at the height
`c + dot (rot θ * a) q`. These formulas of Lemma 4.1 are used as the definition of the model;
`Wobbly/Coordinates.lean` derives them from the rigid motion `S_q ∘ R_θ` of the paper. The terrain is
a function `g : ℂ → ℝ` with `IsLip g L` (`|g x - g y| ≤ L ‖x - y‖` for all `x, y`).

## Files

* `Wobbly/Basic.lean`: the map `Φ`, Lemma 4.2, Lemma 4.3, an explicit solver for 2×2 systems.
* `Wobbly/Coordinates.lean`: Lemma 4.1. The rotation `S_q` as a matrix of `SO(3)`, its axis and
  angle, the coordinates of the feet, equation (4.1), and the decomposition `T = S_q ∘ R_θ` of the
  rotations which neither turn the table upside down nor make it vertical.
* `Wobbly/Hover.lean`: tables, the smallness assumption (4.3), Proposition 4.4.
* `Wobbly/Wobble.lean`: the wobbling function, Lemma 4.7 and Propositions 4.8–4.10.
* `Wobbly/Remainder.lean`, `Wobbly/Taylor.lean`: Proposition 5.2 (third order term with an explicit
  remainder) and the scaling of the remainder.
* `Wobbly/Modes.lean`: degenerate Fourier modes, Lemma 5.3.
* `Wobbly/ClosedForm.lean`, `Wobbly/Degenerate.lean`: Proposition 5.6.
* `Wobbly/PolyCalc.lean`: calculus for the terrains `Re(z^k) + ½(|z|² - 1) Re(b z^{2k})`.
* `Wobbly/Rational.lean`: Corollary 4.11, Proposition 5.4, Corollary 5.5.
* `Wobbly/Rectangle.lean`: Theorem 5.1.
* `Wobbly/TrapezoidCex.lean`: Theorem 5.7 (an isosceles trapezoid which wobbles at every angle).
* `Wobbly/UneqCex.lean`: Proposition 5.8 (a table with diagonals of different lengths which
  wobbles at every angle).
* `Wobbly/Orbit.lean`: rational tables and Theorem 5.11 (with coercivity as a hypothesis).
* `Wobbly/Coercive.lean`: coercivity of the circulant operator from `m(s) ≠ 0` (discrete Fourier
  transform and Parseval's identity), hence Theorem 5.11 for every non-degenerate rational table.
* `Wobbly/Hexagon.lean`: the hexagonal table and Corollary 5.12.
* `Wobbly/Axis.lean`: Proposition 4.13 (moving the axis) for globally Lipschitz terrains and
  non-square tables (Liouville argument), and the Fourier coefficients on circles.
* `Wobbly/AxisLocal.lean`: Proposition 4.13 (a) (local version) and (b) for continuous terrains,
  for every table (including the square).
* `Wobbly/Smooth.lean`: Proposition 4.4, regularity (if `g` is `C^k`, so are `q_AC` and `c_AC`),
  by the implicit function theorem.
* `Wobbly/Classification.lean`: Lemma 5.3 (f), the shape of the table when `4` or `5` is a
  degenerate mode (isosceles trapezoids, the family `G_χ` with `χ ∈ ]0, π/4]`), and the fact that
  the diagonals of a table are never parallel.
* `Wobbly/Extras.lean`: the theorem of §2 in the idealised model (`Table.idealised_balance`) and the
  Chebyshev form of Lemma 5.3 (c) (`trapezoid_m_eq_zero_iff_chebyshev`).
* `Wobbly/Strengthened.lean` (added by Aristotle, Harmonic): Corollary 4.11, Proposition 5.4, Corollary 5.5 with the conclusion of the
  paper ("four feet on the ground", with (4.3) holding), and Theorem 5.11 with exactly the hypotheses
  of the paper (assumption (4.3) derived, not assumed).
* `Wobbly/Remarks4.lean`: the remarks of §4 (Remarks 4.5 and 4.12).
* `Wobbly/Remarks5.lean`: the remarks of §5 (Remarks 5.9, 5.10, 5.13 and 5.14 (a)).
* `Wobbly/Ergodic.lean`: Weyl's equidistribution theorem, and the ergodic averages of `w_AC` along an
  irrational rotation (Remark 5.14 (a)).

## Correspondence with the paper

| Paper | Lean |
|---|---|
| Theorem 2.2 (idealised model of Remark 2.3) | `Table.idealised_balance` |
| Lemma 4.1: `S_q ∈ SO(3)`, `S_0 = Id` | `Wobbly.S_mem`, `Wobbly.S_zero` |
| Lemma 4.1: `S_q` is the rotation around the horizontal axis orthogonal to `q`, by the angle `arcsin ‖q‖`, which lifts `q` | `Wobbly.S_axis`, `Wobbly.S_dir`, and uniqueness: `Wobbly.S_unique` |
| Lemma 4.1: coordinates of the feet | `Wobbly.feet_eq` (and `Wobbly.S_pt`; the residual: `Wobbly.resid_eq`) |
| (4.1) | `Wobbly.plane_eq` |
| decomposition `T = S_q ∘ R_θ` (§4.1) | `Wobbly.exists_S_mul_Rz`, `Wobbly.S_mul_Rz_inj`, `Wobbly.S_mul_Rz_mem` |
| Lemma 4.2 (bounds on Φ) | `Wobbly.norm_Φ_le`, `Wobbly.norm_Φ_sub_le`, `Wobbly.psi_le` |
| shadow is smaller than the table | `Wobbly.norm_sub_Φ_le` |
| Lemma 4.3 | `Wobbly.sq_norm_le_of_abs_dot_le`, `Wobbly.norm_solve2_le` |
| (4.3) smallness assumption | `Wobbly.Table.SmallL` |
| Proposition 4.4 (existence, uniqueness, continuity) | `Table.existsUnique_tilt`, `Table.norm_tilt_le`, `Table.continuous_tilt` |
| Proposition 4.4 (`C^k` regularity) | `Table.contDiff_tilt`, `Table.contDiff_cAC` |
| Lemma 4.7 (four feet on the ground ⇔ w = 0) | `Table.four_feet_iff` |
| Proposition 4.8 (formula for w) | `Table.wob_eq` |
| Proposition 4.9 (common tilt, w_BD = -w_AC) | `Table.hover_BD`, `Table.hover_BD_unique` |
| Proposition 4.10 (comparison with F₀) | `Table.abs_wob_sub_F₀_le` |
| continuity of w | `Table.continuous_wob` |
| Corollary 4.11 | `Table.exists_stable_of_F₀` (with `∫ F₀ = 0`: `Table.integral_F₀`); paper form: `Table.exists_four_feet_of_F₀` |
| Proposition 4.13 (a) (local version) | `Axis.paraboloid_of_F₀v_local` (converse: `Axis.F₀v_of_paraboloid`) |
| Proposition 4.13 (b) | `Axis.paraboloid_of_F₀v`; Lipschitz terrains: `Axis.affine_of_F₀v_all` (and `Axis.affine_of_F₀v`, non-square tables, Liouville argument); link with `F₀`: `Axis.F₀v_eq_F₀` |
| Proposition 4.13, the square | `Axis.m_sq_ne_zero`, `Axis.sq_eig`, `Axis.sq_dz_dz`, `Axis.sq_van`, `Axis.van_sq` |
| Theorem 5.1 (rectangles) | `Table.rectangle_stable`, `Table.rectangle_wob_zero` |
| Proposition 5.2 | `Table.abs_wob_sub_third_order_le`, `Rem`, `Rem_le_scale` |
| Lemma 5.3 (c), Chebyshev form | `trapezoid_m_eq_zero_iff_chebyshev` |
| Lemma 5.3 (a)–(d) | `Feet.m_zero`, `Feet.m_one`, `Feet.m_odd_of_rectangle`, `trapezoid_m`, `trapezoid_four_iff`, `Feet.m_eq_zero_of_rational` |
| Lemma 5.3 (e) | `Feet.m_two_ne_zero`, `Feet.m_eq_zero_iff`, `Feet.interp_coeffs` |
| Lemma 5.3 (f) | `Feet.m_three_iff`, `Feet.m_four_iff`, `Feet.m_five_iff`, `Feet.m_three_iff_rectangle`, `Feet.diag_eq_of_m_three_or_four`, `Feet.m_five_family'` |
| Lemma 5.3 (f), shape of the table | `Feet.isoTrap_of_m_four` (`4 ∈ 𝒦` ⇒ isosceles trapezoid), `Feet.m_five_classification'` (`5 ∈ 𝒦` ⇒ isosceles trapezoid or `G_χ`, `χ ∈ ]0, π/4]`), `Feet.isoTrap_of_diag_eq`, `Feet.nonParallel` |
| Proposition 5.4 | `Table.F₀_eq_zero_of_affine`, `Table.sum_w3_orbit`, `Table.exists_stable_of_w3`; paper form: `Table.exists_four_feet_of_w3` |
| Corollary 5.5 | `Table.hexagon_stable` (with `Table.hex_affine_of_F₀`); paper form: `Table.hexagon_four_feet` |
| Proposition 5.6 | `Feet.w3_eq_full`, `Feet.w3_eq`, `Table.idealTilt_eq`, `Table.W3_ge` |
| Theorem 5.7 | `trapezoid_wob_ge`, `trapezoid_wobbles`, `trapezoid_terrain_exists` (`W₃ ≥ 1.4`: `trap_W3_bound`) |
| Proposition 5.8 | `Uneq.uneq_wob_ge`, `Uneq.uneq_wobbles`, `Uneq.uneq_terrain_exists`, `Uneq.uT_diagonals` (`W₃ ≥ 0.45`: `Uneq.u_W3_bound`) |
| Theorem 5.11 | `Table.exists_balanced_of_paper` (hypotheses exactly as in the paper), `Table.exists_balanced_of_nondeg` (the conditions of the paper give the orbit data: `Table.OrbitData.of_paper`; from `Table.exists_balanced`, `Table.not_all_pos` and `coercive_of_nondeg`) |
| Corollary 5.12 (hexagon, L ≤ 0.065) | `Wobbly.hexagon_balanced` |

### The remarks

| Paper | Lean |
|---|---|
| Remark 4.5 (a): for the square, (4.3) reads `L ≤ 1/(2√2)`, slopes up to about 19.5° | `square_smallL_iff` (`square_K`, `square_dmin`), `square_slope` (`arctan(1/(2√2)) = arcsin(1/3)`), `square_slope_deg` (between 19.4° and 19.5°) |
| Remark 4.5 (b): (4.3) is symmetric in the diagonals, equal hovering position with respect to `BD` | `Table.swap`, `smallL_swap_iff`, `existsUnique_hover_BD` |
| Remark 4.12: Fourier coefficients of `F₀`; `F₀ ≡ 0` iff only degenerate modes | `integral_F₀v`, `F₀v_eq_zero_iff` (and `Feet.m_zero`, `Feet.m_one`, `Feet.m_odd_of_rectangle`) |
| Remark 4.12: `tr M = 0`, `M` not definite | `Feet.Mq`, `Mq_eq`, `Mq_add_Mq_I`, `Mq_not_pos`, `Mq_not_neg` |
| Remark 4.12: the ellipse, the inequality, the form vanishes on the ellipse | `exists_Mq_idealTilt_eq_zero`, `exists_re_mul_sq_eq_zero`, `abs_normSq_sub_le` |
| Remark 5.9 (a): generic tables, `g₁` affine on the circle, `q₀` constant, `W₃` has mean `0` and changes sign | `affine_on_circle`, `affine_on_circle_of_generic`, `idealTilt_const`, `w3_eq_F₀` (with `tangential_of_affine`), `W3_generic` |
| Remark 5.9 (a): rational tables, orbit sums of `W₃` | `sum_F₀_orbit`, `sum_W3_orbit`, `W3_rational` |
| Remark 5.9 (a): `S = 0` for the extra mode `n/2` of the degenerate rational trapezoids (and for `𝒦_n`) | `Feet.Sk`, `Feet.κ_eq`, `Feet.Sk_eq_zero_of_pm`, `Feet.Sk_eq_zero_of_rational` |
| Remark 5.9 (a): `k ≥ 5` if the diagonals differ | `Feet.five_le_of_diag_ne` |
| Remark 5.9 (e): pentagon (`χ = 0`) and hexagon (`χ = π/4`), `S = 0` there | `Qχ_zero`, `Qχ_zero_root`, `Qχ_pi_div_four`, `Qχ_pi_div_four_root`, `Sk_pentagon`, `Sk_hexagon` |
| Remark 5.9 (e): the tables of the family are not isosceles trapezoids, diagonals differ | `not_isoTrap_of_s₁`, `diag_ne_of_s₁` |
| Remark 5.9 (f): moving the axis gives `F₀^{(1)} ≢ 0` | `trapezoid_axis_moved` |
| Remark 5.9 (g): the trapezoid of Theorem 5.7 cannot be balanced locally (any rotation in `SO(3)`, centre on the axis) | `OnGround`, `trapezoid_not_locally_balanced` (`trapezoid_not_upright`, `trapezoid_not_upside_down`, `trapezoid_not_vertical`, `flipX`, `height_sub_sq_le`) |
| Remark 5.10: rotation between the diagonals, the exact chain presupposes the conclusion | `diag_sq_sub`, `exists_rot_of_diag_eq`, `resid_rot_chain`, `chain_presupposes` |
| Remark 5.13 (b): the extra degenerate mode `n/2` of the degenerate rational trapezoids | `τ_eq_μ_of_symm`, `m_eq_zero_of_symm`, `exp_pow_real` |
| Remark 5.13 (c): `σ → 0` along approximating rational tables | `exists_small_mode_of_tendsto` |
| Remark 5.13 (d): `min x ≤ -½ max x` without modes `0, ±1` (`n = 6`) | `exists_le_neg_half_max` |
| Remark 5.14 (a): `∫ w_AC = ∫ (w_AC - F₀) = O(L³)`, not `0` in general | `integral_wob`, `integral_wob_trapezoid_pos` |
| Remark 5.14 (a): ergodic averages along an irrational rotation | `tendsto_avg_of_irrational` (Weyl), `wob_periodic`, `tendsto_avg_wob` |
| Remark 5.14 (a): `inf |m(k)| = 0` over the non-degenerate modes of an irrational table | `Feet.IsRat`, `Feet.isRat_of_three`, `Feet.exists_small_nondegenerate_mode` |

### Differences with the paper

* **Proposition 4.4.** The regularity uses Mathlib's implicit function theorem for
  `F(θ, q) = Q_θ(q) - q` rather than a direct argument.
* **Lemma 5.3 (f).** "Isosceles trapezoid (or rectangle)" is formalised as `Feet.IsoTrap`: the feet
  are invariant under a reflection `z ↦ u z̄` which fixes no foot. "Up to rotations and
  reflections" is a map `z ↦ ω z` or `z ↦ ω z̄` with `|ω| = 1`.
* **Proposition 4.13.** Formalised for every table, including the square. The region swept by the
  feet is `Axis.Ω r v₀ R₀ = {x | ∃ v ∈ B(v₀, R₀), ‖x - v‖ = r}`, the terrain is only assumed
  continuous on it, and the paraboloids are `Axis.rpar a c b x = a + b·x + c|x|²`. The proof
  follows the paper: Step 1 is `Axis.van_isolated`, Step 2 (induction on the length of a block of
  modes) is `Axis.van_block`, Step 3 is `Axis.van_all_ns` for the tables other than the square
  (hypothesis `m(3) ≠ 0 ∨ m(4) ≠ 0`, which by `Axis.square_of_m3_m4` only excludes the square;
  `Axis.exists_pow_near_one` gives the simultaneous approximation) and Step 4 is `Axis.center` and
  `Axis.paraboloid_core` (with the symmetry of second derivatives, `Axis.dz_dzb_comm`). For the
  square, the non-degenerate modes are the `k ≡ 2 mod 4` (`Axis.m_sq`, `Axis.m_sq_ne_zero`), and
  Step 3 is replaced by an eigenvalue argument: if `m - 2, m + 2 ∈ Z(f)`, then
  `(m² - 1) G_m[f] = -2r² G_m[∂∂̄f]` (`Axis.sq_eig`); comparing the eigenvalues for `m` and `m + 4`
  gives `G_m[∂²f] = 0` (`Axis.sq_dz_dz`), then `G_m[f] = 0` (`Axis.sq_van`), and all the modes
  `k ≥ 2` vanish (`Axis.van_sq`); `Axis.van_all` combines both cases. This is Step 3 for the square
  in the paper. The global argument for (b) (spectral synthesis and Bessel functions) and the
  alternative argument for Steps 2 and 4 (polynomials) are not formalised. In the reduction to smooth terrains, the mollification uses a continuous
  extension of `g` (Tietze) from a compact part of `Ω`, and the limit is taken through the values at
  four fixed points (`Axis.interp`). For Lipschitz terrains, `Axis.affine_of_F₀v_all` deduces that
  `c = 0`; `Axis.affine_of_F₀v` is an earlier, independent proof for the tables other than the square
  (Liouville).
* **Hypotheses stated abstractly.** In Proposition 5.4 and Corollary 5.5, "`ĝ` is supported in
  `𝒦_n`" is replaced by the equivalent condition that `g₁` is affine on the orbits of the rotations
  by `2π/n` (`Table.AffineOnOrbits`). For the hexagon, `Table.hex_affine_of_F₀` proves that
  `F₀ ≡ 0` implies it. "`g₁` is C²" is replaced by the Taylor estimate of Proposition 5.2.
* **Theorem 5.1.** The paper states it as the theorem of Baritompa, Löwen, Polster & Ross in its
  set-up and only sketches the proof, with a degree argument; the Lean proof is complete, and
  replaces the degree argument by the intermediate value theorem, applied to the direction of the
  shadow of a foot (`Table.exists_foot_dir`).
* **Theorem 5.7 and Proposition 5.8: the Lean proofs are numerically weaker than the paper.**
  The constants are cruder than in the paper (`K`, `d_min`,
  `P₃ ≤ K L₃`, `f(s) ≤ ½ + s/2`), so `ε₀` is smaller:
  * Theorem 5.7: `w_AC ≥ ε³` for `0 < ε ≤ 10⁻³` (paper: `w_AC ≥ 0.5 ε³` for `ε ≤ 4·10⁻³`);
  * Proposition 5.8: `w_AC ≥ 0.3 ε³` for `0 < ε ≤ 5·10⁻⁴` (paper: `ε ≤ 10⁻³`).
* **Terrain.** The terrain is any function equal to the given polynomial on the closed unit disc
  and Lipschitz with the stated constant on `ℂ`. Such a terrain exists (McShane extension); the
  radial extension of the paper is one such function.
* **Computations.** For the trapezoid, all quantities are exact in `ℚ(√23)`. For Proposition 5.8,
  the feet are located by the intermediate value theorem. The algebra of `z^j mod Q` then shows
  that `m(2) = i t` and `m(3) = e^{iπ/6} m(2)`, so only the lower bound `t > 1.4` is numerical.
* **Theorem 5.11.** The non-degeneracy is stated with the multiplier `mR iA iB iC iD τ μ s`, i.e.
  `m(s) = -Σ_E c_E e_E^s` for the feet `e_E = ω^{i_E}`. The hypothesis is `σ ≤ |m(s)|` for all
  `s ≢ 0, ±1 mod n`. `coercive_of_nondeg` turns it into the coercivity of the circulant operator
  (`Wobbly.Coercive`): the operator multiplies the Fourier mode `s` by `-m(-s)`, and one applies
  Parseval's identity. For the hexagon, `hex_coercive'` recovers `σ = 2/√3` this way, and so does
  the earlier sum-of-squares certificate `hex_coercive`.

* **Remark 5.14 (a).** The paper says that `inf |m(k)|` over the non-degenerate modes of an
  irrational table is `0` "by the argument of Remark 5.13 (c)", which only shows that some `|m(k)|`
  are small. The Lean proof also shows that the small modes can be taken non-degenerate: if
  `e_E^n` is close to `1` for the four feet, then `m(n)`, `m(2n)` and `m(3n)` are small, and they do
  not all vanish unless the table is rational (`Feet.isRat_of_three`, a Vandermonde argument). The
  paper now mentions this.
* **Remark 5.9 (a).** The gradient of `g₁` along the circle is that of the affine function: this is
  derived from the differentiability of `g₁` (`tangential_of_affine`).
* **Remark 5.9 (g).** Formalised for `0 < ε ≤ 10⁻³`, the range of the Lean version of
  Theorem 5.7 (paper: `ε ≤ 4·10⁻³`). A position of the table is any `T ∈ SO(3)` and any height `c`,
  the feet being at `T (a_E, 0) + (0, 0, c)`; the three cases `T₂₂ > 0`, `T₂₂ < 0` and `T₂₂ = 0`
  (upright, upside down, vertical) are treated as in the paper.

### Not formalised

* §1–§3, except Theorem 2.2 (in the idealised model of Remark 2.3 (b)).
* The global argument for Proposition 4.13 (b) and the alternative argument for its Steps 2 and 4.
* The larger ranges of `ε` of Theorem 5.7 and Proposition 5.8 (see above).
* In the remarks: the heuristic second order computation of Remark 4.12 and its comment on random
  terrains; the numerical observations of Remarks 5.9 (b)–(f), 5.13 (a), (c), (d) (the values of
  `W₃`, `min w_AC/ε³`, the slopes and sizes, the table of admissible slopes, the CMA-ES search); the
  fact that the degenerate rational tables with `n ≤ 12` are exactly the ones listed in
  Remark 5.13 (b) (a numerical check; the Lean proof only shows that the listed trapezoids are
  degenerate); the limits `χ → 0` and `S → 0` in Remark 5.9 (e) (only the end points are
  formalised); and the informal Remark 5.14 (b).

Everything compiles without `sorry`; the main theorems only depend on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
