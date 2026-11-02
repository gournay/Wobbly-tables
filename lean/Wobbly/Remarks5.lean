import Wobbly.Remarks4
import Wobbly.TrapezoidCex
import Wobbly.Classification
import Wobbly.Rational

/-!
# The remarks of §5 of the paper

**Remark 5.9 (a).**
* If `𝒦 = {0, ±1}` and `F₀^{(1)} ≡ 0`, then `g₁` is affine on the circle (`affine_on_circle`,
  `affine_on_circle_of_generic`), so `q₀` is constant (`idealTilt_const`), and
  `W₃ = w₃ + F₀^{(3)}` is the idealised wobbling function of `-½(β - u·q₀)(u·q₀)² + g₃`
  (`w3_eq_F₀`), so it has mean `0` and changes sign unless `W₃ ≡ 0` (`W3_generic`).
* For rational tables and `γ̂` supported in `𝒦_n`, the orbit sums of `W₃` vanish (`sum_F₀_orbit`,
  `sum_W3_orbit`), so again `W₃` changes sign unless `W₃ ≡ 0` (`W3_rational`).
* The quantity `S` of Proposition 5.6 (`Feet.Sk`, with `Feet.κ = Re(b S)/8`, `κ_eq`) vanishes for the
  modes `k` with `e_E^k = ±1` (`Sk_eq_zero_of_pm`), in particular for the extra degenerate mode
  `n/2` of the degenerate rational trapezoids, and for the modes of `𝒦_n`
  (`Sk_eq_zero_of_rational`): the construction of §5.5 does not apply there.
* If the diagonals have different lengths, a degenerate mode `k ≥ 2` is at least `5`
  (`five_le_of_diag_ne`).

**Remark 5.9 (e).** For `χ = 0` the polynomial `Q_χ` has its roots at four vertices of a regular
pentagon (`Qχ_zero`), for `χ = π/4` at four vertices of a regular hexagon (`Qχ_pi_div_four`); `S = 0`
for such tables (`Sk_eq_zero_of_pm`, `Sk_eq_zero_of_right`). The tables of the family (normalised
by `s₄ = 1`, `s₁ = e^{iχ}`, `0 < χ < π/2`) are not isosceles trapezoids, so their diagonals have
different lengths (`not_isoTrap_of_s₁`, `diag_ne_of_s₁`).

**Remark 5.9 (f).** For the terrain of Theorem 5.7, arbitrarily small moves of the axis give
`F₀^{(1)} ≢ 0` (`trapezoid_axis_moved`, from Proposition 4.13 (a)).

**Remark 5.9 (g).** The trapezoid of Theorem 5.7 cannot be balanced locally on the terrain of
Theorem 5.7, in the sense of Baritompa, Löwen, Polster & Ross: no rotation `T ∈ SO(3)` and no height
`c` put its four feet `T (a_E, 0) + (0, 0, c)` on the ground (`OnGround`,
`trapezoid_not_locally_balanced`). The positions which neither turn the table upside down nor make
it vertical are the positions `(θ, q, c)` (`exists_S_mul_Rz`, `onGround_iff_resid`), excluded by
Theorem 5.7 (`trapezoid_not_upright`); turning the table upside down (`flipX`) acts as `z ↦ z̄` on
its frame, which maps the trapezoid onto itself (`trapezoid_not_upside_down`); in a vertical
position, the heights of two feet on the ground differ by at most `L` times their distance
(`height_sub_sq_le`), which is impossible for the feet `A`, `B` and `D` (`trapezoid_not_vertical`).

**Remark 5.10.** If the diagonals have the same length, a rotation of the circle maps the chord
`AC` onto the chord `BD` (`exists_rot_of_diag_eq`); then the position `(θ + ψ, q, c)` puts `A` and
`C` exactly where `(θ, q, c)` puts `D` and `B` (`resid_rot_chain`, and `feet_eq` for the points of
`ℝ³`), so the exact chain presupposes that the table is already stable (`chain_presupposes`).

**Remark 5.13.**
* (b) An isosceles trapezoid symmetric with respect to the real axis has `τ = μ`
  (`τ_eq_μ_of_symm`), and a mode `k` with `e_A^k`, `e_C^k` real is degenerate (`m_eq_zero_of_symm`,
  `exp_pow_real`): this gives the extra degenerate mode `n/2` of the five trapezoids listed in the
  paper (after a rotation, their feet are at `±πa/k`, `±πb/k`, `k = n/2`). That there are no other
  degenerate rational tables with `n ≤ 12` is a numerical check, not formalised.
* (c) If tables `F_j` converge to a table and `n_j → ∞`, then eventually some residue
  `2 ≤ s ≤ n_j - 2` has `|m_j(s)| < ε`, so `σ_j → 0` (`exists_small_mode_of_tendsto`).
* (d) A vector of `ℝ^{ℤ/6}` without Fourier modes `0, ±1` satisfies `min x ≤ -½ max x`
  (`exists_le_neg_half_max`).

**Remark 5.14 (a).** `∫ w_AC = ∫ (w_AC - F₀) = O(L³)` (`integral_wob`), not `0` in general
(`integral_wob_trapezoid_pos`); for an irrational table (`Feet.IsRat`), arbitrarily large
non-degenerate modes have arbitrarily small `|m(k)|`, so `inf |m(k)| = 0` over the non-degenerate
modes (`Feet.exists_small_nondegenerate_mode`: if `e_E^n` is close to `1` for the four feet, then
`m(n)`, `m(2n)`, `m(3n)` are small, and one of them is non-zero unless the table is rational,
`Feet.isRat_of_three`).

The numerical statements of Remarks 5.9 (b)–(f), 5.13 (a)–(d) and the informal Remark 5.14 (b) are
not formalised.
-/

noncomputable section

open Complex ComplexConjugate MeasureTheory Filter Topology Matrix

namespace Wobbly

/-! ### Fourier coefficients on a circle -/

section circle

variable {r : ℝ}

open Axis in
/-- Two continuous functions with the same coefficients `G_n` on the circle of radius `r` centred
at `v` agree on this circle. -/
lemma eq_on_circle_of_γ {f h : ℂ → ℂ} (hf : Continuous f) (hh : Continuous h) (v : ℂ)
    (hcoef : ∀ n : ℤ, γ r n f v = γ r n h v) (θ : ℝ) :
    f (v + r * rot θ) = h (v + r * rot θ) := by
  set ψ : ℝ → ℂ := fun φ => f (v + r * rot φ) - h (v + r * rot φ) with hψ
  have hψc : Continuous ψ := (continuous_circle hf v).sub (continuous_circle hh v)
  have hψp : Function.Periodic ψ (2 * Real.pi) := fun φ => by
    simp only [hψ, rot_add', rot_two_pi, mul_one]
  have hc : ∀ n : ℤ, ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = 0 := by
    intro n
    have e : ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = γ r n f v - γ r n h v := by
      unfold γ
      rw [← intervalIntegral.integral_sub]
      · congr 1; ext φ; simp only [hψ]; ring
      · exact ((continuous_rotk n).mul (continuous_circle hf v)).intervalIntegrable _ _
      · exact ((continuous_rotk n).mul (continuous_circle hh v)).intervalIntegrable _ _
    rw [e, hcoef]; exact sub_self _
  exact sub_eq_zero.1 (eq_zero_of_fourier hψc hψp hc θ)

open Axis in
/-- A continuous function on the circle of radius `r > 0` centred at `v`, whose Fourier modes
`|k| ≥ 2` vanish, is the restriction of an affine function. -/
theorem affine_on_circle (hr : 0 < r) {g : ℂ → ℝ} (hg : Continuous g) {v : ℂ}
    (h : ∀ k : ℕ, 2 ≤ k → γR r k g v = 0) :
    ∃ (a : ℝ) (b : ℂ), ∀ θ : ℝ, g (v + r * rot θ) = a + dot b (r * rot θ) := by
  have hreal : ∀ x, conj ((g x : ℂ)) = (g x : ℂ) := fun x => Complex.conj_ofReal _
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set G0 := γR r 0 g v with hG0def
  set G1 := γR r 1 g v with hG1def
  have hG0 : conj G0 = G0 := by
    have := γ_neg (r := r) hreal 0 v
    simp only [neg_zero] at this
    exact this.symm
  have hG0re : ((G0.re : ℝ) : ℂ) = G0 := Complex.conj_eq_iff_re.1 hG0
  set a : ℝ := G0.re / (2 * Real.pi) with hadef
  set b : ℂ := conj G1 / (Real.pi * r) with hbdef
  refine ⟨a, b, fun θ => ?_⟩
  set P : ℂ → ℂ := parab ((a : ℂ) - dot b v) (conj b / 2) (b / 2) 0 with hPdef
  have hP : ∀ x, P x = ((a + dot b (x - v) : ℝ) : ℂ) := by
    intro x
    simp only [hPdef, parab, dot_sub_right]
    push_cast
    rw [dot_eq_complex', dot_eq_complex']
    ring
  have hcb : conj b = G1 / (Real.pi * r) := by
    simp only [hbdef, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  have hcoef : ∀ n : ℤ, γ r n (fun x => (g x : ℂ)) v = γ r n P v := by
    intro n
    rw [hPdef, γ_parab]
    by_cases n0 : n = 0
    · subst n0
      simp only [ite_true, show (0 : ℤ) ≠ 1 by norm_num, show (0 : ℤ) ≠ -1 by norm_num, ite_false,
        add_zero, zero_mul]
      have e1 : conj b / 2 * v + b / 2 * conj v = (dot b v : ℂ) := by rw [dot_eq_complex']; ring
      rw [add_assoc, e1, sub_add_cancel]
      show G0 = _
      rw [← hG0re, hadef]; push_cast; field_simp
    by_cases n1 : n = 1
    · subst n1
      simp only [show (1 : ℤ) ≠ 0 by norm_num, show (1 : ℤ) ≠ -1 by norm_num, ite_true, ite_false,
        zero_add, add_zero, zero_mul]
      show G1 = _
      rw [hcb]; field_simp
    by_cases nm : n = -1
    · subst nm
      simp only [show (-1 : ℤ) ≠ 0 by norm_num, show (-1 : ℤ) ≠ 1 by norm_num, ite_true, ite_false,
        zero_add, zero_mul, add_zero]
      rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, γ_neg hreal 1 v]
      show conj G1 = _
      rw [hbdef]; field_simp
    · simp only [n0, n1, nm, ite_false, add_zero]
      rcases le_or_gt 0 n with hn | hn
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        exact h k (by omega)
      · have := γ_neg (r := r) hreal (-n) v
        rw [neg_neg] at this
        rw [this]
        obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
        rw [hk, show γ r (k : ℤ) (fun x => (g x : ℂ)) v = γR r k g v from rfl, h k (by omega),
          map_zero]
  have hgc : Continuous fun x => (g x : ℂ) := Complex.continuous_ofReal.comp hg
  have hPc : Continuous P := continuous_parab _ _ _ _
  have := eq_on_circle_of_γ hgc hPc v hcoef θ
  rw [hP, add_sub_cancel_left] at this
  exact_mod_cast this

end circle

/-! ### Remark 5.9 (a): the generic case -/

open Axis in
/-- **Remark 5.9 (a)**: if `𝒦 = {0, ±1}`, then `F₀ ≡ 0` forces the terrain to be affine on the
circle. -/
theorem affine_on_circle_of_generic (F : Feet) (hgen : ∀ k : ℕ, 2 ≤ k → F.m k ≠ 0) {r : ℝ}
    (hr : 0 < r) {g : ℂ → ℝ} (hg : Continuous g) {v : ℂ} (h : ∀ θ, F₀v F r g v θ = 0) :
    ∃ (a : ℝ) (b : ℂ), ∀ θ : ℝ, g (v + r * rot θ) = a + dot b (r * rot θ) :=
  affine_on_circle hr hg fun k hk =>
    (mul_eq_zero.1 ((F₀v_eq_zero_iff F hg v).1 h k)).resolve_left (hgen k hk)

/-- **Remark 5.9 (a)**: if `g₁` is affine on the circle (with gradient `b`), the idealised tilt
`q₀(θ)` is the constant `b`. -/
theorem idealTilt_const {T : Table} (hc : T.Cyclic) {g : ℂ → ℝ} {a : ℝ} {b : ℂ}
    (hab : ∀ θ : ℝ, g (T.r * rot θ) = a + dot b (T.r * rot θ)) (θ : ℝ) : T.Q g θ 0 = b := by
  have key : ∀ E : ℂ, ‖E‖ = T.r → g (rot θ * E) = a + dot (rot θ * E) b := by
    intro E hE
    obtain ⟨φ, hφ⟩ := Axis.exists_rot_of_norm (r := T.r) (w := rot θ * E)
      (by rw [norm_rot_mul, hE])
    rw [hφ, hab, dot_comm]
  exact Table.Q_of_affine (c := a) (key _ hc.hA) (key _ hc.hB) (key _ hc.hC) (key _ hc.hD)

/-- The identity `(G·b)(u·b) = (G·u - u·b)(u·b)² + |b|² (u·b)` for `|u| = 1` and `G·(iu) = b·(iu)`. -/
lemma grad_mul_dot {u G b : ℂ} (hu : ‖u‖ = 1) (hG : dot G (I * u) = dot b (I * u)) :
    dot G b * dot u b = (dot G u - dot u b) * dot u b ^ 2 + ‖b‖ ^ 2 * dot u b := by
  have h1 := sq_norm_eq u
  rw [hu, one_pow] at h1
  rw [sq_norm_eq]
  simp only [dot, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at hG ⊢
  linear_combination (u.re * b.re + u.im * b.im) * (b.re ^ 2 + b.im ^ 2 - (G.re * b.re + G.im * b.im))
    * (-h1) + (u.re * b.re + u.im * b.im) * (-(u.im * b.re) + u.re * b.im) * hG

/-- **Remark 5.9 (a)**: if `g₁` is affine on the unit circle with gradient `b`, i.e. the gradient
`G₁` of `g₁` satisfies `G₁(u)·(iu) = b·(iu)` on the circle, then `w₃` (for the constant idealised
tilt `b`) is the idealised wobbling function of `h(u) = -½ (β(u) - u·b)(u·b)²`, where
`β(u) = G₁(u)·u` is the radial derivative of `g₁`. -/
theorem w3_eq_F₀ {T : Table} (hc : T.Cyclic) (hr : T.r = 1) {G₁ : ℂ → ℂ} {b : ℂ}
    (hG : ∀ u : ℂ, ‖u‖ = 1 → dot (G₁ u) (I * u) = dot b (I * u)) {τ μ : ℝ}
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D) (θ : ℝ) :
    T.w3 G₁ τ μ θ b =
      T.F₀ (fun u => -(1 / 2) * (dot (G₁ u) u - dot u b) * dot u b ^ 2) τ μ θ := by
  have hn : ∀ E : ℂ, ‖E‖ = T.r → ‖rot θ * E‖ = 1 := fun E hE => by rw [norm_rot_mul, hE, hr]
  have kA := grad_mul_dot (hn _ hc.hA) (hG _ (hn _ hc.hA))
  have kB := grad_mul_dot (hn _ hc.hB) (hG _ (hn _ hc.hB))
  have kC := grad_mul_dot (hn _ hc.hC) (hG _ (hn _ hc.hC))
  have kD := grad_mul_dot (hn _ hc.hD) (hG _ (hn _ hc.hD))
  -- `Σ c_E (u_E · b) = 0`
  have hp := plane_eq hX θ b 0
  simp only [zero_add] at hp
  unfold Table.w3 Table.F₀
  rw [kA, kB, kC, kD]
  linear_combination (-(1 / 2) * ‖b‖ ^ 2) * hp

/-- The derivative along the unit circle: if `g₁` has gradient `G₁` and is affine with gradient `b`
on the unit circle, then `G₁(u)·(iu) = b·(iu)` on the circle. -/
lemma tangential_of_affine {g : ℂ → ℝ} {G : ℂ → ℂ} (hd : ∀ x, HasFDerivAt g (dotCLM (G x)) x)
    {a : ℝ} {b : ℂ} (hab : ∀ θ : ℝ, g (rot θ) = a + dot b (rot θ)) {u : ℂ} (hu : ‖u‖ = 1) :
    dot (G u) (I * u) = dot b (I * u) := by
  obtain ⟨φ, hφ⟩ := Axis.exists_rot_of_norm (r := 1) (w := u) (by rw [hu])
  rw [Complex.ofReal_one, one_mul] at hφ
  subst hφ
  have h1 : HasDerivAt (fun t => g (rot t)) (dotCLM (G (rot φ)) (I * rot φ)) φ :=
    (hd (rot φ)).comp_hasDerivAt φ (Axis.hasDerivAt_rot1 φ)
  have h2 : HasDerivAt (fun t => a + dot b (rot t)) (dotCLM b (I * rot φ)) φ := by
    have := ((dotCLM b).hasFDerivAt (x := rot φ)).comp_hasDerivAt φ (Axis.hasDerivAt_rot1 φ)
    simpa [Function.comp_def] using this.const_add a
  have e : (fun t => g (rot t)) = fun t => a + dot b (rot t) := funext hab
  rw [e] at h1
  have := h1.unique h2
  simpa using this

/-- **Remark 5.9 (a)**, generic case: if `𝒦 = {0, ±1}`, `F₀^{(1)} ≡ 0` and `g₁` has a continuous
gradient `G₁`, then `W₃ = w₃ + F₀^{(3)}` has mean `0`, and it changes sign unless `W₃ ≡ 0`. -/
theorem W3_generic (F : Feet) (hgen : ∀ k : ℕ, 2 ≤ k → F.m k ≠ 0) {T : Table} (hc : T.Cyclic)
    (hr : T.r = 1) (hA : T.A = F.A) (hB : T.B = F.B) (hC : T.C = F.C) (hD : T.D = F.D)
    {g₁ g₃ : ℂ → ℝ} {G₁ : ℂ → ℂ} (hd : ∀ x, HasFDerivAt g₁ (dotCLM (G₁ x)) x)
    (hG₁ : Continuous G₁) (hg₃ : Continuous g₃) (h1 : ∀ θ, Axis.F₀v F 1 g₁ 0 θ = 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, (T.w3 G₁ F.τ F.μ θ (T.Q g₁ θ 0) + T.F₀ g₃ F.τ F.μ θ)) = 0 ∧
      ((∀ θ, T.w3 G₁ F.τ F.μ θ (T.Q g₁ θ 0) + T.F₀ g₃ F.τ F.μ θ = 0) ∨
        ((∃ θ, 0 < T.w3 G₁ F.τ F.μ θ (T.Q g₁ θ 0) + T.F₀ g₃ F.τ F.μ θ) ∧
          ∃ θ, T.w3 G₁ F.τ F.μ θ (T.Q g₁ θ 0) + T.F₀ g₃ F.τ F.μ θ < 0)) := by
  have hg₁ : Continuous g₁ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  obtain ⟨a, b, hab⟩ := affine_on_circle_of_generic F hgen one_pos hg₁ h1
  simp only [zero_add, Complex.ofReal_one, one_mul] at hab
  have hab' : ∀ θ : ℝ, g₁ (T.r * rot θ) = a + dot b (T.r * rot θ) := by
    intro θ; rw [hr, Complex.ofReal_one, one_mul]; exact hab θ
  have hX : (F.τ : ℂ) * T.A + (1 - F.τ : ℝ) * T.C = (F.μ : ℂ) * T.B + (1 - F.μ : ℝ) * T.D := by
    rw [hA, hB, hC, hD]; exact F.hX
  set h : ℂ → ℝ := fun u => -(1 / 2) * (dot (G₁ u) u - dot u b) * dot u b ^ 2 with hh
  have hW : ∀ θ, T.w3 G₁ F.τ F.μ θ (T.Q g₁ θ 0) + T.F₀ g₃ F.τ F.μ θ =
      T.F₀ (fun u => h u + g₃ u) F.τ F.μ θ := by
    intro θ
    rw [idealTilt_const hc hab' θ, w3_eq_F₀ hc hr (fun u hu => tangential_of_affine hd hab hu) hX,
      Table.F₀_add]
  have hhc : Continuous fun u => h u + g₃ u := by
    have hd' : Continuous fun u : ℂ => dot (G₁ u) u := continuous_dot.comp (hG₁.prodMk continuous_id)
    have hd'' : Continuous fun u : ℂ => dot u b := continuous_dot.comp (continuous_id.prodMk continuous_const)
    exact ((continuous_const.mul (hd'.sub hd'')).mul (hd''.pow 2)).add hg₃
  simp_rw [hW]
  have hI := Table.integral_F₀ hc hhc F.τ F.μ
  refine ⟨hI, ?_⟩
  by_cases h0 : ∀ θ, T.F₀ (fun u => h u + g₃ u) F.τ F.μ θ = 0
  · exact Or.inl h0
  · push Not at h0
    obtain ⟨θ₀, hθ₀⟩ := h0
    exact Or.inr (exists_pos_neg_of_integral_zero (Table.continuous_F₀ hhc _ _)
      (Table.periodic_F₀ _ _ _) hI hθ₀)

/-! ### Remark 5.9 (a): rational tables -/

section rational

variable {T : Table} {n : ℕ} [NeZero n] {iA iB iC iD : ZMod n} {τ μ : ℝ}

/-- For a rational table, the sum of `F₀` over an orbit of the rotations by `2π/n` vanishes. -/
theorem sum_F₀_orbit (hR : IsRational T n iA iB iC iD τ μ) (g : ℂ → ℝ) (θ : ℝ) :
    ∑ j : ZMod n, T.F₀ g τ μ (θj n θ j) = 0 := by
  have hj : ∀ j : ZMod n, T.F₀ g τ μ (θj n θ j) =
      τ * g (vtx n T.r θ (iA + j)) + (1 - τ) * g (vtx n T.r θ (iC + j))
        - μ * g (vtx n T.r θ (iB + j)) - (1 - μ) * g (vtx n T.r θ (iD + j)) := by
    intro j
    unfold Table.F₀
    rw [Table.rot_θj_A hR, Table.rot_θj_B hR, Table.rot_θj_C hR, Table.rot_θj_D hR]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_shift (F := fun i => g (vtx n T.r θ i))]
  ring

/-- **Remark 5.9 (a)**: for a rational table and `g₁` affine on the orbits (`γ̂` supported in
`𝒦_n`), the orbit sums of `W₃ = w₃ + F₀^{(3)}` vanish. -/
theorem sum_W3_orbit (hR : IsRational T n iA iB iC iD τ μ) {g₁ : ℂ → ℝ}
    (hg : Table.AffineOnOrbits g₁ n T.r) (G₁ : ℂ → ℂ) (g₃ : ℂ → ℝ) (θ : ℝ) :
    ∑ j : ZMod n, (T.w3 G₁ τ μ (θj n θ j) (T.Q g₁ (θj n θ j) 0) + T.F₀ g₃ τ μ (θj n θ j)) = 0 := by
  rw [Finset.sum_add_distrib, Table.sum_w3_orbit hR hg G₁ θ, sum_F₀_orbit hR g₃ θ, add_zero]

/-- **Remark 5.9 (a)**: hence `W₃` changes sign unless `W₃ ≡ 0`. -/
theorem W3_rational (hR : IsRational T n iA iB iC iD τ μ) {g₁ : ℂ → ℝ}
    (hg : Table.AffineOnOrbits g₁ n T.r) (G₁ : ℂ → ℂ) (g₃ : ℂ → ℝ) :
    (∀ θ, T.w3 G₁ τ μ θ (T.Q g₁ θ 0) + T.F₀ g₃ τ μ θ = 0) ∨
      ((∃ θ, 0 < T.w3 G₁ τ μ θ (T.Q g₁ θ 0) + T.F₀ g₃ τ μ θ) ∧
        ∃ θ, T.w3 G₁ τ μ θ (T.Q g₁ θ 0) + T.F₀ g₃ τ μ θ < 0) := by
  set W : ℝ → ℝ := fun θ => T.w3 G₁ τ μ θ (T.Q g₁ θ 0) + T.F₀ g₃ τ μ θ with hW
  have hs : ∀ θ, ∑ j : ZMod n, W (θj n θ j) = 0 := sum_W3_orbit hR hg G₁ g₃
  by_cases h0 : ∀ θ, W θ = 0
  · exact Or.inl h0
  push Not at h0
  obtain ⟨θ₀, hθ₀⟩ := h0
  have h00 : θj n θ₀ 0 = θ₀ := Table.θj_zero θ₀
  -- an orbit containing a non-zero value contains values of both signs
  have both : ∀ θ : ℝ, W θ ≠ 0 → (∃ θ', 0 < W θ') ∧ ∃ θ', W θ' < 0 := by
    intro θ hθ
    have hsum := hs θ
    have h0' : θj n θ 0 = θ := Table.θj_zero θ
    rcases hθ.lt_or_gt with hneg | hpos
    · refine ⟨?_, ⟨θ, hneg⟩⟩
      by_contra hc
      push Not at hc
      have : ∑ j : ZMod n, W (θj n θ j) < 0 :=
        Finset.sum_neg' (fun j _ => hc _) ⟨0, Finset.mem_univ _, by rw [h0']; exact hneg⟩
      linarith
    · refine ⟨⟨θ, hpos⟩, ?_⟩
      by_contra hc
      push Not at hc
      have : 0 < ∑ j : ZMod n, W (θj n θ j) :=
        Finset.sum_pos' (fun j _ => hc _) ⟨0, Finset.mem_univ _, by rw [h0']; exact hpos⟩
      linarith
  exact Or.inr (both θ₀ hθ₀)

end rational

/-! ### Remark 5.9 (a): the quantity `S` of Proposition 5.6 -/

namespace Feet

variable (F : Feet)

/-- `ξ₊ = m(k-1)/conj(m(2))` (Proposition 5.6). -/
def ξp (k : ℕ) : ℂ := F.m (k - 1) / conj (F.m 2)

/-- `ξ₋ = conj(m(k+1))/conj(m(2))` (Proposition 5.6). -/
def ξm (k : ℕ) : ℂ := conj (F.m (k + 1)) / conj (F.m 2)

/-- `S = m(2k+2) conj(ξ₊)² + 2 m(2k) conj(ξ₊) ξ₋ + m(2k-2) ξ₋²` (Proposition 5.6). -/
def Sk (k : ℕ) : ℂ :=
  F.m (2 * k + 2) * conj (F.ξp k) ^ 2 + 2 * F.m (2 * k) * conj (F.ξp k) * F.ξm k
    + F.m (2 * k - 2) * F.ξm k ^ 2

/-- The mean `κ(b)` of `w₃` in Proposition 5.6 is `Re(b S)/8`. -/
lemma κ_eq (k : ℕ) (b : ℂ) : F.κ k b (F.ξp k) (F.ξm k) = (1 / 8) * (b * F.Sk k).re := rfl

/-- `S = 0` if `m(k-1) = m(2k-2) = 0` (e.g. `k ≡ 1 mod n` for a rational table). -/
lemma Sk_eq_zero_of_left {k : ℕ} (h1 : F.m (k - 1) = 0) (h2 : F.m (2 * k - 2) = 0) : F.Sk k = 0 := by
  simp [Sk, ξp, h1, h2]

/-- `S = 0` if `m(k+1) = m(2k+2) = 0` (e.g. `k ≡ -1 mod n` for a rational table). -/
lemma Sk_eq_zero_of_right {k : ℕ} (h1 : F.m (k + 1) = 0) (h2 : F.m (2 * k + 2) = 0) :
    F.Sk k = 0 := by
  simp [Sk, ξm, h1, h2]

/-- For a foot `e` with `e^k = ±1`: `e^{k-1} = conj(e^{k+1})`, `e^{2k} = 1`, `e^{2k+2} = e²` and
`e^{2k-2} = conj(e²)`. -/
lemma pm_aux {e : ℂ} (he : ‖e‖ = 1) {k : ℕ} (hk : 2 ≤ k) (h : e ^ k = 1 ∨ e ^ k = -1) :
    e ^ (k - 1) = conj (e ^ (k + 1)) ∧ e ^ (2 * k) = 1 ∧ e ^ (2 * k + 2) = e ^ 2 ∧
      e ^ (2 * k - 2) = conj (e ^ 2) := by
  have hc : conj e * e = 1 := by
    rw [Complex.conj_mul', he]; simp
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hk1 : e ^ k = e ^ (k - 1) * e := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have h2k : e ^ (2 * k) = 1 := by rw [mul_comm, pow_mul]; rcases h with h | h <;> rw [h] <;> norm_num
  have hkk : e ^ (2 * k) = e ^ (2 * k - 2) * e ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  refine ⟨?_, h2k, by rw [pow_add, h2k, one_mul], ?_⟩
  · -- `e^{k-1} = e^k conj e`
    have : e ^ (k - 1) = e ^ k * conj e := by
      rw [hk1, mul_assoc, mul_comm e, hc, mul_one]
    rw [this, pow_succ, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  · -- `e^{2k-2} e² = 1`
    have h3 : e ^ (2 * k - 2) * e ^ 2 = 1 := by rw [← hkk, h2k]
    have h4 : conj (e ^ 2) * e ^ 2 = 1 := by rw [map_pow, ← mul_pow, hc, one_pow]
    have he2 : e ^ 2 ≠ 0 := pow_ne_zero _ he0
    exact mul_right_cancel₀ he2 (h3.trans h4.symm)

/-- **Remark 5.9 (a)**: `S = 0` for a degenerate mode `k` with `e_E^k = ±1` for every foot, e.g.
the extra degenerate mode `k = n/2` of the degenerate rational trapezoids. -/
theorem Sk_eq_zero_of_pm {k : ℕ} (hk : 2 ≤ k) (hmk : F.m k = 0)
    (hA : F.A ^ k = 1 ∨ F.A ^ k = -1) (hB : F.B ^ k = 1 ∨ F.B ^ k = -1)
    (hC : F.C ^ k = 1 ∨ F.C ^ k = -1) (hD : F.D ^ k = 1 ∨ F.D ^ k = -1) : F.Sk k = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := pm_aux F.nA hk hA
  obtain ⟨b1, b2, b3, b4⟩ := pm_aux F.nB hk hB
  obtain ⟨c1, c2, c3, c4⟩ := pm_aux F.nC hk hC
  obtain ⟨d1, d2, d3, d4⟩ := pm_aux F.nD hk hD
  -- `m(k-1) = conj m(k+1)`, `m(2k) = 0`, `m(2k+2) = m(2)`, `m(2k-2) = conj m(2)`
  have e1 : F.m (k - 1) = conj (F.m (k + 1)) := by
    simp only [m, a1, b1, c1, d1, map_neg, map_sub, map_add, map_mul, Complex.conj_ofReal]
  have e2 : F.m (2 * k) = 0 := by simp only [m, a2, b2, c2, d2]; push_cast; ring
  have e3 : F.m (2 * k + 2) = F.m 2 := by simp only [m, a3, b3, c3, d3]
  have e4 : F.m (2 * k - 2) = conj (F.m 2) := by
    simp only [m, a4, b4, c4, d4, map_neg, map_sub, map_add, map_mul, Complex.conj_ofReal]
  -- Lemma 5.3 (e): `Re(m(2) m(k-1) conj m(k+1)) = 0`
  obtain ⟨α₀, α₁, α₂, hI⟩ := (F.m_eq_zero_iff k).1 hmk
  have hre := (F.interp_coeffs (by omega) hmk hI).2.2
  have hM : F.m 2 ≠ 0 := F.m_two_ne_zero
  have hM' : conj (F.m 2) ≠ 0 := by rwa [map_ne_zero]
  have hξ : F.ξm k = F.ξp k := by simp only [ξm, ξp, e1]
  rw [← e1] at hre
  have key : F.Sk k * (F.m 2 * conj (F.m 2)) =
      F.m 2 * F.m (k - 1) * F.m (k - 1) + conj (F.m 2 * F.m (k - 1) * F.m (k - 1)) := by
    simp only [Sk, hξ, e2, e3, e4, ξp, map_div₀, map_mul, Complex.conj_conj]
    field_simp
    ring
  rw [Complex.add_conj, hre, mul_zero, Complex.ofReal_zero] at key
  exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero hM hM')

/-- **Remark 5.9 (a)**: for a rational table (`e_E^n = 1`), `S = 0` for the modes of
`𝒦_n = {k ≡ 0, ±1 mod n}`. -/
theorem Sk_eq_zero_of_rational {n : ℕ} (hn : 1 ≤ n) (hA : F.A ^ n = 1) (hB : F.B ^ n = 1)
    (hC : F.C ^ n = 1) (hD : F.D ^ n = 1) {k : ℕ} (hk : 2 ≤ k)
    (hmod : k % n = 0 ∨ k % n = 1 ∨ (k + 1) % n = 0) : F.Sk k = 0 := by
  have hz := F.m_eq_zero_of_rational hn hA hB hC hD
  rcases hmod with h | h | h
  · obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    have hE : ∀ e : ℂ, e ^ n = 1 → e ^ (n * j) = 1 ∨ e ^ (n * j) = -1 := fun e he =>
      Or.inl (by rw [pow_mul, he, one_pow])
    exact F.Sk_eq_zero_of_pm hk (hz j).1 (hE _ hA) (hE _ hB) (hE _ hC) (hE _ hD)
  · obtain ⟨q, hq⟩ : ∃ q, k = n * q + 1 := ⟨k / n, by rw [← h]; exact (Nat.div_add_mod k n).symm⟩
    refine F.Sk_eq_zero_of_left ?_ ?_
    · rw [show k - 1 = n * q by omega]; exact (hz _).1
    · rw [hq, show 2 * (n * q + 1) - 2 = n * (2 * q) by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]; ring]
      exact (hz _).1
  · obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero h
    refine F.Sk_eq_zero_of_right ?_ ?_
    · rw [hj]; exact (hz j).1
    · rw [show 2 * k + 2 = n * (2 * j) by rw [show 2 * k + 2 = 2 * (k + 1) by ring, hj]; ring]
      exact (hz _).1

/-- `S = 0` if all the feet satisfy `e^{k+1} = c` for the same `c` (as for the kite at the end of
the family `G_χ`, whose feet satisfy `e⁶ = -i`). -/
theorem Sk_eq_zero_of_const {k : ℕ} {c : ℂ} (hA : F.A ^ (k + 1) = c) (hB : F.B ^ (k + 1) = c)
    (hC : F.C ^ (k + 1) = c) (hD : F.D ^ (k + 1) = c) : F.Sk k = 0 := by
  refine F.Sk_eq_zero_of_right ?_ ?_
  · simp only [m, hA, hB, hC, hD]; push_cast; ring
  · simp only [m, show 2 * k + 2 = (k + 1) * 2 by ring, pow_mul, hA, hB, hC, hD]; push_cast; ring

/-- **Remark 5.9 (a)**: if the diagonals have different lengths, a degenerate mode `k ≥ 2` is at
least `5` (Lemma 5.3 (e), (f)). -/
theorem five_le_of_diag_ne {k : ℕ} (hk : 2 ≤ k) (hmk : F.m k = 0)
    (hd : ‖F.A - F.C‖ ≠ ‖F.B - F.D‖) : 5 ≤ k := by
  by_contra h
  interval_cases k
  · exact F.m_two_ne_zero hmk
  · exact hd (F.diag_eq_of_m_three_or_four F.nonParallel (Or.inl hmk))
  · exact hd (F.diag_eq_of_m_three_or_four F.nonParallel (Or.inr hmk))

end Feet

/-! ### Remark 5.9 (e): the ends of the family `G_χ` -/

/-- For `χ = 0`: `(z + 1) Q₀(z) = z⁵ + 1`, so the roots of `Q₀` are four vertices of the regular
pentagon `{z⁵ = -1}`. -/
theorem Qχ_zero (z : ℂ) : (z + 1) * Feet.Qχ 0 z = z ^ 5 + 1 := by
  simp only [Feet.Qχ, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_zero,
    Real.cos_zero, Complex.ofReal_one]
  ring

lemma Qχ_zero_root {z : ℂ} (h : Feet.Qχ 0 z = 0) : z ^ 5 = -1 := by
  have := Qχ_zero z
  rw [h, mul_zero] at this
  linear_combination -this

/-- For `χ = π/4`: `(z² + e^{iπ/4} z + i) Q_{π/4}(z) = z⁶ + i`, so the roots of `Q_{π/4}` are four
vertices of the regular hexagon `{z⁶ = -i}`. -/
theorem Qχ_pi_div_four (z : ℂ) :
    (z ^ 2 + Complex.exp ((Real.pi / 4 : ℝ) * I) * z + I) * Feet.Qχ (Real.pi / 4) z = z ^ 6 + I := by
  have h2 : Complex.exp ((Real.pi / 4 : ℝ) * I) ^ 2 = I := by
    rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * I) = Real.pi / 2 * I by
      push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I
  have hinv : Complex.exp (-((Real.pi / 4 : ℝ) * I)) = -I * Complex.exp ((Real.pi / 4 : ℝ) * I) := by
    have h0 : Complex.exp (-((Real.pi / 4 : ℝ) * I)) * Complex.exp ((Real.pi / 4 : ℝ) * I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have h1 : (-I * Complex.exp ((Real.pi / 4 : ℝ) * I)) * Complex.exp ((Real.pi / 4 : ℝ) * I) = 1 := by
      rw [mul_assoc, ← sq, h2, neg_mul, Complex.I_mul_I, neg_neg]
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h0.trans h1.symm)
  have hc : ((Real.cos (2 * (Real.pi / 4)) : ℝ) : ℂ) = 0 := by
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two, Complex.ofReal_zero]
  simp only [Feet.Qχ, hc, hinv]
  linear_combination (-z ^ 4 + I * z ^ 2) * h2
    + (z * Complex.exp ((Real.pi / 4 : ℝ) * I) + z ^ 2) * Complex.I_sq

lemma Qχ_pi_div_four_root {z : ℂ} (h : Feet.Qχ (Real.pi / 4) z = 0) : z ^ 6 = -I := by
  have := Qχ_pi_div_four z
  rw [h, mul_zero] at this
  linear_combination -this

/-- **Remark 5.9 (e)**: `S = 0` for the tables with feet on the regular pentagon `{z⁵ = -1}` (the end
`χ → 0` of the family), with `k = 5`. -/
theorem Sk_pentagon (F : Feet) (hA : F.A ^ 5 = -1) (hB : F.B ^ 5 = -1) (hC : F.C ^ 5 = -1)
    (hD : F.D ^ 5 = -1) : F.Sk 5 = 0 :=
  F.Sk_eq_zero_of_pm (by norm_num) (by simp only [Feet.m, hA, hB, hC, hD]; push_cast; ring)
    (Or.inr hA) (Or.inr hB) (Or.inr hC) (Or.inr hD)

/-- **Remark 5.9 (e)**: `S = 0` for the tables with feet on the regular hexagon `{z⁶ = -i}` (the
kite `χ = π/4`), with `k = 5`. -/
theorem Sk_hexagon (F : Feet) (hA : F.A ^ 6 = -I) (hB : F.B ^ 6 = -I) (hC : F.C ^ 6 = -I)
    (hD : F.D ^ 6 = -I) : F.Sk 5 = 0 :=
  F.Sk_eq_zero_of_const hA hB hC hD

/-- In each pair `{P, u P̄}` of feet exchanged by the reflection `z ↦ u z̄`, the sum is real if
`u = 1` and imaginary if `u = -1`. -/
lemma pair_sum {P Q u : ℂ} (hu : u = 1 ∨ u = -1) :
    (P + u * conj P + (Q + u * conj Q)).im = 0 ∨ (P + u * conj P + (Q + u * conj Q)).re = 0 := by
  rcases hu with rfl | rfl
  · left; simp
  · right; simp

/-- **Remark 5.9 (e)**: a table with `s₄ = 1` and `s₁ = e^{iχ}`, `0 < χ < π/2` (the family `G_χ`,
normalised), is not an isosceles trapezoid: the product of a pair `{z, u z̄}` of feet exchanged by
a reflection is `u`, so `u² = s₄ = 1`, and then `s₁` would be real or imaginary. -/
theorem not_isoTrap_of_s₁ (F : Feet) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < Real.pi / 2)
    (h1 : F.s₁ = Complex.exp (χ * I)) (h4 : F.s₄ = 1) : ¬ F.IsoTrap := by
  rintro ⟨u, hu, hmap, hfix⟩
  set R : ℂ → ℂ := fun z => u * conj z with hR
  have hRR : ∀ z, R (R z) = z := fun z => by
    simp only [hR, map_mul, Complex.conj_conj, ← mul_assoc, Complex.mul_conj', hu]; simp
  have hprod : ∀ z : ℂ, ‖z‖ = 1 → z * R z = u := fun z hz => by
    simp only [hR]
    rw [mul_left_comm, Complex.mul_conj', hz]; simp
  have mem : ∀ z ∈ F.feet, R z = F.A ∨ R z = F.B ∨ R z = F.C ∨ R z = F.D := fun z hz => by
    have := hmap z hz
    simpa [Feet.feet] using this
  have hA : F.A ∈ F.feet := by simp [Feet.feet]
  have hB : F.B ∈ F.feet := by simp [Feet.feet]
  have hC : F.C ∈ F.feet := by simp [Feet.feet]
  have hD : F.D ∈ F.feet := by simp [Feet.feet]
  -- the feet split into two pairs `{P, R P}`, `{Q, R Q}`
  have hpairs : ∃ P Q : ℂ, ‖P‖ = 1 ∧ ‖Q‖ = 1 ∧ F.s₁ = P + R P + (Q + R Q) ∧
      F.s₄ = P * R P * (Q * R Q) := by
    have fA := hfix _ hA
    rcases mem _ hA with h | h | h | h
    · exact absurd h fA
    · -- `R A = B`, so `R C = D`
      have hRB : R F.B = F.A := by rw [← h]; exact hRR _
      have fC := hfix _ hC
      rcases mem _ hC with h' | h' | h' | h'
      · exact absurd (by rw [← h', hRR] : F.C = R F.A) (by rw [h]; exact F.BC.symm)
      · exact absurd (by rw [← h', hRR] : F.C = R F.B) (by rw [hRB]; exact F.AC.symm)
      · exact absurd h' fC
      · exact ⟨F.A, F.C, F.nA, F.nC, by rw [h, h']; simp only [Feet.s₁]; ring,
          by rw [h, h']; simp only [Feet.s₄]; ring⟩
    · -- `R A = C`, so `R B = D`
      have hRC : R F.C = F.A := by rw [← h]; exact hRR _
      have fB := hfix _ hB
      rcases mem _ hB with h' | h' | h' | h'
      · exact absurd (by rw [← h', hRR] : F.B = R F.A) (by rw [h]; exact F.BC)
      · exact absurd h' fB
      · exact absurd (by rw [← h', hRR] : F.B = R F.C) (by rw [hRC]; exact F.AB.symm)
      · exact ⟨F.A, F.B, F.nA, F.nB, by rw [h, h']; simp only [Feet.s₁]; ring,
          by rw [h, h']; simp only [Feet.s₄]; ring⟩
    · -- `R A = D`, so `R B = C`
      have hRD : R F.D = F.A := by rw [← h]; exact hRR _
      have fB := hfix _ hB
      rcases mem _ hB with h' | h' | h' | h'
      · exact absurd (by rw [← h', hRR] : F.B = R F.A) (by rw [h]; exact F.BD)
      · exact absurd h' fB
      · exact ⟨F.A, F.B, F.nA, F.nB, by rw [h, h']; simp only [Feet.s₁]; ring,
          by rw [h, h']; simp only [Feet.s₄]; ring⟩
      · exact absurd (by rw [← h', hRR] : F.B = R F.D) (by rw [hRD]; exact F.AB.symm)
  obtain ⟨P, Q, hP, hQ, hs1, hs4⟩ := hpairs
  rw [hprod P hP, hprod Q hQ, h4] at hs4
  have hu1 : u = 1 ∨ u = -1 := mul_self_eq_one_iff.1 hs4.symm
  rw [h1] at hs1
  simp only [hR] at hs1
  rcases pair_sum (P := P) (Q := Q) hu1 with him | hre
  · rw [← hs1, Complex.exp_ofReal_mul_I_im] at him
    exact (Real.sin_pos_of_pos_of_lt_pi hχ0 (by linarith [Real.pi_pos])).ne' him
  · rw [← hs1, Complex.exp_ofReal_mul_I_re] at hre
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, hχ1⟩).ne' hre

/-- **Remark 5.9 (e)**: hence the tables of the family have diagonals of different lengths. -/
theorem diag_ne_of_s₁ (F : Feet) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < Real.pi / 2)
    (h1 : F.s₁ = Complex.exp (χ * I)) (h4 : F.s₄ = 1) : ‖F.A - F.C‖ ≠ ‖F.B - F.D‖ := fun hd =>
  not_isoTrap_of_s₁ F hχ0 hχ1 h1 h4 (F.isoTrap_of_diag_eq hd)

/-! ### Remark 5.9 (f): moving the axis -/

open Axis in
/-- **Remark 5.9 (f)**: for the table and the terrain `g₁ = Re z⁴ - 3(|z|² - 1) Im z⁸` of
Theorem 5.7, arbitrarily small moves of the axis give `F₀^{(1)} ≢ 0` (Proposition 4.13 (a)). -/
theorem trapezoid_axis_moved {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ℂ, ‖v‖ < δ ∧ ∃ θ : ℝ, F₀v trapF 1 (gk 4 (6 * I)) v θ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h : ∀ v ∈ Metric.ball (0 : ℂ) δ, ∀ θ, F₀v trapF 1 (gk 4 (6 * I)) v θ = 0 :=
    fun v hv θ => hcon v (by simpa using hv) θ
  have hgc : Continuous (gk 4 (6 * I)) := by unfold gk; fun_prop
  obtain ⟨a, c, b, hab⟩ := paraboloid_of_F₀v_local trapF one_pos hδ hgc.continuousOn h
  have hΩ : ∀ z : ℂ, ‖z‖ = 1 → z ∈ Ω 1 0 δ := fun z hz =>
    ⟨0, Metric.mem_ball_self hδ, by simpa using hz⟩
  have hval : ∀ z : ℂ, ‖z‖ = 1 → (z ^ 4).re = a + c + dot b z := by
    intro z hz
    have hn : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
    have := hab z (hΩ z hz)
    simp only [gk, rpar, hn, sub_self, mul_zero, zero_mul, add_zero] at this
    linarith
  set ω := Complex.exp ((Real.pi / 4 : ℝ) * I) with hω
  have hω1 : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hω4 : ω ^ 4 = -1 := by
    rw [hω, ← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I]
    congr 1; push_cast; ring
  have e1 := hval 1 (by simp)
  have e2 := hval (-1) (by simp)
  have e3 := hval ω hω1
  have e4 := hval (-ω) (by rw [norm_neg, hω1])
  have hdn : dot b (-ω) = -dot b ω := by simp [dot]; ring
  have hd1 : dot b (-1) = -dot b 1 := by simp [dot]
  rw [hω4] at e3
  rw [neg_pow, hω4, hdn] at e4
  rw [hd1] at e2
  norm_num at e1 e2 e3 e4
  linarith

/-! ### Remark 5.9 (g): the trapezoid cannot be balanced locally -/

/-- The point `p ∈ ℝ³` is on the ground, the graph of `g`. -/
def OnGround (g : ℂ → ℝ) (p : Fin 3 → ℝ) : Prop := p 2 = g ⟨p 0, p 1⟩

/-- In the position `S_q ∘ R_θ` (and height `c`), the foot at `a` is on the ground if and only if
its residual vanishes. -/
lemma onGround_iff_resid (g : ℂ → ℝ) (θ : ℝ) (q : ℂ) (c : ℝ) (a : ℂ) :
    OnGround g ((S q * Rz θ) *ᵥ pt a 0 + pt 0 c) ↔ resid g θ q c a = 0 := by
  rw [resid_eq, Matrix.mulVec_mulVec, sub_eq_zero]
  rfl

/-- The rotation by `π` around the first axis, which turns the table upside down. -/
def flipX : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

lemma flipX_mem : flipX ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [flipX, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [Matrix.det_fin_three]; simp [flipX]

/-- Turning the table upside down acts on its frame as the conjugation `z ↦ z̄`. -/
lemma flipX_pt (a : ℂ) : flipX *ᵥ pt a 0 = pt (conj a) 0 := by
  ext i
  fin_cases i <;> simp [flipX, pt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma mul_flipX_22 (T : Matrix (Fin 3) (Fin 3) ℝ) : (T * flipX) 2 2 = -T 2 2 := by
  simp [flipX, Matrix.mul_apply, Fin.sum_univ_three]

/-- The heights of two feet on an `L`-Lipschitz ground differ by at most `L` times their distance
in the frame of the table (the horizontal distance of the feet is at most this distance). -/
lemma height_sub_sq_le {g : ℂ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : IsLip g L)
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (c : ℝ)
    {a b : ℂ} (ha : OnGround g (T *ᵥ pt a 0 + pt 0 c)) (hb : OnGround g (T *ᵥ pt b 0 + pt 0 c)) :
    (T 2 0 * (a.re - b.re) + T 2 1 * (a.im - b.im)) ^ 2 ≤
      L ^ 2 * ((a.re - b.re) ^ 2 + (a.im - b.im) ^ 2) := by
  obtain ⟨hTT, -, -⟩ := SO3_iff hT
  have h00 := congrFun (congrFun hTT 0) 0
  have h11 := congrFun (congrFun hTT 1) 1
  have h01 := congrFun (congrFun hTT 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h00 h11 h01
  simp only [OnGround, pt, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Complex.zero_re, Complex.zero_im, mul_zero, add_zero] at ha hb
  set x : ℝ := a.re - b.re
  set y : ℝ := a.im - b.im
  have hlip := hg ⟨T 0 0 * a.re + T 0 1 * a.im, T 1 0 * a.re + T 1 1 * a.im⟩
    ⟨T 0 0 * b.re + T 0 1 * b.im, T 1 0 * b.re + T 1 1 * b.im⟩
  rw [← ha, ← hb] at hlip
  have hn : ‖(⟨T 0 0 * a.re + T 0 1 * a.im, T 1 0 * a.re + T 1 1 * a.im⟩ : ℂ) -
      ⟨T 0 0 * b.re + T 0 1 * b.im, T 1 0 * b.re + T 1 1 * b.im⟩‖ ^ 2 =
      (T 0 0 * x + T 0 1 * y) ^ 2 + (T 1 0 * x + T 1 1 * y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, x, y]
    ring
  have hsum : (T 0 0 * x + T 0 1 * y) ^ 2 + (T 1 0 * x + T 1 1 * y) ^ 2 +
      (T 2 0 * x + T 2 1 * y) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination x ^ 2 * h00 + y ^ 2 * h11 + 2 * x * y * h01
  have hz : T 2 0 * a.re + T 2 1 * a.im + c - (T 2 0 * b.re + T 2 1 * b.im + c) =
      T 2 0 * x + T 2 1 * y := by simp only [x, y]; ring
  rw [hz] at hlip
  set N := ‖(⟨T 0 0 * a.re + T 0 1 * a.im, T 1 0 * a.re + T 1 1 * a.im⟩ : ℂ) -
      ⟨T 0 0 * b.re + T 0 1 * b.im, T 1 0 * b.re + T 1 1 * b.im⟩‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have h1 : (T 2 0 * x + T 2 1 * y) ^ 2 ≤ L ^ 2 * N ^ 2 := by
    have := abs_le_abs_of_nonneg (abs_nonneg _) hlip
    rw [abs_abs, abs_of_nonneg (mul_nonneg hL hN0)] at this
    calc (T 2 0 * x + T 2 1 * y) ^ 2 = |T 2 0 * x + T 2 1 * y| ^ 2 := (sq_abs _).symm
      _ ≤ (L * N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = L ^ 2 * N ^ 2 := by ring
  rw [hn] at h1
  nlinarith [sq_nonneg (T 2 0 * x + T 2 1 * y), sq_nonneg L]

section local_balance

variable {ε : ℝ} {g : ℂ → ℝ}

/-- The trapezoid of Theorem 5.7 is symmetric with respect to the real axis. -/
lemma conj_trapT_A : conj trapT.A = trapT.B := by
  apply Complex.ext <;> simp [trapT, eA, eB]

lemma conj_trapT_B : conj trapT.B = trapT.A := by
  apply Complex.ext <;> simp [trapT, eA, eB]

lemma conj_trapT_C : conj trapT.C = trapT.D := by
  apply Complex.ext <;> simp [trapT, eC, eD]

lemma conj_trapT_D : conj trapT.D = trapT.C := by
  apply Complex.ext <;> simp [trapT, eC, eD]

/-- Remark 5.9 (g), first case: the positions which neither turn the table upside down nor make it
vertical are the positions `(θ, q, c)`, excluded by Theorem 5.7. -/
lemma trapezoid_not_upright (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000)
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x)
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h : 0 < T 2 2) (c : ℝ) :
    ¬ (OnGround g (T *ᵥ pt trapT.A 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.B 0 + pt 0 c) ∧
      OnGround g (T *ᵥ pt trapT.C 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.D 0 + pt 0 c)) := by
  obtain ⟨q, θ, hq, rfl⟩ := exists_S_mul_Rz hT h
  rintro ⟨hA, hB, hC, hD⟩
  rw [onGround_iff_resid] at hA hB hC hD
  exact trapezoid_wobbles hε hε₀ hg hgd θ ⟨q, c, hq, hA, hB, hC, hD⟩

/-- Remark 5.9 (g), second case: turning the table upside down maps the trapezoid onto itself. -/
lemma trapezoid_not_upside_down (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000)
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x)
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h : T 2 2 < 0) (c : ℝ) :
    ¬ (OnGround g (T *ᵥ pt trapT.A 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.B 0 + pt 0 c) ∧
      OnGround g (T *ᵥ pt trapT.C 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.D 0 + pt 0 c)) := by
  rintro ⟨hA, hB, hC, hD⟩
  have key : ∀ a : ℂ, (T * flipX) *ᵥ pt a 0 = T *ᵥ pt (conj a) 0 := fun a => by
    rw [← Matrix.mulVec_mulVec, flipX_pt]
  refine trapezoid_not_upright hε hε₀ hg hgd (Submonoid.mul_mem _ hT flipX_mem)
    (by rw [mul_flipX_22]; linarith) c ?_
  rw [key, key, key, key, conj_trapT_A, conj_trapT_B, conj_trapT_C, conj_trapT_D]
  exact ⟨hB, hA, hD, hC⟩

/-- Remark 5.9 (g), third case: a vertical position is impossible on a flat ground, since the
feet `A`, `B` and `D` cannot all be on the ground. -/
lemma trapezoid_not_vertical (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000)
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h : T 2 2 = 0) (c : ℝ) :
    ¬ (OnGround g (T *ᵥ pt trapT.A 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.B 0 + pt 0 c) ∧
      OnGround g (T *ᵥ pt trapT.D 0 + pt 0 c)) := by
  rintro ⟨hA, hB, hD⟩
  set L := ε * 10 + ε ^ 3 * 169 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hε3 : ε ^ 3 ≤ (1 / 1000) ^ 3 := pow_le_pow_left₀ hε.le hε₀ 3
  have hL1 : L ≤ 0.0102 := by rw [hLdef]; linarith only [hε₀, hε3]
  obtain ⟨-, hTT', -⟩ := SO3_iff hT
  have hrow := congrFun (congrFun hTT' 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h] at hrow
  have hAB := height_sub_sq_le hL0 hg hT c hA hB
  have hAD := height_sub_sq_le hL0 hg hT c hA hD
  simp only [trapT, eA, eB, eD] at hAB hAD
  have hcb := cb_bounds
  have hsb := sb_bounds
  set u := T 2 0
  set v := T 2 1
  -- the pair `A`, `B`: `|v| ≤ L`
  have hv : v ^ 2 ≤ L ^ 2 := by nlinarith only [hAB]
  -- the pair `A`, `D`
  set a' : ℝ := 3 / 5 - cb
  set b' : ℝ := 4 / 5 - sb
  have ha' : 0.42 < a' ∧ a' < 0.4205 := ⟨by simp only [a']; linarith, by simp only [a']; linarith⟩
  have hb' : -0.1839 < b' ∧ b' < -0.1836 := ⟨by simp only [b']; linarith, by simp only [b']; linarith⟩
  have h1 : (u * a') ^ 2 ≤ 2 * (u * a' + v * b') ^ 2 + 2 * (v * b') ^ 2 := by
    nlinarith only [sq_nonneg (u * a' + v * b' + v * b')]
  have h2 : (v * b') ^ 2 ≤ L ^ 2 * b' ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hv (sq_nonneg _)
  have h3 : (1 - L ^ 2) * a' ^ 2 ≤ (u * a') ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by linarith only [hrow, hv]) (sq_nonneg _)
  have key : (1 - L ^ 2) * a' ^ 2 ≤ 2 * (L ^ 2 * (a' ^ 2 + b' ^ 2)) + 2 * (L ^ 2 * b' ^ 2) := by
    linarith only [h1, h2, h3, hAD]
  have hL2 : L ^ 2 ≤ 0.000105 := by nlinarith only [hL0, hL1]
  have ha2 : 0.1764 < a' ^ 2 := by nlinarith only [ha'.1]
  have ha2' : a' ^ 2 < 0.1769 := by nlinarith only [ha'.1, ha'.2]
  have hb2 : b' ^ 2 < 0.0339 := by nlinarith only [hb'.1, hb'.2]
  have hXA : L ^ 2 * a' ^ 2 ≤ 0.000105 * 0.1769 :=
    mul_le_mul hL2 ha2'.le (sq_nonneg _) (by norm_num)
  have hXB : L ^ 2 * b' ^ 2 ≤ 0.000105 * 0.0339 :=
    mul_le_mul hL2 hb2.le (sq_nonneg _) (by norm_num)
  linarith only [key, hXA, hXB, ha2]

/-- **Remark 5.9 (g)**: the trapezoid of Theorem 5.7 cannot be *balanced locally* on the terrain
`g` of Theorem 5.7, in the sense of Baritompa, Löwen, Polster & Ross: there is no rotation
`T ∈ SO(3)` (which may tilt the table, turn it upside down or make it vertical) and no height `c`
such that the four feet `T (a_E, 0) + (0, 0, c)` are on the ground. -/
theorem trapezoid_not_locally_balanced (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000)
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x)
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (c : ℝ) :
    ¬ (OnGround g (T *ᵥ pt trapT.A 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.B 0 + pt 0 c) ∧
      OnGround g (T *ᵥ pt trapT.C 0 + pt 0 c) ∧ OnGround g (T *ᵥ pt trapT.D 0 + pt 0 c)) := by
  rcases lt_trichotomy (T 2 2) 0 with h | h | h
  · exact trapezoid_not_upside_down hε hε₀ hg hgd hT h c
  · rintro ⟨hA, hB, -, hD⟩
    exact trapezoid_not_vertical hε hε₀ hg hT h c ⟨hA, hB, hD⟩
  · exact trapezoid_not_upright hε hε₀ hg hgd hT h c

end local_balance

/-! ### Remark 5.10: chains of touchdowns -/

/-- The difference of the squared lengths of the diagonals:
`(|A - C|² - |B - D|²) ABCD = (BC - AD)(AB - CD)`. -/
lemma diag_sq_sub (F : Feet) :
    ((‖F.A - F.C‖ ^ 2 - ‖F.B - F.D‖ ^ 2 : ℝ) : ℂ) * (F.A * F.B * F.C * F.D) =
      (F.B * F.C - F.A * F.D) * (F.A * F.B - F.C * F.D) := by
  have cA := inv_eq_conj_of_norm_eq_one F.nA
  have cB := inv_eq_conj_of_norm_eq_one F.nB
  have cC := inv_eq_conj_of_norm_eq_one F.nC
  have cD := inv_eq_conj_of_norm_eq_one F.nD
  have hA := F.A_ne
  have hB := F.B_ne
  have hC := F.C_ne
  have hD := F.D_ne
  have e : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, e, e, map_sub, map_sub, ← cA, ← cB, ← cC, ← cD]
  field_simp
  ring

/-- **Remark 5.10**: if the diagonals have the same length, a rotation `R_ψ` of the circle maps the
chord `AC` onto the chord `BD`, with `A ↦ D, C ↦ B` or `A ↦ B, C ↦ D`. -/
theorem exists_rot_of_diag_eq (F : Feet) (hd : ‖F.A - F.C‖ = ‖F.B - F.D‖) :
    ∃ ψ : ℝ, (rot ψ * F.A = F.D ∧ rot ψ * F.C = F.B) ∨ (rot ψ * F.A = F.B ∧ rot ψ * F.C = F.D) := by
  have h := diag_sq_sub F
  rw [hd, sub_self, Complex.ofReal_zero, zero_mul] at h
  have cA := inv_eq_conj_of_norm_eq_one F.nA
  have hA := F.A_ne
  -- a unit complex number is a rotation
  have hrot : ∀ w : ℂ, ‖w‖ = 1 → ∃ ψ : ℝ, rot ψ = w := fun w hw => by
    obtain ⟨ψ, hψ⟩ := Axis.exists_rot_of_norm (r := 1) hw
    exact ⟨ψ, by rw [hψ]; simp⟩
  rcases mul_eq_zero.1 h.symm with h1 | h1
  · -- `BC = AD`: `w = B / A`
    obtain ⟨ψ, hψ⟩ := hrot (F.B * F.A⁻¹) (by rw [norm_mul, norm_inv, F.nA, F.nB]; simp)
    refine ⟨ψ, Or.inr ⟨by rw [hψ]; field_simp, ?_⟩⟩
    rw [hψ]; field_simp; linear_combination h1
  · -- `AB = CD`: `w = D / A`
    obtain ⟨ψ, hψ⟩ := hrot (F.D * F.A⁻¹) (by rw [norm_mul, norm_inv, F.nA, F.nD]; simp)
    refine ⟨ψ, Or.inl ⟨by rw [hψ]; field_simp, ?_⟩⟩
    rw [hψ]; field_simp; linear_combination -h1

/-- **Remark 5.10**: with the same tilt and height, the position at `θ + ψ` puts the foot `A`
exactly where the position at `θ` puts `D` (`S_q(R_{θ+ψ} a_A, 0) = S_q(R_θ a_D, 0)`). -/
lemma resid_rot_chain {ψ : ℝ} {X Y : ℂ} (h : rot ψ * X = Y) (g : ℂ → ℝ) (θ : ℝ)
    (q : ℂ) (c : ℝ) :
    resid g (θ + ψ) q c X = resid g θ q c Y ∧
      S q *ᵥ (Rz (θ + ψ) *ᵥ pt X 0) + pt 0 c = S q *ᵥ (Rz θ *ᵥ pt Y 0) + pt 0 c := by
  have e : rot (θ + ψ) * X = rot θ * Y := by rw [Axis.rot_add', mul_assoc, h]
  refine ⟨by unfold resid; rw [e], by rw [feet_eq, feet_eq, e]⟩

/-- **Remark 5.10**: the exact chain presupposes the conclusion: if `A`, `C` are on the ground at
`θ` and, with the same tilt and height, at `θ + ψ`, then the table already has its four feet on
the ground at `θ`. -/
theorem chain_presupposes {T : Table} {ψ : ℝ} (hA : rot ψ * T.A = T.D) (hC : rot ψ * T.C = T.B)
    {g : ℂ → ℝ} {θ : ℝ} {q : ℂ} {c : ℝ} (h0A : resid g θ q c T.A = 0)
    (h0C : resid g θ q c T.C = 0) (h1A : resid g (θ + ψ) q c T.A = 0)
    (h1C : resid g (θ + ψ) q c T.C = 0) :
    resid g θ q c T.A = 0 ∧ resid g θ q c T.B = 0 ∧ resid g θ q c T.C = 0 ∧
      resid g θ q c T.D = 0 := by
  refine ⟨h0A, ?_, h0C, ?_⟩
  · rw [← (resid_rot_chain hC g θ q c).1]; exact h1C
  · rw [← (resid_rot_chain hA g θ q c).1]; exact h1A

/-! ### Remark 5.13 -/

/-- For an isosceles trapezoid symmetric with respect to the real axis (`B = Ā`, `D = C̄`), the
diagonals are cut in the same ratio: `τ = μ`. -/
lemma τ_eq_μ_of_symm (F : Feet) (hB : F.B = conj F.A) (hD : F.D = conj F.C) : F.τ = F.μ := by
  have hX := F.hX
  have hX' := congrArg conj hX
  simp only [map_add, map_mul, Complex.conj_ofReal] at hX'
  rw [hB, hD] at hX
  rw [hB, hD, Complex.conj_conj, Complex.conj_conj] at hX'
  -- `X - X̄ = (τ - μ)(A - C) = (μ - τ)(Ā - C̄)`
  have e : ((F.τ - F.μ : ℝ) : ℂ) * ((F.A - F.C) + (conj F.A - conj F.C)) = 0 := by
    push_cast at hX hX' ⊢
    linear_combination hX + hX'
  rcases mul_eq_zero.1 e with h | h
  · exact sub_eq_zero.1 (by exact_mod_cast h)
  · -- otherwise `A - C` is imaginary, i.e. the diagonals `AC` and `BD = conj AC` are parallel
    exfalso
    have hw : (F.A - F.C).re = 0 := by
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.zero_re] at this
      simp only [Complex.sub_re]
      linarith
    apply F.nonParallel
    rw [hB, hD]
    simp only [map_sub, Complex.conj_conj]
    rw [Complex.mul_im, hw]
    ring

/-- **Remark 5.13 (b)**: for an isosceles trapezoid symmetric with respect to the real axis, a
mode `k` such that `e_A^k` and `e_C^k` are real (e.g. `k = n/2` when the feet are at angles in
`(2π/n) ℤ`, as for the degenerate rational trapezoids of Remark 5.13 (b), after a rotation) is
degenerate. -/
theorem m_eq_zero_of_symm (F : Feet) (hB : F.B = conj F.A) (hD : F.D = conj F.C) {k : ℕ}
    (hA : (F.A ^ k).im = 0) (hC : (F.C ^ k).im = 0) : F.m k = 0 := by
  have hτμ := τ_eq_μ_of_symm F hB hD
  have rA : conj (F.A ^ k) = F.A ^ k := Complex.conj_eq_iff_im.2 hA
  have rC : conj (F.C ^ k) = F.C ^ k := Complex.conj_eq_iff_im.2 hC
  simp only [Feet.m, hB, hD, ← map_pow, rA, rC, hτμ]
  ring

/-- For the feet `e^{±iπa/k}`, `e^{±iπb/k}`, the mode `k` has real powers: `(e^{iπa/k})^k = ±1`. -/
lemma exp_pow_real (a k : ℕ) (hk : k ≠ 0) :
    (Complex.exp ((Real.pi * a / k : ℝ) * I) ^ k).im = 0 := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have e : (k : ℂ) * (((Real.pi * a / k : ℝ) : ℂ) * I) = ((a * Real.pi : ℝ) : ℂ) * I := by
    push_cast
    field_simp
  rw [← Complex.exp_nat_mul, e, Complex.exp_ofReal_mul_I_im, Real.sin_nat_mul_pi]

/-- **Remark 5.13 (c)**: if tables `F_j` converge to a table `F` and `n_j → ∞`, then for every
`ε > 0`, eventually some residue `2 ≤ s ≤ n_j - 2` has `|m_j(s)| < ε`; in particular the constant
`σ` of the non-degenerate approximants tends to `0`. -/
theorem exists_small_mode_of_tendsto (F : ℕ → Feet) (Flim : Feet)
    (hA : Tendsto (fun j => (F j).A) atTop (𝓝 Flim.A)) (hB : Tendsto (fun j => (F j).B) atTop (𝓝 Flim.B))
    (hC : Tendsto (fun j => (F j).C) atTop (𝓝 Flim.C)) (hD : Tendsto (fun j => (F j).D) atTop (𝓝 Flim.D))
    (hτ : Tendsto (fun j => (F j).τ) atTop (𝓝 Flim.τ)) (hμ : Tendsto (fun j => (F j).μ) atTop (𝓝 Flim.μ))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ s : ℕ, 2 ≤ s ∧ s + 2 ≤ n j ∧ ‖(F j).m s‖ < ε := by
  obtain ⟨N, hN, h1, h2, h3, h4⟩ :=
    Axis.exists_pow_near_one Flim.nA Flim.nB Flim.nC Flim.nD (by positivity : 0 < ε / 4) 2
  have hm : ‖Flim.m N‖ < ε / 2 := by
    have := Axis.m_shift Flim h1 h2 h3 h4 0
    rw [add_zero, Flim.m_zero, sub_zero] at this
    linarith
  have hc : ∀ {x : ℕ → ℝ} {y : ℝ}, Tendsto x atTop (𝓝 y) →
      Tendsto (fun j => ((x j : ℝ) : ℂ)) atTop (𝓝 (y : ℂ)) :=
    fun h => (Complex.continuous_ofReal.tendsto _).comp h
  have ht : Tendsto (fun j => (F j).m N) atTop (𝓝 (Flim.m N)) := by
    simp only [Feet.m]
    have h1' := hc (hτ.const_sub 1)
    have h2' := hc (hμ.const_sub 1)
    exact (((((hc hτ).mul (hA.pow N)).sub ((hc hμ).mul (hB.pow N))).add (h1'.mul (hC.pow N))).sub
      (h2'.mul (hD.pow N))).neg
  have e1 : ∀ᶠ j in atTop, ‖(F j).m N‖ < ε :=
    (continuous_norm.tendsto _ |>.comp ht).eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ j in atTop, N + 2 ≤ n j := hn.eventually_ge_atTop (N + 2)
  exact (e1.and e2).mono fun j hj => ⟨N, hN, hj.2, hj.1⟩

/-- **Remark 5.13 (d)**: a vector `x ∈ ℝ^{ℤ/6}` without Fourier modes `0, ±1`
(`∑ x_j = ∑ x_j cos(πj/3) = ∑ x_j sin(πj/3) = 0`) satisfies `min x ≤ -½ max x`. -/
theorem exists_le_neg_half_max (x : Fin 6 → ℝ) (h0 : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 = 0)
    (hc : 2 * x 0 + x 1 - x 2 - 2 * x 3 - x 4 + x 5 = 0) (hs : x 1 + x 2 - x 4 - x 5 = 0)
    (i : Fin 6) (hi : ∀ j, x j ≤ x i) : ∃ j, x j ≤ -(x i / 2) := by
  by_contra hcon
  push Not at hcon
  have := hi 0; have := hi 1; have := hi 2; have := hi 3; have := hi 4; have := hi 5
  have := hcon 0; have := hcon 1; have := hcon 2; have := hcon 3; have := hcon 4; have := hcon 5
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at * <;> linarith

/-! ### Remark 5.14 (a) -/

section ergodic

variable {T : Table} {g : ℂ → ℝ} {L : ℝ}

/-- **Remark 5.14 (a)**: for a cyclic table, `∫ w_AC = ∫ (w_AC - F₀)`, which is `O(L³)` by
Proposition 4.10. -/
theorem integral_wob (hc : T.Cyclic) (hg : IsLip g L) (hs : T.SmallL L) {τ μ : ℝ}
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, T.wob g L θ =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (T.wob g L θ - T.F₀ g τ μ θ) ∧
      |∫ θ in (0 : ℝ)..2 * Real.pi, T.wob g L θ| ≤
        2 * Real.pi * (2 * (L * (f ((L * T.K) ^ 2) * T.r * (L * T.K) ^ 2))) := by
  have hw := Table.continuous_wob hg hs
  have hF := Table.continuous_F₀ (T := T) hg.continuous τ μ
  have hI := Table.integral_F₀ hc hg.continuous τ μ
  have e : ∫ θ in (0 : ℝ)..2 * Real.pi, T.wob g L θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi, (T.wob g L θ - T.F₀ g τ μ θ) := by
    rw [intervalIntegral.integral_sub (hw.intervalIntegrable _ _) (hF.intervalIntegrable _ _), hI,
      sub_zero]
  refine ⟨e, ?_⟩
  rw [e, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := fun θ => T.wob g L θ - T.F₀ g τ μ θ)
    (C := 2 * (L * (f ((L * T.K) ^ 2) * T.r * (L * T.K) ^ 2)))
    (fun θ _ => by
      rw [Real.norm_eq_abs]
      exact Table.abs_wob_sub_F₀_le hg hs θ hX hτ0 hτ1 hμ0 hμ1)
  rw [sub_zero, abs_of_pos (by positivity)] at hb
  linarith

/-- **Remark 5.14 (a)**: `∫ w_AC` is not `0` in general: for the table-terrain duo of Theorem 5.7,
`∫ w_AC ≥ 2π ε³ > 0`. -/
theorem integral_wob_trapezoid_pos {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000) {g : ℂ → ℝ}
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x) :
    0 < ∫ θ in (0 : ℝ)..2 * Real.pi, trapT.wob g (ε * 10 + ε ^ 3 * 169) θ := by
  have hw := Table.continuous_wob hg (trapT_small hε.le hε₀)
  have hmono : ∫ θ in (0 : ℝ)..2 * Real.pi, ε ^ 3 ≤
      ∫ θ in (0 : ℝ)..2 * Real.pi, trapT.wob g (ε * 10 + ε ^ 3 * 169) θ :=
    intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
      (hw.intervalIntegrable _ _) fun θ _ => trapezoid_wob_ge hε hε₀ hg hgd θ
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have : 0 < 2 * Real.pi * ε ^ 3 := by positivity
  linarith

end ergodic

/-! ### Remark 5.14 (a): small non-degenerate modes -/

namespace Feet

variable (F : Feet)

/-- A table is *rational* if, after a rotation, its feet are `n`-th roots of unity for some
`n ≥ 1`: `e_A^n = e_B^n = e_C^n = e_D^n`. -/
def IsRat : Prop := ∃ n : ℕ, 1 ≤ n ∧ F.B ^ n = F.A ^ n ∧ F.C ^ n = F.A ^ n ∧ F.D ^ n = F.A ^ n

lemma mul_conj_eq_one {e : ℂ} (he : ‖e‖ = 1) : e * conj e = 1 := by
  rw [Complex.mul_conj', he]; simp

/-- If `τ = μ`, then `e_A e_B = e_C e_D` (the chords `AB` and `CD` are parallel). -/
lemma AB_eq_CD (h : F.τ = F.μ) : F.A * F.B = F.C * F.D := by
  have hX := F.hX
  have hX' := congrArg conj hX
  simp only [map_add, map_mul, Complex.conj_ofReal] at hX'
  rw [h] at hX hX'
  push_cast at hX hX'
  have hAc := mul_conj_eq_one F.nA
  have hBc := mul_conj_eq_one F.nB
  have hCc := mul_conj_eq_one F.nC
  have hDc := mul_conj_eq_one F.nD
  have ht : (F.μ : ℂ) ≠ 0 := by exact_mod_cast F.μ0.ne'
  have key : (F.μ : ℂ) * (F.A - F.B) * (F.C * F.D - F.A * F.B) = 0 := by
    linear_combination (-(F.A * F.B * F.C * F.D)) * hX' + ((F.μ : ℂ) * F.B * F.C * F.D) * hAc
      + ((1 - (F.μ : ℂ)) * F.A * F.B * F.D) * hCc - ((F.μ : ℂ) * F.A * F.C * F.D) * hBc
      - ((1 - (F.μ : ℂ)) * F.A * F.B * F.C) * hDc - (F.A * F.B) * hX
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ht)) F.AB
  · exact (sub_eq_zero.1 h1).symm

/-- If `τ + μ = 1`, then `e_A e_D = e_B e_C` (the chords `AD` and `BC` are parallel). -/
lemma AD_eq_BC (h : F.τ + F.μ = 1) : F.A * F.D = F.B * F.C := by
  have hX := F.hX
  have hX' := congrArg conj hX
  simp only [map_add, map_mul, Complex.conj_ofReal] at hX'
  have hμ : F.μ = 1 - F.τ := by linarith
  rw [hμ] at hX hX'
  push_cast at hX hX'
  have hAc := mul_conj_eq_one F.nA
  have hBc := mul_conj_eq_one F.nB
  have hCc := mul_conj_eq_one F.nC
  have hDc := mul_conj_eq_one F.nD
  have ht : (F.τ : ℂ) ≠ 0 := by exact_mod_cast F.τ0.ne'
  have key : (F.τ : ℂ) * (F.A - F.D) * (F.B * F.C - F.A * F.D) = 0 := by
    linear_combination (-(F.A * F.B * F.C * F.D)) * hX' + ((F.τ : ℂ) * F.B * F.C * F.D) * hAc
      + ((1 - (F.τ : ℂ)) * F.A * F.B * F.D) * hCc - ((1 - (F.τ : ℂ)) * F.A * F.C * F.D) * hBc
      - ((F.τ : ℂ) * F.A * F.B * F.C) * hDc - (F.A * F.D) * hX
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ht)) F.AD
  · exact (sub_eq_zero.1 h1).symm

/-- If `m(n) = m(2n) = m(3n) = 0`, the table is rational: the values `z_E = e_E^n` satisfy
`Σ c_E z_E^j = 0` for `j = 0, …, 3`, so each `z_E` equals another one (a Vandermonde argument),
and the possible coincidences force `e_E^{2n}` to be the same for all feet. -/
lemma isRat_of_three {n : ℕ} (hn : 1 ≤ n) (z1 : F.m n = 0) (z2 : F.m (2 * n) = 0)
    (z3 : F.m (3 * n) = 0) : F.IsRat := by
  have pw : ∀ (e : ℂ) (j : ℕ), e ^ (j * n) = (e ^ n) ^ j := fun e j => by rw [mul_comm, pow_mul]
  have hτ : (F.τ : ℂ) ≠ 0 := by exact_mod_cast F.τ0.ne'
  have hμ : (F.μ : ℂ) ≠ 0 := by exact_mod_cast F.μ0.ne'
  have hτ' : 1 - (F.τ : ℂ) ≠ 0 := by
    have : (1 - F.τ : ℝ) ≠ 0 := by linarith [F.τ1]
    exact_mod_cast this
  have hμ' : 1 - (F.μ : ℂ) ≠ 0 := by
    have : (1 - F.μ : ℝ) ≠ 0 := by linarith [F.μ1]
    exact_mod_cast this
  have S0 : (F.τ : ℂ) - F.μ + (1 - F.τ) - (1 - F.μ) = 0 := by ring
  have S1 : (F.τ : ℂ) * F.A ^ n - F.μ * F.B ^ n + (1 - F.τ) * F.C ^ n - (1 - F.μ) * F.D ^ n = 0 := by
    have := z1; simp only [Feet.m] at this; push_cast at this; linear_combination -this
  have S2 : (F.τ : ℂ) * (F.A ^ n) ^ 2 - F.μ * (F.B ^ n) ^ 2 + (1 - F.τ) * (F.C ^ n) ^ 2
      - (1 - F.μ) * (F.D ^ n) ^ 2 = 0 := by
    have := z2; simp only [Feet.m, pw] at this; push_cast at this; linear_combination -this
  have S3 : (F.τ : ℂ) * (F.A ^ n) ^ 3 - F.μ * (F.B ^ n) ^ 3 + (1 - F.τ) * (F.C ^ n) ^ 3
      - (1 - F.μ) * (F.D ^ n) ^ 3 = 0 := by
    have := z3; simp only [Feet.m, pw] at this; push_cast at this; linear_combination -this
  -- the rationality conclusions
  have all_eq : F.A ^ n = F.B ^ n → F.A ^ n = F.C ^ n → F.A ^ n = F.D ^ n → F.IsRat :=
    fun h1 h2 h3 => ⟨n, hn, h1.symm, h2.symm, h3.symm⟩
  have two_n : (F.A ^ n) ^ 2 = (F.B ^ n) ^ 2 → (F.A ^ n) ^ 2 = (F.C ^ n) ^ 2 →
      (F.A ^ n) ^ 2 = (F.D ^ n) ^ 2 → F.IsRat := fun h1 h2 h3 =>
    ⟨2 * n, by omega, by rw [mul_comm, pow_mul, pow_mul, h1], by rw [mul_comm, pow_mul, pow_mul, h2],
      by rw [mul_comm, pow_mul, pow_mul, h3]⟩
  have hAB : (F.A * F.B) ^ n = (F.C * F.D) ^ n → F.A ^ n * F.B ^ n = F.C ^ n * F.D ^ n :=
    fun h => by rw [← mul_pow, ← mul_pow, h]
  have hAD : (F.A * F.D) ^ n = (F.B * F.C) ^ n → F.A ^ n * F.D ^ n = F.B ^ n * F.C ^ n :=
    fun h => by rw [← mul_pow, ← mul_pow, h]
  generalize F.A ^ n = a at S1 S2 S3 all_eq two_n hAB hAD
  generalize F.B ^ n = b at S1 S2 S3 all_eq two_n hAB hAD
  generalize F.C ^ n = c at S1 S2 S3 all_eq two_n hAB hAD
  generalize F.D ^ n = d at S1 S2 S3 all_eq two_n hAB hAD
  -- each `z_E` coincides with another one
  have cA : (a - b) * (a - c) * (a - d) = 0 := by
    have : (F.τ : ℂ) * ((a - b) * (a - c) * (a - d)) = 0 := by
      linear_combination S3 - (b + c + d) * S2 + (b * c + b * d + c * d) * S1 - b * c * d * S0
    exact (mul_eq_zero.1 this).resolve_left hτ
  have cB : (b - a) * (b - c) * (b - d) = 0 := by
    have : -(F.μ : ℂ) * ((b - a) * (b - c) * (b - d)) = 0 := by
      linear_combination S3 - (a + c + d) * S2 + (a * c + a * d + c * d) * S1 - a * c * d * S0
    exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 hμ)
  have cC : (c - a) * (c - b) * (c - d) = 0 := by
    have : (1 - (F.τ : ℂ)) * ((c - a) * (c - b) * (c - d)) = 0 := by
      linear_combination S3 - (a + b + d) * S2 + (a * b + a * d + b * d) * S1 - a * b * d * S0
    exact (mul_eq_zero.1 this).resolve_left hτ'
  have cD : (d - a) * (d - b) * (d - c) = 0 := by
    have : -(1 - (F.μ : ℂ)) * ((d - a) * (d - b) * (d - c)) = 0 := by
      linear_combination S3 - (a + b + c) * S2 + (a * b + a * c + b * c) * S1 - a * b * c * S0
    exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 hμ')
  -- `Σ c_E (z_E - x) = 0`
  have pair : ∀ x : ℂ, (F.τ : ℂ) * (a - x) - F.μ * (b - x) + (1 - F.τ) * (c - x)
      - (1 - F.μ) * (d - x) = 0 := fun x => by linear_combination S1 - x * S0
  have z0 : ∀ {x y : ℂ}, x - y = 0 → x = y := fun h => sub_eq_zero.1 h
  -- `d` once `a = b = c`
  have fin_d : a = b → a = c → F.IsRat := fun hab hac => by
    refine all_eq hab hac ?_
    rcases mul_eq_zero.1 cD with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact (z0 h).symm
      · rw [z0 h, hab]
    · rw [z0 h, hac]
  rcases mul_eq_zero.1 cA with h | had
  · rcases mul_eq_zero.1 h with hab | hac
    · -- `a = b`
      have hab := z0 hab
      rcases mul_eq_zero.1 cC with h' | hcd
      · rcases mul_eq_zero.1 h' with hca | hcb
        · exact fin_d hab (z0 hca).symm
        · exact fin_d hab (by rw [z0 hcb, hab])
      · -- `a = b`, `c = d`: then `τ = μ`, or `a = c`
        have hcd := z0 hcd
        have : ((F.τ : ℂ) - F.μ) * (a - c) = 0 := by
          linear_combination pair c - (F.μ : ℂ) * hab - (1 - (F.μ : ℂ)) * hcd
        rcases mul_eq_zero.1 this with htm | hac
        · have hτμ : F.τ = F.μ := Complex.ofReal_injective (z0 htm)
          have e := hAB (by rw [F.AB_eq_CD hτμ])
          rw [← hab, ← hcd] at e
          exact two_n (by rw [hab]) (by rw [sq, sq, e]) (by rw [← hcd, sq, sq, e])
        · exact fin_d hab (z0 hac)
    · -- `a = c`: then `a = b`
      have hac := z0 hac
      have hab : a = b := by
        rcases mul_eq_zero.1 cB with h' | hbd
        · rcases mul_eq_zero.1 h' with hba | hbc
          · exact (z0 hba).symm
          · rw [z0 hbc, hac]
        · have hbd := z0 hbd
          have : a - b = 0 := by
            linear_combination pair b + (1 - (F.τ : ℂ)) * hac - (1 - (F.μ : ℂ)) * hbd
          exact z0 this
      exact fin_d hab hac
  · -- `a = d`
    have had := z0 had
    rcases mul_eq_zero.1 cB with h' | hbd
    · rcases mul_eq_zero.1 h' with hba | hbc
      · have hab := (z0 hba).symm
        refine all_eq hab ?_ had
        rcases mul_eq_zero.1 cC with h'' | hcd
        · rcases mul_eq_zero.1 h'' with hca | hcb
          · exact (z0 hca).symm
          · rw [z0 hcb, hab]
        · rw [z0 hcd, had]
      · -- `a = d`, `b = c`: then `τ + μ = 1`, or `a = b`
        have hbc := z0 hbc
        have : ((F.τ : ℂ) + F.μ - 1) * (a - b) = 0 := by
          linear_combination pair b + (1 - (F.τ : ℂ)) * hbc - (1 - (F.μ : ℂ)) * had
        rcases mul_eq_zero.1 this with htm | hab
        · have hτμ : F.τ + F.μ = 1 := by
            have h1 : ((F.τ + F.μ : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
              push_cast; linear_combination htm
            exact_mod_cast h1
          have e := hAD (by rw [F.AD_eq_BC hτμ])
          rw [← had, ← hbc] at e
          exact two_n (by rw [sq, sq, e]) (by rw [← hbc, sq, sq, e]) (by rw [had])
        · have hab := z0 hab
          exact all_eq hab (by rw [hab, hbc]) had
    · -- `a = d = b`
      have hab : a = b := by rw [had, z0 hbd]
      refine all_eq hab ?_ had
      rcases mul_eq_zero.1 cC with h'' | hcd
      · rcases mul_eq_zero.1 h'' with hca | hcb
        · exact (z0 hca).symm
        · rw [z0 hcb, hab]
      · rw [z0 hcd, had]

/-- **Remark 5.14 (a)**: for an irrational table, the non-degenerate modes `k` (`m(k) ≠ 0`) have
`inf |m(k)| = 0`, and arbitrarily large such modes are arbitrarily small: the analogue of `σ` for
an infinite orbit is `0`. -/
theorem exists_small_nondegenerate_mode (hirr : ¬ F.IsRat) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k ≥ N, F.m k ≠ 0 ∧ ‖F.m k‖ < ε := by
  obtain ⟨n, hn, h1, h2, h3, h4⟩ :=
    Axis.exists_pow_near_one F.nA F.nB F.nC F.nD (by positivity : 0 < ε / 7) (max N 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have s1 : ‖F.m n‖ < 2 * (ε / 7) := by
    have := Axis.m_shift F h1 h2 h3 h4 0
    rwa [add_zero, F.m_zero, sub_zero] at this
  have s2 : ‖F.m (2 * n)‖ < 4 * (ε / 7) := by
    have := Axis.m_shift F h1 h2 h3 h4 n
    rw [show n + n = 2 * n by ring] at this
    have := norm_add_le (F.m (2 * n) - F.m n) (F.m n)
    rw [sub_add_cancel] at this
    linarith
  have s3 : ‖F.m (3 * n)‖ < 6 * (ε / 7) := by
    have := Axis.m_shift F h1 h2 h3 h4 (2 * n)
    rw [show n + 2 * n = 3 * n by ring] at this
    have := norm_add_le (F.m (3 * n) - F.m (2 * n)) (F.m (2 * n))
    rw [sub_add_cancel] at this
    linarith
  by_cases e1 : F.m n = 0
  · by_cases e2 : F.m (2 * n) = 0
    · by_cases e3 : F.m (3 * n) = 0
      · exact absurd (F.isRat_of_three hn1 e1 e2 e3) hirr
      · exact ⟨3 * n, by omega, e3, by linarith⟩
    · exact ⟨2 * n, by omega, e2, by linarith⟩
  · exact ⟨n, hnN, e1, by linarith⟩

end Feet

end Wobbly
