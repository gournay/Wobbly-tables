import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Instances.RealVectorSpace
import Wobbly.Coercive
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Prod

open Complex ComplexConjugate MeasureTheory AddCircle

/-!
# Proposition 4.13: moving the axis of rotation

`G_k(v) = ∫₀^{2π} e^{-ikφ} g(v + r e^{iφ}) dφ` is (up to `2π`) the `k`-th Fourier coefficient of the
terrain on the circle of radius `r` centred at `v`. Integration by parts in `φ` gives the recurrence
`k G_k = r (∂G_{k-1} - ∂̄G_{k+1})` (Wirtinger derivatives in `v`). For a Lipschitz terrain the `G_k`
with `k ≠ 0` are bounded, and a Liouville argument shows that `G₂ = G₃ = 0` (or `G₂ = G₄ = 0`) on all
circles forces `G_k = 0` for all `|k| ≥ 2`, `G_{±1}` constant and `G₀` affine; then `g` is affine by
uniqueness of Fourier coefficients. Lipschitz terrains are reduced to `C¹` ones by mollification.

* `affine_of_γR`: the analytic statement;
* `affine_of_F₀v`: **Proposition 4.13 (b)** for terrains which are Lipschitz on the whole plane
  (the paraboloids of the general statement are then excluded) and all tables but the square
  (`square_of_m3_m4`), by a Liouville argument;
* `F₀v_of_affine`: the converse.

The local version (and the global version for continuous terrains) is in `Wobbly.AxisLocal`.
-/

namespace Wobbly

namespace Axis

/-! ### Elementary facts on `rot` -/

lemma rot_zero' : rot 0 = 1 := by simp [rot]

lemma rot_two_pi : rot (2 * Real.pi) = 1 := by
  rw [rot]; push_cast; exact Complex.exp_two_pi_mul_I

lemma rot_add' (a b : ℝ) : rot (a + b) = rot a * rot b := by
  unfold rot; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_rot (φ : ℝ) : conj (rot φ) = rot (-φ) := by
  unfold rot; rw [← Complex.exp_conj]; congr 1; simp [map_mul, Complex.conj_ofReal]

lemma rot_int_two_pi (k : ℤ) : rot (k * (2 * Real.pi)) = 1 := by
  unfold rot
  have : ((k * (2 * Real.pi) : ℝ) : ℂ) * I = k * (2 * Real.pi * I) := by push_cast; ring
  rw [this]; exact Complex.exp_int_mul_two_pi_mul_I k

lemma hasDerivAt_rot (a φ : ℝ) : HasDerivAt (fun t : ℝ => rot (a * t)) (a * I * rot (a * φ)) φ := by
  unfold rot
  have h : HasDerivAt (fun t : ℝ => ((a * t : ℝ) : ℂ) * I) (a * I) φ := by
    have := ((hasDerivAt_id φ).const_mul a).ofReal_comp.mul_const I
    simpa using this
  have := h.cexp
  convert this using 1; ring

/-- `∫₀^{2π} e^{ijφ} dφ = 2π [j = 0]`. -/
lemma integral_rot_int (j : ℤ) :
    ∫ φ in (0 : ℝ)..2 * Real.pi, rot (j * φ) = if j = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hj
  · subst hj; simp [rot_zero']
  · have hj' : ((j : ℝ) : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
    have hd : ∀ φ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => rot (j * t) / ((j : ℂ) * I)) (rot (j * φ)) φ := by
      intro φ _
      have := (hasDerivAt_rot j φ).div_const ((j : ℂ) * I)
      convert this using 1; field_simp; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_rot.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
    simp only [mul_zero, rot_zero']
    rw [show (j : ℝ) * (2 * Real.pi) = (j : ℝ) * (2 * Real.pi) from rfl, rot_int_two_pi, sub_self]

/-- Uniqueness of Fourier coefficients for continuous `2π`-periodic functions. -/
theorem eq_zero_of_fourier {ψ : ℝ → ℂ} (hc : Continuous ψ) (hp : Function.Periodic ψ (2 * Real.pi))
    (h : ∀ n : ℤ, ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = 0) (φ : ℝ) : ψ φ = 0 := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) := ⟨hp.lift, by
    exact continuous_quot_lift _ hc⟩
  have hF : ∀ x : ℝ, F x = ψ x := fun x => rfl
  have hcoef : ∀ n : ℤ, fourierCoeff F n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
    have e : ∀ x : ℝ, (@fourier (2 * Real.pi) (-n) (x : AddCircle (2 * Real.pi))) • F x =
        ψ x * rot (-(n : ℝ) * x) := by
      intro x
      rw [fourier_coe_apply, hF, smul_eq_mul, mul_comm, rot]
      congr 2
      push_cast; field_simp
    simp_rw [e, h n, smul_zero]
  have h0 : ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ F = 0 := by
    apply fourierBasis.repr.injective
    ext i
    rw [fourierBasis_repr, fourierCoeff_toLp, hcoef, map_zero]; rfl
  have : F = 0 := by
    have hinj := ContinuousMap.toLp_injective (α := AddCircle (2 * Real.pi)) (E := ℂ) (𝕜 := ℂ) (p := 2)
      (μ := haarAddCircle)
    exact hinj (by rw [h0, map_zero])
  have := congrArg (fun G : C(AddCircle (2 * Real.pi), ℂ) => G φ) this
  simpa [hF] using this


/-! ### Fourier coefficients on circles -/

variable (r : ℝ)

/-- `G_k(v) = ∫₀^{2π} e^{-ikφ} f(v + r e^{iφ}) dφ`, `2π` times the `k`-th Fourier coefficient of
`f` restricted to the circle of radius `r` centred at `v`. -/
noncomputable def γ (k : ℤ) (f : ℂ → ℂ) (v : ℂ) : ℂ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) * f (v + r * rot φ)

/-- Wirtinger derivatives `∂f = (∂_x f - i ∂_y f)/2` and `∂̄f = (∂_x f + i ∂_y f)/2`. -/
noncomputable def dz (f : ℂ → ℂ) (x : ℂ) : ℂ := (fderiv ℝ f x 1 - I * fderiv ℝ f x I) / 2
noncomputable def dzb (f : ℂ → ℂ) (x : ℂ) : ℂ := (fderiv ℝ f x 1 + I * fderiv ℝ f x I) / 2

/-- A real-linear map `ℂ → ℂ` is `h ↦ a h + b h̄`. -/
lemma clm_eq (D : ℂ →L[ℝ] ℂ) (h : ℂ) :
    D h = (D 1 - I * D I) / 2 * h + (D 1 + I * D I) / 2 * conj h := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, h = a + b * I := ⟨h.re, h.im, (Complex.re_add_im h).symm⟩
  have e1 : D ((a : ℂ) + (b : ℂ) * I) = a • D 1 + b • D I := by
    rw [show ((a : ℂ) + (b : ℂ) * I) = a • (1 : ℂ) + b • I by simp [Complex.real_smul]]
    rw [map_add, map_smul, map_smul]
  have e2 : conj ((a : ℂ) + (b : ℂ) * I) = a - b * I := by
    simp [map_add, map_mul, Complex.conj_ofReal]; ring
  rw [e1, e2, Complex.real_smul, Complex.real_smul]
  linear_combination ((b : ℂ) * D I) * Complex.I_sq

lemma hasDerivAt_rot1 (φ : ℝ) : HasDerivAt rot (I * rot φ) φ := by
  have := hasDerivAt_rot 1 φ
  simp only [Complex.ofReal_one, one_mul] at this
  exact this

lemma norm_rot' (φ : ℝ) : ‖rot φ‖ = 1 := norm_rot φ

variable {r}

lemma continuous_circle {E : Type*} [TopologicalSpace E] {f : ℂ → E} (hf : Continuous f) (v : ℂ) :
    Continuous fun φ : ℝ => f (v + r * rot φ) :=
  hf.comp (continuous_const.add (continuous_const.mul continuous_rot))

lemma continuous_rotk (k : ℤ) : Continuous fun φ : ℝ => rot (-(k : ℝ) * φ) :=
  continuous_rot.comp (continuous_const.mul continuous_id)

lemma continuous_dz {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dz f) := by
  have h := hf.continuous_fderiv one_ne_zero
  unfold dz
  exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp h).sub
    (continuous_const.mul ((ContinuousLinearMap.apply ℝ ℂ I).continuous.comp h))).div_const _

lemma continuous_dzb {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dzb f) := by
  have h := hf.continuous_fderiv one_ne_zero
  unfold dzb
  exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp h).add
    (continuous_const.mul ((ContinuousLinearMap.apply ℝ ℂ I).continuous.comp h))).div_const _

/-- The recurrence `k G_k = r (G_{k-1}[∂f] - G_{k+1}[∂̄f])` (integration by parts in `φ`). -/
theorem γ_recurrence {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (k : ℤ) (v : ℂ) :
    (k : ℂ) * γ r k f v = r * (γ r (k - 1) (dz f) v - γ r (k + 1) (dzb f) v) := by
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  set u : ℝ → ℂ := fun φ => f (v + r * rot φ)
  set u' : ℝ → ℂ := fun φ => fderiv ℝ f (v + r * rot φ) (r * (I * rot φ))
  set w : ℝ → ℂ := fun φ => rot (-(k : ℝ) * φ)
  set w' : ℝ → ℂ := fun φ => -(k : ℝ) * I * rot (-(k : ℝ) * φ)
  have hu : ∀ φ, HasDerivAt u (u' φ) φ := fun φ => by
    have h1 : HasDerivAt (fun t : ℝ => v + (r : ℂ) * rot t) (r * (I * rot φ)) φ :=
      ((hasDerivAt_rot1 φ).const_mul (r : ℂ)).const_add v
    exact (hdiff (v + r * rot φ)).hasFDerivAt.comp_hasDerivAt φ h1
  have hw : ∀ φ, HasDerivAt w (w' φ) φ := fun φ => by
    have := hasDerivAt_rot (-(k : ℝ)) φ
    simpa [w, w'] using this
  have hcu' : Continuous u' := by
    have h := hf.continuous_fderiv one_ne_zero
    exact (h.comp (continuous_const.add (continuous_const.mul continuous_rot))).clm_apply
      (continuous_const.mul (continuous_const.mul continuous_rot))
  have hcw' : Continuous w' := continuous_const.mul (continuous_rotk k)
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi)
    (fun φ _ => hu φ) (fun φ _ => hw φ) (hcu'.intervalIntegrable _ _) (hcw'.intervalIntegrable _ _)
  have hu2 : u (2 * Real.pi) = u 0 := by
    simp only [u]; rw [show (2 * Real.pi : ℝ) = ((1 : ℤ) : ℝ) * (2 * Real.pi) by simp, rot_int_two_pi,
      rot_zero']
  have hw2 : w (2 * Real.pi) = w 0 := by
    simp only [w]; rw [show -(k : ℝ) * (2 * Real.pi) = ((-k : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring,
      rot_int_two_pi, mul_zero, rot_zero']
  rw [hu2, hw2, sub_self, zero_sub] at ibp
  -- pointwise identities
  have e1 : ∀ φ, u φ * w' φ = (-(k : ℂ) * I) * (rot (-(k : ℝ) * φ) * f (v + r * rot φ)) := fun φ => by
    simp only [u, w']; push_cast; ring
  have e2 : ∀ φ, u' φ * w φ = (r * I) * (rot (-((k - 1 : ℤ) : ℝ) * φ) * dz f (v + r * rot φ)) -
      (r * I) * (rot (-((k + 1 : ℤ) : ℝ) * φ) * dzb f (v + r * rot φ)) := fun φ => by
    simp only [u', w]
    rw [clm_eq, dz, dzb]
    have c1 : conj ((r : ℂ) * (I * rot φ)) = -((r : ℂ) * I * rot (-φ)) := by
      simp [map_mul, Complex.conj_ofReal, conj_rot]; ring
    rw [c1]
    have r1 : rot (-((k - 1 : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) * rot φ := by
      rw [← rot_add']; congr 1; push_cast; ring
    have r2 : rot (-((k + 1 : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) * rot (-φ) := by
      rw [← rot_add']; congr 1; push_cast; ring
    rw [r1, r2]; ring
  simp_rw [e1, e2] at ibp
  have hi1 : IntervalIntegrable (fun φ : ℝ => rot (-((k - 1 : ℤ) : ℝ) * φ) * dz f (v + r * rot φ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    ((continuous_rotk (k - 1)).mul (continuous_circle (continuous_dz hf) v)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun φ : ℝ => rot (-((k + 1 : ℤ) : ℝ) * φ) * dzb f (v + r * rot φ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    ((continuous_rotk (k + 1)).mul (continuous_circle (continuous_dzb hf) v)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi1.const_mul _)
    (hi2.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at ibp
  have key : I * ((k : ℂ) * γ r k f v - r * (γ r (k - 1) (dz f) v - γ r (k + 1) (dzb f) v)) = 0 := by
    simp only [γ]; linear_combination -ibp
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h Complex.I_ne_zero
  · exact sub_eq_zero.1 h

/-! ### Differentiating `G_k` in the centre `v` -/

lemma hasFDerivAt_γ {f : ℂ → ℂ} {L : ℝ} (hf : ContDiff ℝ 1 f) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (k : ℤ) (v : ℂ) :
    HasFDerivAt (γ r k f)
      (∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) • fderiv ℝ f (v + r * rot φ)) v := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  unfold γ
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume) (s := Set.univ)
    (F := fun x φ => rot (-(k : ℝ) * φ) * f (x + r * rot φ))
    (F' := fun x φ => rot (-(k : ℝ) * φ) • fderiv ℝ f (x + r * rot φ))
    (bound := fun _ => L) Filter.univ_mem ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((continuous_rotk k).mul (continuous_circle hf.continuous x)).aestronglyMeasurable
  · exact ((continuous_rotk k).mul (continuous_circle hf.continuous v)).intervalIntegrable _ _
  · exact ((continuous_rotk k).smul (continuous_circle hcont v)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun φ _ x _ => ?_
    rw [norm_smul, norm_rot', one_mul]; exact hb _
  · refine Filter.Eventually.of_forall fun φ _ x _ => ?_
    have h1 : HasFDerivAt (fun x : ℂ => x + (r : ℂ) * rot φ) (ContinuousLinearMap.id ℝ ℂ) x :=
      (hasFDerivAt_id x).add_const _
    have h3 := (hdiff (x + r * rot φ)).hasFDerivAt.comp x h1
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3.const_mul (rot (-(k : ℝ) * φ))

lemma fderiv_γ_apply {f : ℂ → ℂ} {L : ℝ} (hf : ContDiff ℝ 1 f) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (k : ℤ) (v h : ℂ) :
    fderiv ℝ (γ r k f) v h =
      ∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) * fderiv ℝ f (v + r * rot φ) h := by
  rw [(hasFDerivAt_γ hf hb k v).fderiv, ContinuousLinearMap.intervalIntegral_apply]
  · rfl
  · exact ((continuous_rotk k).smul (continuous_circle (hf.continuous_fderiv one_ne_zero) v)).intervalIntegrable _ _

lemma dz_γ {f : ℂ → ℂ} {L : ℝ} (hf : ContDiff ℝ 1 f) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (k : ℤ) (v : ℂ) :
    dz (γ r k f) v = γ r k (dz f) v := by
  have hcont := hf.continuous_fderiv one_ne_zero
  have i1 : ∀ h : ℂ, IntervalIntegrable (fun φ : ℝ => rot (-(k : ℝ) * φ) * fderiv ℝ f (v + r * rot φ) h)
      MeasureTheory.volume 0 (2 * Real.pi) := fun h =>
    ((continuous_rotk k).mul ((continuous_circle hcont v).clm_apply continuous_const)).intervalIntegrable _ _
  unfold dz
  rw [fderiv_γ_apply hf hb, fderiv_γ_apply hf hb, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (i1 1) ((i1 I).const_mul I), ← intervalIntegral.integral_div]
  unfold γ
  congr 1; ext φ; ring

lemma dzb_γ {f : ℂ → ℂ} {L : ℝ} (hf : ContDiff ℝ 1 f) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (k : ℤ) (v : ℂ) :
    dzb (γ r k f) v = γ r k (dzb f) v := by
  have hcont := hf.continuous_fderiv one_ne_zero
  have i1 : ∀ h : ℂ, IntervalIntegrable (fun φ : ℝ => rot (-(k : ℝ) * φ) * fderiv ℝ f (v + r * rot φ) h)
      MeasureTheory.volume 0 (2 * Real.pi) := fun h =>
    ((continuous_rotk k).mul ((continuous_circle hcont v).clm_apply continuous_const)).intervalIntegrable _ _
  unfold dzb
  rw [fderiv_γ_apply hf hb, fderiv_γ_apply hf hb, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i1 1) ((i1 I).const_mul I), ← intervalIntegral.integral_div]
  unfold γ
  congr 1; ext φ; ring

lemma differentiable_γ {f : ℂ → ℂ} {L : ℝ} (hf : ContDiff ℝ 1 f) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (k : ℤ) : Differentiable ℝ (γ r k f) := fun v => (hasFDerivAt_γ hf hb k v).differentiableAt

/-! ### Bounds -/

/-- For `k ≠ 0`, `|G_k(v)| ≤ 2π L r` if `f` is `L`-Lipschitz. -/
lemma norm_γ_le {f : ℂ → ℂ} {L : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) (hr : 0 ≤ r)
    (hfc : Continuous f) {k : ℤ} (hk : k ≠ 0) (v : ℂ) : ‖γ r k f v‖ ≤ 2 * Real.pi * (L * r) := by
  have h0 : ∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) = 0 := by
    have := integral_rot_int (-k); push_cast at this; rw [this]; simp [hk]
  have e : γ r k f v = ∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) * (f (v + r * rot φ) - f v) := by
    unfold γ
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_mul_const, h0, zero_mul, sub_zero]
    · exact ((continuous_rotk k).mul (continuous_circle hfc v)).intervalIntegrable _ _
    · exact ((continuous_rotk k).mul continuous_const).intervalIntegrable _ _
  rw [e]
  have hL : 0 ≤ L := by
    have := hf 1 0; simp at this
    nlinarith [norm_nonneg (f 1 - f 0)]
  calc _ ≤ (L * r) * |2 * Real.pi - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro φ _
        rw [norm_mul, norm_rot', one_mul]
        calc _ ≤ L * ‖v + r * rot φ - v‖ := hf _ _
          _ = L * r := by rw [add_sub_cancel_left, norm_mul, norm_rot', mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hr]
    _ = 2 * Real.pi * (L * r) := by rw [sub_zero, abs_of_pos (by positivity)]; ring

/-! ### A Liouville lemma -/

/-- If `∂̄H = 0` at `z` (for a real-differentiable `H`), then `H` is complex-differentiable at `z`. -/
lemma differentiableAt_of_dzb {H : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ H z) (h : dzb H z = 0) :
    DifferentiableAt ℂ H z := by
  set D := fderiv ℝ H z
  have hDI : D I = I * D 1 := by
    unfold dzb at h
    have : D 1 + I * D I = 0 := by
      have := congrArg (· * 2) h; simp at this; exact this
    linear_combination (-I) * this + (D I) * Complex.I_sq
  let g' : ℂ →L[ℂ] ℂ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (D 1)
  have hg : g'.restrictScalars ℝ = D := by
    ext1 x
    simp only [ContinuousLinearMap.coe_restrictScalars', g', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [clm_eq D x, hDI]
    linear_combination (x * D 1 / 2 - conj x * D 1 / 2) * Complex.I_sq
  exact (hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt hg).differentiableAt

lemma dzb_sub_comp {G : ℂ → ℂ} (hG : Differentiable ℝ G) (w z : ℂ) :
    dzb (fun z => G (z + w) - G z) z = dzb G (z + w) - dzb G z := by
  have h1 : HasFDerivAt (fun z => G (z + w)) (fderiv ℝ G (z + w)) z := by
    have h := (hG (z + w)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const w)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have h2 : HasFDerivAt (fun z => G (z + w) - G z) (fderiv ℝ G (z + w) - fderiv ℝ G z) z :=
    h1.sub (hG z).hasFDerivAt
  unfold dzb; rw [h2.fderiv]
  simp only [sub_apply]; ring

/-- A bounded real-differentiable `G : ℂ → ℂ` with constant `∂̄G` is constant. -/
theorem const_of_dzb_const {G : ℂ → ℂ} (hG : Differentiable ℝ G) {C : ℝ} (hb : ∀ z, ‖G z‖ ≤ C)
    {c : ℂ} (hc : ∀ z, dzb G z = c) (z : ℂ) : G z = G 0 := by
  -- the differences `z ↦ G (z + w) - G z` are entire and bounded, hence constant
  have hdiff : ∀ w z, G (z + w) - G z = G w - G 0 := by
    intro w z
    set H : ℂ → ℂ := fun z => G (z + w) - G z
    have hH : Differentiable ℂ H := fun z => by
      apply differentiableAt_of_dzb
      · exact ((hG (z + w)).comp z ((differentiableAt_id).add_const w)).sub (hG z)
      · rw [dzb_sub_comp hG, hc, hc, sub_self]
    have hbd : Bornology.IsBounded (Set.range H) := by
      refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨C + C, ?_⟩
      rintro _ ⟨y, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_sub_le _ _).trans (add_le_add (hb _) (hb _))
    have := hH.apply_eq_apply_of_bounded hbd z 0
    simpa [H] using this
  -- `κ(w) = G w - G 0` is additive and continuous, hence `ℝ`-linear, and bounded, hence zero
  let κ : ℂ →+ ℂ := AddMonoidHom.mk' (fun w => G w - G 0) (fun a b => by
    have := hdiff b a; linear_combination this)
  have hκ : Continuous κ := (hG.continuous.sub continuous_const)
  have hlin : ∀ t : ℝ, κ (t • z) = t • κ z := fun t => map_real_smul κ hκ t z
  by_contra hne
  have hpos : 0 < ‖κ z‖ := norm_pos_iff.2 (by simp only [κ, AddMonoidHom.mk'_apply]; exact sub_ne_zero.2 hne)
  set t := (C + C + 1) / ‖κ z‖
  have h1 := hlin t
  have h2 : ‖κ (t • z)‖ ≤ C + C := by
    simp only [κ, AddMonoidHom.mk'_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hb _) (hb _))
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hpos)] at h2
  rw [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

/-! ### Real-valued functions -/

/-- For a real-valued `f`, `G_{-k} = conj G_k`. -/
lemma γ_neg {f : ℂ → ℂ} (hreal : ∀ x, conj (f x) = f x) (k : ℤ) (v : ℂ) :
    γ r (-k) f v = conj (γ r k f v) := by
  unfold γ
  rw [← intervalIntegral.intervalIntegral_conj]
  congr 1; ext φ
  rw [map_mul, hreal, conj_rot]; push_cast; ring_nf

/-- For a real-valued differentiable `F`, `∂F = conj (∂̄F)`. -/
lemma dz_eq_conj_dzb {F : ℂ → ℂ} (hreal : ∀ x, conj (F x) = F x) (hd : DifferentiableAt ℝ F x) :
    dz F x = conj (dzb F x) := by
  have hF : F = fun x => ((F x).re : ℂ) := funext fun x => by
    have := hreal x; rw [Complex.conj_eq_iff_re] at this; exact this.symm
  have hre : DifferentiableAt ℝ (fun x => (F x).re) x := (Complex.reCLM.differentiableAt).comp x hd
  have e : fderiv ℝ F x = Complex.ofRealCLM.comp (fderiv ℝ (fun x => (F x).re) x) := by
    conv_lhs => rw [hF]
    exact (Complex.ofRealCLM.hasFDerivAt.comp x hre.hasFDerivAt).fderiv
  unfold dz dzb
  rw [e]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply, map_div₀,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma dz_of_eq_zero {G : ℂ → ℂ} (h : ∀ v, G v = 0) (v : ℂ) : dz G v = 0 := by
  have : G = fun _ => 0 := funext h
  subst this; simp [dz]

lemma dzb_of_eq_zero {G : ℂ → ℂ} (h : ∀ v, G v = 0) (v : ℂ) : dzb G v = 0 := by
  have : G = fun _ => 0 := funext h
  subst this; simp [dzb]

lemma dzb_of_const {G : ℂ → ℂ} (h : ∀ v, G v = G 0) (v : ℂ) : dzb G v = 0 := by
  have : G = fun _ => G 0 := funext h
  rw [this]; simp [dzb]

/-! ### The core statement, for `C¹` functions -/

/-- **Proposition 4.13 (core)**: if `f` is real-valued, `C¹` with bounded derivative, and its Fourier
coefficients `G₂` and `G₃` (or `G₂` and `G₄`) on all the circles of radius `r > 0` vanish, then `f`
is affine: `f x = a + b x + conj b conj x`. -/
theorem affine_of_γ {f : ℂ → ℂ} {L : ℝ} (hr : 0 < r) (hf : ContDiff ℝ 1 f)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (hreal : ∀ x, conj (f x) = f x)
    (h2 : ∀ v, γ r 2 f v = 0) (h34 : (∀ v, γ r 3 f v = 0) ∨ (∀ v, γ r 4 f v = 0)) :
    ∃ a b : ℂ, ∀ x, f x = a + b * x + conj b * conj x := by
  set G : ℤ → ℂ → ℂ := fun k => γ r k f with hGdef
  have hlip : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖ := fun x y => by
    have := (convex_univ : Convex ℝ (Set.univ : Set ℂ)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.differentiable one_ne_zero) z) (fun z _ => hb z) (Set.mem_univ y) (Set.mem_univ x)
    simpa using this
  have hrec : ∀ (k : ℤ) (v : ℂ), (k : ℂ) * G k v = r * (dz (G (k - 1)) v - dzb (G (k + 1)) v) := fun k v => by
    simp only [G]; rw [dz_γ hf hb, dzb_γ hf hb]; exact γ_recurrence hf k v
  have hdif : ∀ k, Differentiable ℝ (G k) := fun k => differentiable_γ hf hb k
  have hbd : ∀ k, k ≠ 0 → ∀ v, ‖G k v‖ ≤ 2 * Real.pi * (L * r) := fun k hk v =>
    norm_γ_le hlip hr.le hf.continuous hk v
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  -- Step 0: `G₃ = 0`
  have h3 : ∀ v, G 3 v = 0 := by
    rcases h34 with h | h
    · exact h
    · intro v
      have := hrec 3 v
      rw [show (3 : ℤ) - 1 = 2 by norm_num, show (3 : ℤ) + 1 = 4 by norm_num,
        dz_of_eq_zero h2, dzb_of_eq_zero h] at this
      simpa using this
  -- Step 1: `G_n = 0` for `n ≥ 2`
  have hpos : ∀ m : ℕ, (∀ v, G (m + 2) v = 0) ∧ (∀ v, G (m + 3) v = 0) := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using h2, by simpa using h3⟩
    | succ m ih =>
      obtain ⟨ha, hb'⟩ := ih
      refine ⟨by push_cast; rw [show (m : ℤ) + 1 + 2 = m + 3 by ring]; exact hb', ?_⟩
      -- `∂̄G_{m+4} = 0`, so `G_{m+4}` is constant
      have hz : ∀ v, dzb (G (m + 4)) v = 0 := fun v => by
        have := hrec (m + 3) v
        rw [show (m : ℤ) + 3 - 1 = m + 2 by ring, show (m : ℤ) + 3 + 1 = m + 4 by ring, hb' v,
          dz_of_eq_zero ha] at this
        simpa [hr0] using this
      have hne4 : ((m : ℤ) + 4) ≠ 0 := by omega
      have hc4 : ∀ v, G (m + 4) v = G (m + 4) 0 :=
        const_of_dzb_const (hdif _) (hbd _ hne4) hz
      -- `∂̄G_{m+5}` is constant, so `G_{m+5}` is constant and `∂̄G_{m+5} = 0`
      have hz5 : ∀ v, dzb (G (m + 5)) v = -((m + 4 : ℂ) * G (m + 4) 0) / r := fun v => by
        have := hrec (m + 4) v
        rw [show (m : ℤ) + 4 - 1 = m + 3 by ring, show (m : ℤ) + 4 + 1 = m + 5 by ring,
          dz_of_eq_zero hb', hc4 v] at this
        field_simp; push_cast at this ⊢; linear_combination this
      have hne5 : ((m : ℤ) + 5) ≠ 0 := by omega
      have hc5 := const_of_dzb_const (hdif _) (hbd _ hne5) hz5
      have h0 := hz5 0
      rw [dzb_of_const hc5] at h0
      have hm : (m + 4 : ℂ) ≠ 0 := by exact_mod_cast (show (m + 4 : ℕ) ≠ 0 by omega)
      have : G (m + 4) 0 = 0 := by
        have h' : -((m + 4 : ℂ) * G (m + 4) 0) / r = 0 := h0.symm
        rw [div_eq_zero_iff, neg_eq_zero] at h'
        rcases h'.resolve_right hr0 |> mul_eq_zero.1 with h | h
        · exact absurd h hm
        · exact h
      intro v
      rw [show (((m + 1 : ℕ) : ℤ) + 3) = m + 4 by push_cast; ring, hc4 v, this]
  have hge : ∀ k : ℤ, 2 ≤ k → ∀ v, G k v = 0 := fun k hk v => by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨(k - 2).toNat, by omega⟩
    exact (hpos m).1 v
  have hle : ∀ k : ℤ, k ≤ -2 → ∀ v, G k v = 0 := fun k hk v => by
    have := γ_neg (r := r) hreal (-k) v
    rw [neg_neg] at this
    show γ r k f v = 0
    rw [this, show γ r (-k) f v = 0 from hge (-k) (by omega) v, map_zero]
  -- Step 2: `G_{-1}` is constant and `∂̄G₀ = G_{-1}/r`
  have hzm1 : ∀ v, dzb (G (-1)) v = 0 := fun v => by
    have := hrec (-2) v
    rw [show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) + 1 = -1 by norm_num, hle (-2) le_rfl v,
      dz_of_eq_zero (hle (-3) (by norm_num))] at this
    simpa [hr0] using this
  have hcm1 := const_of_dzb_const (hdif (-1)) (hbd (-1) (by norm_num)) hzm1
  set β := G (-1) 0 / r with hβ
  have hdzb0 : ∀ v, dzb (G 0) v = β := fun v => by
    have := hrec (-1) v
    rw [show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) + 1 = 0 by norm_num,
      dz_of_eq_zero (hle (-2) le_rfl), hcm1 v] at this
    rw [hβ]; field_simp; push_cast at this; linear_combination this
  have hreal0 : ∀ v, conj (G 0 v) = G 0 v := fun v => by
    have := γ_neg (r := r) hreal 0 v; simp only [neg_zero] at this; simp only [G]; rw [← this]
  have hdz0 : ∀ v, dz (G 0) v = conj β := fun v => by
    rw [dz_eq_conj_dzb hreal0 (hdif 0 v), hdzb0]
  -- Step 3: `G₀` is affine
  set Λ : ℂ →L[ℝ] ℂ := (conj β) • ContinuousLinearMap.id ℝ ℂ + β • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hΛ : ∀ h, Λ h = conj β * h + β * conj h := fun h => by
    simp [Λ, smul_eq_mul]
  have hG0 : ∀ v, G 0 v = G 0 0 + conj β * v + β * conj v := by
    set E : ℂ → ℂ := fun v => G 0 v - Λ v
    have hE : Differentiable ℝ E := (hdif 0).sub Λ.differentiable
    have hfE : ∀ v, fderiv ℝ E v = 0 := fun v => by
      have : fderiv ℝ E v = fderiv ℝ (G 0) v - Λ :=
        ((hdif 0 v).hasFDerivAt.sub Λ.hasFDerivAt).fderiv
      rw [this]; ext1 h
      rw [sub_apply, clm_eq (fderiv ℝ (G 0) v) h, hΛ]
      have e1 := hdz0 v; have e2 := hdzb0 v
      unfold dz at e1; unfold dzb at e2
      rw [e1, e2]; simp
    intro v
    have := is_const_of_fderiv_eq_zero hE hfE v 0
    simp only [E, map_zero, hΛ] at this
    linear_combination this
  -- Step 4: `G₁` and `G_{-1}`
  have hG1 : ∀ v, G 1 v = r * conj β := fun v => by
    have := hrec 1 v
    rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, hdz0 v,
      dzb_of_eq_zero (hge 2 le_rfl)] at this
    simpa using this
  have hGm1 : ∀ v, G (-1) v = r * β := fun v => by
    rw [hcm1 v, hβ]; field_simp
  -- Step 5: the affine function `p` has the same coefficients as `f`
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  set a : ℂ := G 0 0 / (2 * Real.pi)
  set b : ℂ := conj β / (2 * Real.pi)
  set p : ℂ → ℂ := fun x => a + b * x + conj b * conj x
  have hconjb : conj b = β / (2 * Real.pi) := by
    simp only [b, map_div₀, Complex.conj_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]
  have hpc : Continuous p := by
    exact (continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_const.mul Complex.continuous_conj)
  have hp : ∀ k v, γ r k p v = G k v := by
    intro k v
    have e : ∀ φ : ℝ, rot (-(k : ℝ) * φ) * p (v + r * rot φ) =
        (a + b * v + conj b * conj v) * rot (((-k : ℤ) : ℝ) * φ)
          + b * r * rot (((1 - k : ℤ) : ℝ) * φ) + conj b * r * rot (((-1 - k : ℤ) : ℝ) * φ) := by
      intro φ
      have r1 : rot (((1 - k : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) * rot φ := by
        rw [← rot_add']; congr 1; push_cast; ring
      have r2 : rot (((-1 - k : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) * rot (-φ) := by
        rw [← rot_add']; congr 1; push_cast; ring
      rw [r1, r2]; simp only [p, map_add, map_mul, Complex.conj_ofReal, conj_rot]
      push_cast; ring
    have ci : ∀ j : ℤ, IntervalIntegrable (fun φ : ℝ => rot ((j : ℝ) * φ)) volume 0 (2 * Real.pi) :=
      fun j => (continuous_rot.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    unfold γ
    simp_rw [e]
    rw [intervalIntegral.integral_add (((ci _).const_mul _).add ((ci _).const_mul _)) ((ci _).const_mul _),
      intervalIntegral.integral_add ((ci _).const_mul _) ((ci _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_rot_int, integral_rot_int, integral_rot_int]
    by_cases k0 : k = 0
    · subst k0; simp only [neg_zero, ite_true, show (1 - 0 : ℤ) ≠ 0 by norm_num,
        show (-1 - 0 : ℤ) ≠ 0 by norm_num, ite_false, mul_zero, add_zero]
      rw [hG0 v]; simp only [a, b, hconjb]; field_simp
    by_cases k1 : k = 1
    · subst k1; simp only [show (-1 : ℤ) ≠ 0 by norm_num, show (1 - 1 : ℤ) = 0 by norm_num,
        show (-1 - 1 : ℤ) ≠ 0 by norm_num, ite_true, ite_false, mul_zero, zero_add, add_zero]
      rw [hG1 v]; simp only [b]; field_simp
    by_cases km : k = -1
    · subst km; simp only [show (-(-1) : ℤ) ≠ 0 by norm_num, show (1 - -1 : ℤ) ≠ 0 by norm_num,
        show (-1 - -1 : ℤ) = 0 by norm_num, ite_true, ite_false, mul_zero, zero_add]
      rw [hGm1 v, hconjb]; field_simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [mul_zero, add_zero]
      rcases le_or_gt 2 k with hk | hk
      · exact (hge k hk v).symm
      · exact (hle k (by omega) v).symm
  -- Step 6: `f - p` has no Fourier coefficients on any circle, hence vanishes
  refine ⟨a, b, fun x => ?_⟩
  set v := x - r
  set ψ : ℝ → ℂ := fun φ => f (v + r * rot φ) - p (v + r * rot φ)
  have hψc : Continuous ψ := (continuous_circle hf.continuous v).sub (continuous_circle hpc v)
  have hψp : Function.Periodic ψ (2 * Real.pi) := fun φ => by
    simp only [ψ]
    rw [rot_add', show (2 * Real.pi : ℝ) = ((1 : ℤ) : ℝ) * (2 * Real.pi) by simp, rot_int_two_pi, mul_one]
  have hcoef : ∀ n : ℤ, ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = 0 := by
    intro n
    have e : ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = γ r n f v - γ r n p v := by
      unfold γ
      rw [← intervalIntegral.integral_sub]
      · congr 1; ext φ; simp only [ψ]; ring
      · exact ((continuous_rotk n).mul (continuous_circle hf.continuous v)).intervalIntegrable _ _
      · exact ((continuous_rotk n).mul (continuous_circle hpc v)).intervalIntegrable _ _
    rw [e, hp]; exact sub_self _
  have := eq_zero_of_fourier hψc hψp hcoef 0
  simp only [ψ, rot_zero', mul_one, v, sub_add_cancel] at this
  simp only [p] at this
  linear_combination this


/-! ### From `C¹` to Lipschitz terrains: mollification -/

/-- A continuous function satisfying `g (x + y) + g 0 = g x + g y` is affine. -/
lemma affine_of_additive {g : ℂ → ℝ} (hc : Continuous g) (h : ∀ x y, g (x + y) + g 0 = g x + g y) :
    ∀ x, g x = g 0 + dot ⟨g 1 - g 0, g I - g 0⟩ x := by
  let κ : ℂ →+ ℝ := AddMonoidHom.mk' (fun x => g x - g 0) (fun a b => by
    have := h a b; linarith)
  have hκ : Continuous κ := hc.sub continuous_const
  intro x
  have e : x = x.re • (1 : ℂ) + x.im • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]; exact (Complex.re_add_im x).symm
  have h1 : κ x = x.re * κ 1 + x.im * κ I := by
    conv_lhs => rw [e]
    rw [map_add, map_real_smul κ hκ, map_real_smul κ hκ, smul_eq_mul, smul_eq_mul]
  simp only [κ, AddMonoidHom.mk'_apply] at h1
  unfold dot; simp only
  linarith

variable (r) in
/-- `G_k` for a real-valued terrain. -/
noncomputable def γR (k : ℤ) (g : ℂ → ℝ) (v : ℂ) : ℂ := γ r k (fun x => (g x : ℂ)) v

/-- The mollified terrain `g_φ = φ ⋆ g`. -/
noncomputable def moll (φ : ContDiffBump (0 : ℂ)) (g : ℂ → ℝ) : ℂ → ℝ :=
  MeasureTheory.convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma moll_apply (φ : ContDiffBump (0 : ℂ)) (g : ℂ → ℝ) (x : ℂ) :
    moll φ g x = ∫ t, φ.normed volume t * g (x - t) := by
  simp [moll, MeasureTheory.convolution_def]

lemma integrable_bump_mul (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} (hg : Continuous g) (x : ℂ) :
    Integrable (fun t => φ.normed volume t * g (x - t)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact φ.continuous_normed.mul (hg.comp (continuous_const.sub continuous_id))
  · exact φ.hasCompactSupport_normed.mul_right

lemma moll_lip (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) :
    IsLip (moll φ g) L := by
  intro x y
  rw [moll_apply, moll_apply, ← integral_sub (integrable_bump_mul φ hg.continuous x)
    (integrable_bump_mul φ hg.continuous y)]
  calc |∫ t, (φ.normed volume t * g (x - t) - φ.normed volume t * g (y - t))|
      ≤ ∫ t, |φ.normed volume t * g (x - t) - φ.normed volume t * g (y - t)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t, φ.normed volume t * (L * ‖x - y‖) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        · exact (φ.continuous_normed.mul continuous_const).integrable_of_hasCompactSupport
            φ.hasCompactSupport_normed.mul_right
        · refine Filter.Eventually.of_forall fun t => ?_
          simp only
          rw [← mul_sub, abs_mul, abs_of_nonneg (φ.nonneg_normed t)]
          apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
          have := hg (x - t) (y - t)
          rwa [show x - t - (y - t) = x - y by ring] at this
    _ = L * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

lemma moll_contDiff (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (moll φ g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    (hg.locallyIntegrable)

lemma moll_close (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) (x : ℂ) :
    |moll φ g x - g x| ≤ L * φ.rOut := by
  have := φ.dist_normed_convolution_le (μ := volume) (g := g) (x₀ := x) (ε := L * φ.rOut)
    hg.continuous.aestronglyMeasurable (fun y hy => by
      rw [Real.dist_eq]
      calc |g y - g x| ≤ L * ‖y - x‖ := hg y x
        _ ≤ L * φ.rOut := by
          apply mul_le_mul_of_nonneg_left _ hg.nonneg
          rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  rwa [Real.dist_eq] at this

/-- The coefficients of the mollified terrain are averages of those of the terrain. -/
lemma γR_moll (φ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} (hg : Continuous g) (k : ℤ) (v : ℂ) :
    γR r k (moll φ g) v = ∫ t, (φ.normed volume t : ℂ) * γR r k g (v - t) := by
  unfold γR γ
  simp_rw [moll_apply]
  have e1 : ∀ s : ℝ, rot (-(k : ℝ) * s) * ((∫ t, φ.normed volume t * g (v + r * rot s - t) : ℝ) : ℂ) =
      ∫ t, rot (-(k : ℝ) * s) * ((φ.normed volume t : ℂ) * g (v + r * rot s - t)) := by
    intro s
    rw [← integral_complex_ofReal, ← integral_const_mul]
    congr 1; ext t; push_cast; ring
  simp_rw [e1]
  rw [intervalIntegral_integral_swap]
  · congr 1; ext t
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext s
    rw [show v - t + r * rot s = v + r * rot s - t by ring]; ring
  · -- integrability on `(0, 2π] × ℂ`
    set F : ℝ × ℂ → ℂ := fun p => rot (-(k : ℝ) * p.1) * ((φ.normed volume p.2 : ℂ) *
      g (v + r * rot p.1 - p.2))
    have hF : Continuous F := by
      exact ((continuous_rotk k).comp continuous_fst).mul
        ((Complex.continuous_ofReal.comp (φ.continuous_normed.comp continuous_snd)).mul
          (Complex.continuous_ofReal.comp (hg.comp ((continuous_const.add (continuous_const.mul
            (continuous_rot.comp continuous_fst))).sub continuous_snd))))
    have hK : IntegrableOn F (Set.Icc 0 (2 * Real.pi) ×ˢ Metric.closedBall 0 φ.rOut)
        (volume.prod volume) :=
      hF.continuousOn.integrableOn_compact ((isCompact_Icc).prod (isCompact_closedBall _ _))
    have hz : ∀ p ∈ (Set.uIoc 0 (2 * Real.pi) ×ˢ (Set.univ : Set ℂ)) \
        (Set.Icc 0 (2 * Real.pi) ×ˢ Metric.closedBall 0 φ.rOut), F p = 0 := by
      rintro ⟨s, t⟩ ⟨⟨hs, -⟩, hn⟩
      have ht : t ∉ Metric.closedBall (0 : ℂ) φ.rOut := by
        intro ht; apply hn
        rw [Set.uIoc_of_le (by positivity)] at hs
        exact ⟨⟨hs.1.le, hs.2⟩, ht⟩
      have : φ.normed volume t = 0 := by
        rw [← Function.notMem_support, φ.support_normed_eq]
        exact fun h => ht (Metric.ball_subset_closedBall h)
      simp [F, this]
    have := (hK.mono_set (Set.Subset.refl _)).of_forall_sdiff_eq_zero
      ((measurableSet_uIoc).prod MeasurableSet.univ) hz
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at this
    exact this

/-- **Proposition 4.13 (analytic part)**: a Lipschitz terrain whose Fourier coefficients `G₂` and
`G₃` (or `G₂` and `G₄`) vanish on every circle of radius `r > 0` is affine. -/
theorem affine_of_γR {g : ℂ → ℝ} {L : ℝ} (hr : 0 < r) (hg : IsLip g L)
    (h2 : ∀ v, γR r 2 g v = 0) (h34 : (∀ v, γR r 3 g v = 0) ∨ (∀ v, γR r 4 g v = 0)) :
    ∀ x, g x = g 0 + dot ⟨g 1 - g 0, g I - g 0⟩ x := by
  apply affine_of_additive hg.continuous
  -- every mollification is affine
  have hmoll : ∀ φ : ContDiffBump (0 : ℂ), ∀ x y,
      moll φ g (x + y) + moll φ g 0 = moll φ g x + moll φ g y := by
    intro φ
    set gφ := moll φ g
    have hL := moll_lip φ hg
    set f : ℂ → ℂ := fun x => (gφ x : ℂ)
    have hf : ContDiff ℝ 1 f := Complex.ofRealCLM.contDiff.comp (moll_contDiff φ hg.continuous)
    have hfl : LipschitzWith (Real.toNNReal L) f := LipschitzWith.of_dist_le_mul fun x y => by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        Real.coe_toNNReal _ hL.nonneg, dist_eq_norm]
      exact hL x y
    have hb : ∀ x, ‖fderiv ℝ f x‖ ≤ L := fun x => by
      have := norm_fderiv_le_of_lipschitz ℝ hfl (x₀ := x)
      rwa [Real.coe_toNNReal _ hL.nonneg] at this
    have hγ : ∀ k, (∀ v, γR r k g v = 0) → ∀ v, γ r k f v = 0 := fun k hk v => by
      have := γR_moll (r := r) φ hg.continuous k v
      simp only [γR] at this hk
      rw [show γ r k f v = γ r k (fun x => ((moll φ g x : ℝ) : ℂ)) v from rfl, this]
      simp [hk]
    obtain ⟨a, b, hab⟩ := affine_of_γ hr hf hb (fun x => Complex.conj_ofReal _) (hγ 2 h2)
      (h34.imp (hγ 3) (hγ 4))
    intro x y
    have e : ∀ z, (gφ z : ℂ) = a + b * z + conj b * conj z := hab
    have := e (x + y); have := e 0; have := e x; have := e y
    apply Complex.ofReal_injective
    push_cast
    rw [e (x + y), e 0, e x, e y]
    simp only [map_add, map_zero]; ring
  -- pass to the limit
  intro x y
  by_contra hne
  set d := |g (x + y) + g 0 - (g x + g y)|
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hL0 := hg.nonneg
  set δ := d / (8 * (L + 1))
  have hδ : 0 < δ := by positivity
  let φ : ContDiffBump (0 : ℂ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have c := fun z => moll_close φ hg z
  have h := hmoll φ x y
  have e1 := abs_le.1 (c (x + y)); have e2 := abs_le.1 (c 0)
  have e3 := abs_le.1 (c x); have e4 := abs_le.1 (c y)
  have hr' : φ.rOut = δ := rfl
  rw [hr'] at e1 e2 e3 e4
  have hbound : d ≤ 4 * (L * δ) := by
    rw [abs_le']; constructor <;> linarith
  have : 4 * (L * δ) < d := by
    have : 4 * (L * δ) = d * (4 * L / (8 * (L + 1))) := by simp only [δ]; field_simp
    rw [this]
    have : 4 * L / (8 * (L + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  linarith

/-! ### Proposition 4.13 -/

/-- The idealised wobbling function of the table with feet `r e_E` (`e_E` the feet of `F`)
rotating around the vertical axis through `v`. -/
noncomputable def F₀v (F : Feet) (r : ℝ) (g : ℂ → ℝ) (v : ℂ) (θ : ℝ) : ℝ :=
  F.τ * g (v + r * (rot θ * F.A)) + (1 - F.τ) * g (v + r * (rot θ * F.C))
    - F.μ * g (v + r * (rot θ * F.B)) - (1 - F.μ) * g (v + r * (rot θ * F.D))

/-- The `k`-th Fourier coefficient of `θ ↦ g(v + r e^{i(θ + φ₀)})` is `e^{ikφ₀} G_k(v)`. -/
lemma integral_shift {g : ℂ → ℝ} (k : ℕ) (v : ℂ) (e : ℂ) (he : ‖e‖ = 1) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * e)) : ℂ) =
      e ^ k * γR r k g v := by
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : ℝ, e = rot φ₀ := by
    refine ⟨Complex.arg e, ?_⟩
    have := Complex.norm_mul_exp_arg_mul_I e
    rw [he, Complex.ofReal_one, one_mul] at this
    rw [rot]; exact this.symm
  subst hφ₀
  have hrot : ∀ θ, rot θ * rot φ₀ = rot (θ + φ₀) := fun θ => (rot_add' θ φ₀).symm
  simp_rw [hrot]
  -- substitute `ψ = θ + φ₀`
  have hp : Function.Periodic (fun ψ : ℝ => rot (-(k : ℝ) * ψ) * (g (v + r * rot ψ) : ℂ))
      (2 * Real.pi) := fun ψ => by
    simp only
    rw [show -(k : ℝ) * (ψ + 2 * Real.pi) = -(k : ℝ) * ψ + ((-k : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, rot_add', rot_int_two_pi, mul_one, rot_add', rot_two_pi, mul_one]
  have e1 : ∀ θ : ℝ, rot (-(k : ℝ) * θ) * (g (v + r * rot (θ + φ₀)) : ℂ) =
      rot ((k : ℝ) * φ₀) * (rot (-(k : ℝ) * (θ + φ₀)) * (g (v + r * rot (θ + φ₀)) : ℂ)) := by
    intro θ
    rw [← mul_assoc, ← rot_add']; congr 2; ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right (fun ψ => rot (-(k : ℝ) * ψ) * (g (v + r * rot ψ) : ℂ)),
    zero_add, add_comm (2 * Real.pi) φ₀, hp.intervalIntegral_add_eq φ₀ 0, zero_add]
  unfold γR γ
  congr 1
  unfold rot; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- If `F₀^v ≡ 0`, then `m(k) G_k(v) = 0`. -/
lemma m_mul_γR_eq_zero (F : Feet) {g : ℂ → ℝ} (hg : Continuous g) {v : ℂ}
    (h : ∀ θ, F₀v F r g v θ = 0) (k : ℕ) : F.m k * γR r k g v = 0 := by
  have hz : ∫ θ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * θ) * (F₀v F r g v θ : ℂ) = 0 := by
    simp [h]
  have ci : ∀ e : ℂ, IntervalIntegrable (fun θ : ℝ => rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * e)) : ℂ))
      volume 0 (2 * Real.pi) := fun e =>
    ((continuous_rotk k).mul (Complex.continuous_ofReal.comp (hg.comp (continuous_const.add
      (continuous_const.mul (continuous_rot.mul continuous_const)))))).intervalIntegrable _ _
  have e : ∀ θ : ℝ, rot (-(k : ℝ) * θ) * (F₀v F r g v θ : ℂ) =
      (F.τ : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.A)) : ℂ))
      + ((1 - F.τ : ℝ) : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.C)) : ℂ))
      - (F.μ : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.B)) : ℂ))
      - ((1 - F.μ : ℝ) : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.D)) : ℂ)) := by
    intro θ; simp only [F₀v]; push_cast; ring
  simp_rw [e] at hz
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_shift k v _ F.nA, integral_shift k v _ F.nB, integral_shift k v _ F.nC,
    integral_shift k v _ F.nD] at hz
  · simp only [Feet.m]; linear_combination -hz
  all_goals first
    | exact (ci _).const_mul _
    | exact ((ci _).const_mul _).add ((ci _).const_mul _)
    | exact (((ci _).const_mul _).add ((ci _).const_mul _)).sub ((ci _).const_mul _)

/-- **Proposition 4.13 (b), Lipschitz case**: if `F₀^v ≡ 0` for every position `v` of the axis, the
Lipschitz terrain is affine
(for every table except the square, for which `m(3) = m(4) = 0`). -/
theorem affine_of_F₀v (F : Feet) (hr : 0 < r) {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L)
    (h : ∀ v θ, F₀v F r g v θ = 0) (hns : F.m 3 ≠ 0 ∨ F.m 4 ≠ 0) :
    ∀ x, g x = g 0 + dot ⟨g 1 - g 0, g I - g 0⟩ x := by
  have hk : ∀ k : ℕ, F.m k ≠ 0 → ∀ v, γR r k g v = 0 := fun k hm v =>
    (mul_eq_zero.1 (m_mul_γR_eq_zero F hg.continuous (h v) k)).resolve_left hm
  exact affine_of_γR hr hg (by exact_mod_cast hk 2 F.m_two_ne_zero)
    (hns.imp (fun h3 => by exact_mod_cast hk 3 h3) (fun h4 => by exact_mod_cast hk 4 h4))

/-- Converse: for an affine terrain, `F₀^v ≡ 0` for every `v`. -/
theorem F₀v_of_affine (F : Feet) (r : ℝ) (a : ℝ) (b v : ℂ) (θ : ℝ) :
    F₀v F r (fun x => a + dot b x) v θ = 0 := by
  have hX := F.hX
  have h : (F.τ : ℂ) * (r * (rot θ * F.A)) + ((1 - F.τ : ℝ) : ℂ) * (r * (rot θ * F.C)) =
      (F.μ : ℂ) * (r * (rot θ * F.B)) + ((1 - F.μ : ℝ) : ℂ) * (r * (rot θ * F.D)) := by
    linear_combination (r * rot θ) * hX
  unfold F₀v dot
  simp only [Complex.add_re, Complex.add_im]
  generalize (r : ℂ) * (rot θ * F.A) = wA at h ⊢
  generalize (r : ℂ) * (rot θ * F.B) = wB at h ⊢
  generalize (r : ℂ) * (rot θ * F.C) = wC at h ⊢
  generalize (r : ℂ) * (rot θ * F.D) = wD at h ⊢
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hre him
  linear_combination b.re * hre + b.im * him

/-- The only tables with `m(3) = m(4) = 0` are the squares: `e_E⁴` is the same for all feet. -/
lemma square_of_m3_m4 (F : Feet) (h3 : F.m 3 = 0) (h4 : F.m 4 = 0) :
    F.A ^ 4 = F.B ^ 4 ∧ F.A ^ 4 = F.C ^ 4 ∧ F.A ^ 4 = F.D ^ 4 := by
  have h1 := F.m_three_iff.1 h3
  have h2 : F.s₂ = 0 := by rw [F.m_four_iff.1 h4, h1]; ring
  have h3' : F.s₃ = 0 := by rw [← F.conj_s₁, h1]; simp
  have e : ∀ E ∈ ({F.A, F.B, F.C, F.D} : Set ℂ), E ^ 4 = -F.s₄ := by
    intro E hE
    have : E ^ 4 - F.s₁ * E ^ 3 + F.s₂ * E ^ 2 - F.s₃ * E + F.s₄ = 0 := by
      rcases hE with rfl | rfl | rfl | rfl <;> simp only [Feet.s₁, Feet.s₂, Feet.s₃, Feet.s₄] <;> ring
    rw [h1, h2, h3'] at this
    linear_combination this
  rw [e F.A (by simp), e F.B (by simp), e F.C (by simp), e F.D (by simp)]
  exact ⟨rfl, rfl, rfl⟩

/-- `F₀v` is the idealised wobbling function `F₀` of Proposition 4.10 for the table `T` with feet
`r e_E`, on the terrain seen from the axis through `v`. -/
lemma F₀v_eq_F₀ (F : Feet) (T : Table) (hA : T.A = T.r * F.A) (hB : T.B = T.r * F.B)
    (hC : T.C = T.r * F.C) (hD : T.D = T.r * F.D) (g : ℂ → ℝ) (v : ℂ) (θ : ℝ) :
    F₀v F T.r g v θ = Table.F₀ T (fun x => g (v + x)) F.τ F.μ θ := by
  unfold F₀v Table.F₀
  rw [hA, hB, hC, hD]
  simp only [mul_left_comm (rot θ)]

end Axis

end Wobbly
