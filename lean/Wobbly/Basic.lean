import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

/-!
# Wobbly tables — basic definitions and estimates

This file formalises the elementary estimates of §4 of the paper.
The horizontal plane is identified with `ℂ`.

* `dot` is the Euclidean inner product of `ℂ ≅ ℝ²`, `rot θ` the rotation by `θ`.
* `f s = 1 / (1 + √(1 - s))` and `Φ u q = f (‖q‖²) (u · q) q` is the horizontal displacement of
  the foot at `u` when the table has tilt `q` (Lemma 4.1: the foot is at `u - Φ u q`).
* `norm_Φ_le`, `norm_Φ_sub_le`, `psi_le`: the estimates of Lemma 4.2.
* `sq_norm_le_of_abs_dot_le`: Lemma 4.3.
* `solve2`: the explicit solution of the 2 × 2 systems appearing in Proposition 4.4.
-/

noncomputable section

open Complex

namespace Wobbly

/-! ## Euclidean structure on `ℂ ≅ ℝ²` -/

/-- The Euclidean inner product of `ℂ ≅ ℝ²`. -/
def dot (u v : ℂ) : ℝ := u.re * v.re + u.im * v.im

lemma dot_comm (u v : ℂ) : dot u v = dot v u := by
  unfold dot; ring

lemma sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma dot_self (z : ℂ) : dot z z = ‖z‖ ^ 2 := by
  rw [sq_norm_eq]; unfold dot; ring

lemma dot_add_left (u v w : ℂ) : dot (u + v) w = dot u w + dot v w := by
  unfold dot; simp only [add_re, add_im]; ring

lemma dot_add_right (u v w : ℂ) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; simp only [add_re, add_im]; ring

lemma dot_sub_left (u v w : ℂ) : dot (u - v) w = dot u w - dot v w := by
  unfold dot; simp only [sub_re, sub_im]; ring

lemma dot_sub_right (u v w : ℂ) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; simp only [sub_re, sub_im]; ring

lemma dot_real_mul_left (a : ℝ) (u v : ℂ) : dot ((a : ℂ) * u) v = a * dot u v := by
  unfold dot; simp only [mul_re, mul_im, ofReal_re, ofReal_im]; ring

lemma dot_real_mul_right (a : ℝ) (u v : ℂ) : dot u ((a : ℂ) * v) = a * dot u v := by
  unfold dot; simp only [mul_re, mul_im, ofReal_re, ofReal_im]; ring

/-- Cauchy–Schwarz inequality. -/
lemma abs_dot_le (u v : ℂ) : |dot u v| ≤ ‖u‖ * ‖v‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, sq_norm_eq, sq_norm_eq]
  unfold dot
  nlinarith [sq_nonneg (u.re * v.im - u.im * v.re)]

/-- Rotation by the angle `θ`. -/
def rot (θ : ℝ) : ℂ := Complex.exp (θ * I)

lemma norm_rot (θ : ℝ) : ‖rot θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma norm_rot_mul (θ : ℝ) (z : ℂ) : ‖rot θ * z‖ = ‖z‖ := by
  rw [Complex.norm_mul, norm_rot, one_mul]

/-- Rotations preserve the dot product. -/
lemma dot_rot (θ : ℝ) (u v : ℂ) : dot (rot θ * u) (rot θ * v) = dot u v := by
  unfold dot rot
  simp only [mul_re, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (u.re * v.re + u.im * v.im) * Real.cos_sq_add_sin_sq θ

lemma continuous_rot : Continuous rot := by
  unfold rot
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

/-! ## The horizontal displacement `Φ` (Lemmas 4.1 and 4.2) -/

/-- `f s = 1 / (1 + √(1 - s))`. -/
def f (s : ℝ) : ℝ := 1 / (1 + Real.sqrt (1 - s))

lemma f_pos (s : ℝ) : 0 < f s := by
  unfold f; positivity

lemma f_le_one (s : ℝ) : f s ≤ 1 := by
  unfold f
  rw [div_le_one (by positivity)]
  linarith [Real.sqrt_nonneg (1 - s)]

lemma f_mono {s s' : ℝ} (h : s ≤ s') : f s ≤ f s' := by
  unfold f
  apply one_div_le_one_div_of_le (by positivity)
  linarith [Real.sqrt_le_sqrt (show 1 - s' ≤ 1 - s by linarith)]

/-- Lipschitz estimate for `f` on `(-∞, t²]`, with `c = √(1 - t²)`. -/
lemma abs_f_sub_le {s s' t : ℝ} (ht : t ^ 2 < 1) (hs : s ≤ t ^ 2) (hs' : s' ≤ t ^ 2) :
    |f s - f s'| ≤
      |s - s'| / (2 * Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) ^ 2) := by
  set c := Real.sqrt (1 - t ^ 2) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  set A := Real.sqrt (1 - s) with hA
  set B := Real.sqrt (1 - s') with hB
  have hcA : c ≤ A := Real.sqrt_le_sqrt (by linarith)
  have hcB : c ≤ B := Real.sqrt_le_sqrt (by linarith)
  have hA0 : 0 < A := lt_of_lt_of_le hc0 hcA
  have hB0 : 0 < B := lt_of_lt_of_le hc0 hcB
  have hA2 : A ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = 1 - s' := Real.sq_sqrt (by linarith)
  have key : f s - f s' = (s - s') / ((A + B) * (1 + A) * (1 + B)) := by
    have e : s - s' = B ^ 2 - A ^ 2 := by linarith
    have h1 : 1 + A ≠ 0 := by positivity
    have h2 : 1 + B ≠ 0 := by positivity
    have h3 : A + B ≠ 0 := by positivity
    simp only [f]
    rw [← hA, ← hB, e]
    field_simp
    ring
  have hden : 2 * c * (1 + c) ^ 2 ≤ (A + B) * (1 + A) * (1 + B) := by
    have h1 : c + c ≤ A + B := by linarith
    have h2 : 1 + c ≤ 1 + A := by linarith
    have h3 : 1 + c ≤ 1 + B := by linarith
    calc 2 * c * (1 + c) ^ 2 = (c + c) * (1 + c) * (1 + c) := by ring
      _ ≤ (A + B) * (1 + A) * (1 + B) := by gcongr
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (A + B) * (1 + A) * (1 + B))]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

lemma continuous_f : Continuous f := by
  unfold f
  exact continuous_const.div
    (continuous_const.add (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))
    (fun s => by positivity)

lemma continuous_dot : Continuous fun p : ℂ × ℂ => dot p.1 p.2 := by
  unfold dot
  exact ((Complex.continuous_re.comp continuous_fst).mul (Complex.continuous_re.comp continuous_snd)).add
    ((Complex.continuous_im.comp continuous_fst).mul (Complex.continuous_im.comp continuous_snd))

/-- Horizontal displacement of the foot at `u` for the tilt `q` (Lemma 4.1). -/
def Φ (u q : ℂ) : ℂ := ((f (‖q‖ ^ 2) * dot u q : ℝ) : ℂ) * q

lemma continuous_Φ : Continuous fun p : ℂ × ℂ => Φ p.1 p.2 := by
  unfold Φ
  have h1 : Continuous fun p : ℂ × ℂ => f (‖p.2‖ ^ 2) :=
    continuous_f.comp ((continuous_norm.comp continuous_snd).pow 2)
  exact (Complex.continuous_ofReal.comp (h1.mul continuous_dot)).mul continuous_snd

lemma norm_Φ (u q : ℂ) : ‖Φ u q‖ = f (‖q‖ ^ 2) * |dot u q| * ‖q‖ := by
  rw [Φ, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (f_pos _)]

/-- `Φ` is linear in `u`. -/
lemma Φ_sub_left (u v q : ℂ) : Φ u q - Φ v q = Φ (u - v) q := by
  simp only [Φ, dot_sub_left]
  push_cast
  ring

/-- Lemma 4.2, first estimate. -/
lemma norm_Φ_le {u q : ℂ} {r t : ℝ} (hu : ‖u‖ ≤ r) (hq : ‖q‖ ≤ t) :
    ‖Φ u q‖ ≤ f (t ^ 2) * r * t ^ 2 := by
  have ht : 0 ≤ t := le_trans (norm_nonneg _) hq
  have hr : 0 ≤ r := le_trans (norm_nonneg _) hu
  rw [norm_Φ]
  have hf : f (‖q‖ ^ 2) ≤ f (t ^ 2) := f_mono (by gcongr)
  have hd : |dot u q| ≤ r * t := by
    calc |dot u q| ≤ ‖u‖ * ‖q‖ := abs_dot_le u q
      _ ≤ r * t := by gcongr
  calc f (‖q‖ ^ 2) * |dot u q| * ‖q‖ ≤ f (t ^ 2) * (r * t) * t := by
        have := (f_pos (t ^ 2)).le
        gcongr
    _ = f (t ^ 2) * r * t ^ 2 := by ring

/-- The shadow of the table is not larger than the table: `u ↦ u - Φ u q` is 1-Lipschitz. -/
lemma norm_sub_Φ_le {w q : ℂ} (hq : ‖q‖ ≤ 1) : ‖w - Φ w q‖ ≤ ‖w‖ := by
  have hF0 : 0 < f (‖q‖ ^ 2) := f_pos _
  have hF1 : f (‖q‖ ^ 2) ≤ 1 := f_le_one _
  have hq2 : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
  set F := f (‖q‖ ^ 2) with hF
  have hΦ : Φ w q = ((F * dot w q : ℝ) : ℂ) * q := rfl
  have key : ‖w - Φ w q‖ ^ 2 = ‖w‖ ^ 2 - F * (dot w q) ^ 2 * (2 - F * ‖q‖ ^ 2) := by
    rw [hΦ, sq_norm_eq, sq_norm_eq w, sq_norm_eq q]
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, dot]
    ring
  have hpos : 0 ≤ F * (dot w q) ^ 2 * (2 - F * ‖q‖ ^ 2) := by
    have h1 : F * ‖q‖ ^ 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ 2 - F * ‖q‖ ^ 2 := by linarith
    have h3 : 0 ≤ F * (dot w q) ^ 2 := by positivity
    exact mul_nonneg h3 h2
  have h : ‖w - Φ w q‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [key]; linarith
  exact (abs_le_of_sq_le_sq' h (norm_nonneg _)).2

/-- Lemma 4.2, second estimate (Lipschitz estimate in `q`), with `c = √(1 - t²)`. -/
lemma norm_Φ_sub_le {u q q' : ℂ} {r t : ℝ} (hu : ‖u‖ ≤ r) (hq : ‖q‖ ≤ t) (hq' : ‖q'‖ ≤ t)
    (ht : t < 1) :
    ‖Φ u q - Φ u q'‖ ≤
      r * (2 * t / (1 + Real.sqrt (1 - t ^ 2)) +
        t ^ 3 / (Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) ^ 2)) * ‖q - q'‖ := by
  set c := Real.sqrt (1 - t ^ 2) with hc
  have ht0 : 0 ≤ t := le_trans (norm_nonneg _) hq
  have hr : 0 ≤ r := le_trans (norm_nonneg _) hu
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  set F := f (‖q‖ ^ 2) with hF
  set F' := f (‖q'‖ ^ 2) with hF'
  set Dq := dot u q with hDq
  set Dq' := dot u q' with hDq'
  have hFt : F ≤ 1 / (1 + c) := by
    have h := f_mono (show ‖q‖ ^ 2 ≤ t ^ 2 by gcongr)
    have e : f (t ^ 2) = 1 / (1 + c) := rfl
    exact h.trans_eq e
  have hF0 : 0 ≤ F := (f_pos _).le
  -- decomposition
  have hdec : Φ u q - Φ u q' =
      (F : ℂ) * ((Dq : ℂ) * q - (Dq' : ℂ) * q') + ((F - F' : ℝ) : ℂ) * ((Dq' : ℂ) * q') := by
    simp only [Φ, hF, hF', hDq, hDq']
    push_cast
    ring
  -- first term
  have hD'le : |Dq'| ≤ r * t := by
    calc |Dq'| ≤ ‖u‖ * ‖q'‖ := abs_dot_le u q'
      _ ≤ r * t := by gcongr
  have hdiff : |Dq - Dq'| ≤ r * ‖q - q'‖ := by
    rw [hDq, hDq', ← dot_sub_right]
    calc |dot u (q - q')| ≤ ‖u‖ * ‖q - q'‖ := abs_dot_le _ _
      _ ≤ r * ‖q - q'‖ := by gcongr
  have hterm1 : ‖(Dq : ℂ) * q - (Dq' : ℂ) * q'‖ ≤ 2 * r * t * ‖q - q'‖ := by
    have e : (Dq : ℂ) * q - (Dq' : ℂ) * q' = ((Dq - Dq' : ℝ) : ℂ) * q + (Dq' : ℂ) * (q - q') := by
      push_cast; ring
    rw [e]
    calc ‖((Dq - Dq' : ℝ) : ℂ) * q + (Dq' : ℂ) * (q - q')‖
        ≤ ‖((Dq - Dq' : ℝ) : ℂ) * q‖ + ‖(Dq' : ℂ) * (q - q')‖ := norm_add_le _ _
      _ = |Dq - Dq'| * ‖q‖ + |Dq'| * ‖q - q'‖ := by
        rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (r * ‖q - q'‖) * t + (r * t) * ‖q - q'‖ := by gcongr
      _ = 2 * r * t * ‖q - q'‖ := by ring
  -- second term
  have hsq : |‖q‖ ^ 2 - ‖q'‖ ^ 2| ≤ 2 * t * ‖q - q'‖ := by
    have e : ‖q‖ ^ 2 - ‖q'‖ ^ 2 = (‖q‖ - ‖q'‖) * (‖q‖ + ‖q'‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖q‖ + ‖q'‖)]
    have h1 : |‖q‖ - ‖q'‖| ≤ ‖q - q'‖ := abs_norm_sub_norm_le q q'
    calc |‖q‖ - ‖q'‖| * (‖q‖ + ‖q'‖) ≤ ‖q - q'‖ * (t + t) := by gcongr
      _ = 2 * t * ‖q - q'‖ := by ring
  have hFF : |F - F'| ≤ 2 * t * ‖q - q'‖ / (2 * c * (1 + c) ^ 2) := by
    have := abs_f_sub_le ht2 (show ‖q‖ ^ 2 ≤ t ^ 2 by gcongr) (show ‖q'‖ ^ 2 ≤ t ^ 2 by gcongr)
    calc |F - F'| ≤ |‖q‖ ^ 2 - ‖q'‖ ^ 2| / (2 * c * (1 + c) ^ 2) := this
      _ ≤ 2 * t * ‖q - q'‖ / (2 * c * (1 + c) ^ 2) := by gcongr
  have hterm2 : ‖((F - F' : ℝ) : ℂ) * ((Dq' : ℂ) * q')‖ ≤
      t ^ 3 / (c * (1 + c) ^ 2) * r * ‖q - q'‖ := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    calc |F - F'| * (|Dq'| * ‖q'‖)
        ≤ (2 * t * ‖q - q'‖ / (2 * c * (1 + c) ^ 2)) * ((r * t) * t) := by gcongr
      _ = t ^ 3 / (c * (1 + c) ^ 2) * r * ‖q - q'‖ := by
        field_simp
  rw [hdec]
  calc ‖(F : ℂ) * ((Dq : ℂ) * q - (Dq' : ℂ) * q') + ((F - F' : ℝ) : ℂ) * ((Dq' : ℂ) * q')‖
      ≤ ‖(F : ℂ) * ((Dq : ℂ) * q - (Dq' : ℂ) * q')‖ + ‖((F - F' : ℝ) : ℂ) * ((Dq' : ℂ) * q')‖ :=
        norm_add_le _ _
    _ ≤ (1 / (1 + c)) * (2 * r * t * ‖q - q'‖) + t ^ 3 / (c * (1 + c) ^ 2) * r * ‖q - q'‖ := by
        gcongr
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hF0]
        gcongr
    _ = r * (2 * t / (1 + c) + t ^ 3 / (c * (1 + c) ^ 2)) * ‖q - q'‖ := by
        field_simp

/-- The constant of Lemma 4.2: for `0 ≤ t ≤ 1/2`, `ψ(t) ≤ (2/√3) t`. -/
lemma psi_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    2 * t / (1 + Real.sqrt (1 - t ^ 2)) +
        t ^ 3 / (Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) ^ 2) ≤
      2 / Real.sqrt 3 * t := by
  set c := Real.sqrt (1 - t ^ 2) with hc
  set x := Real.sqrt 3 / 2 with hx
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := by positivity
  have hx2 : x ^ 2 = 3 / 4 := by rw [hx, div_pow, hs2]; norm_num
  have hx0 : 0 < x := by positivity
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have hxc : x ≤ c := by
    rw [hc, Real.le_sqrt hx0.le (by linarith)]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le hx0 hxc
  have h1 : 2 * t / (1 + c) ≤ 2 * t / (1 + x) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have h2 : t ^ 3 / (c * (1 + c) ^ 2) ≤ t * (1 / (4 * x * (1 + x) ^ 2)) := by
    rw [show t ^ 3 = t * t ^ 2 by ring, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ ht0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmono : x * (1 + x) ^ 2 ≤ c * (1 + c) ^ 2 := by
      have h1x : 1 + x ≤ 1 + c := by linarith
      have := mul_le_mul hxc (pow_le_pow_left₀ (by positivity) h1x 2) (by positivity) hc0.le
      exact this
    nlinarith [mul_le_mul_of_nonneg_right ht2 (by positivity : (0 : ℝ) ≤ 4 * x * (1 + x) ^ 2)]
  have h3 : 2 / (1 + x) + 1 / (4 * x * (1 + x) ^ 2) = 1 / x := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (4 * x * (1 + x)) * hx2
  have h4 : 2 / Real.sqrt 3 = 1 / x := by rw [hx]; field_simp
  calc 2 * t / (1 + c) + t ^ 3 / (c * (1 + c) ^ 2)
      ≤ 2 * t / (1 + x) + t * (1 / (4 * x * (1 + x) ^ 2)) := add_le_add h1 h2
    _ = (2 / (1 + x) + 1 / (4 * x * (1 + x) ^ 2)) * t := by ring
    _ = 2 / Real.sqrt 3 * t := by rw [h3, h4]

/-! ## Lemma 4.3 and 2 × 2 systems -/

/-- Lemma 4.3: if `w₁, w₂` are unit vectors which are not parallel and `|w_i · q| ≤ s`, then
`‖q‖² ≤ 2 s² / (1 - |w₁ · w₂|)`; this is `K² s²` with `K = 1 / sin (φ/2)`. -/
lemma sq_norm_le_of_abs_dot_le {w₁ w₂ q : ℂ} {s : ℝ} (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1)
    (hγ : |dot w₁ w₂| < 1) (hs₁ : |dot w₁ q| ≤ s) (hs₂ : |dot w₂ q| ≤ s) :
    ‖q‖ ^ 2 ≤ 2 * s ^ 2 / (1 - |dot w₁ w₂|) := by
  set γ := dot w₁ w₂ with hγdef
  set a := dot w₁ q with ha
  set b := dot w₂ q with hb
  have h₁' : w₁.re ^ 2 + w₁.im ^ 2 = 1 := by rw [← sq_norm_eq, h₁]; norm_num
  have h₂' : w₂.re ^ 2 + w₂.im ^ 2 = 1 := by rw [← sq_norm_eq, h₂]; norm_num
  -- the Gram identity in dimension 2
  have gram : (1 - γ ^ 2) * ‖q‖ ^ 2 = a ^ 2 + b ^ 2 - 2 * γ * a * b := by
    rw [sq_norm_eq, hγdef, ha, hb]
    unfold dot
    linear_combination
      (q.re ^ 2 * w₂.re ^ 2 - q.re ^ 2 + 2 * q.re * q.im * w₂.re * w₂.im - q.im ^ 2 * w₂.re ^ 2) * h₁' +
      (-(q.re ^ 2) * w₁.im ^ 2 + 2 * q.re * q.im * w₁.re * w₁.im + q.im ^ 2 * w₁.im ^ 2 - q.im ^ 2) * h₂'
  have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs₁
  have ha2 : a ^ 2 ≤ s ^ 2 := by
    have := abs_le.1 hs₁; nlinarith
  have hb2 : b ^ 2 ≤ s ^ 2 := by
    have := abs_le.1 hs₂; nlinarith
  have hab : -(2 * γ * a * b) ≤ 2 * |γ| * s ^ 2 := by
    have h1 : |2 * γ * a * b| ≤ 2 * |γ| * s ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have : |a| * |b| ≤ s * s := mul_le_mul hs₁ hs₂ (abs_nonneg _) hs0
      nlinarith [abs_nonneg γ]
    linarith [neg_abs_le (2 * γ * a * b)]
  have hg2 : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
  have hpos : 0 < 1 - |γ| := by linarith
  have hpos' : 0 < 1 + |γ| := by linarith [abs_nonneg γ]
  rw [le_div_iff₀ hpos]
  have h : (1 - |γ|) * (1 + |γ|) * ‖q‖ ^ 2 ≤ 2 * s ^ 2 * (1 + |γ|) := by
    have e : (1 - |γ|) * (1 + |γ|) = 1 - γ ^ 2 := by rw [hg2]; ring
    rw [e, gram]
    linarith
  nlinarith

/-- Determinant of the pair `(w₁, w₂)`. -/
def det2 (w₁ w₂ : ℂ) : ℝ := w₁.re * w₂.im - w₁.im * w₂.re

/-- For unit vectors, `det² + (w₁ · w₂)² = 1`. -/
lemma det2_sq_add_dot_sq {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1) :
    det2 w₁ w₂ ^ 2 + dot w₁ w₂ ^ 2 = 1 := by
  have h₁' : w₁.re ^ 2 + w₁.im ^ 2 = 1 := by rw [← sq_norm_eq, h₁]; norm_num
  have h₂' : w₂.re ^ 2 + w₂.im ^ 2 = 1 := by rw [← sq_norm_eq, h₂]; norm_num
  unfold det2 dot
  linear_combination (w₂.re ^ 2 + w₂.im ^ 2) * h₁' + h₂'

lemma det2_ne_zero {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1) (hγ : |dot w₁ w₂| < 1) :
    det2 w₁ w₂ ≠ 0 := by
  intro h0
  have h := det2_sq_add_dot_sq h₁ h₂
  rw [h0] at h
  have h2 : dot w₁ w₂ ^ 2 = 1 := by rw [← h]; ring
  have h1 : dot w₁ w₂ ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (dot w₁ w₂)]
  linarith

lemma det2_rot (θ : ℝ) (w₁ w₂ : ℂ) : det2 (rot θ * w₁) (rot θ * w₂) = det2 w₁ w₂ := by
  unfold det2 rot
  simp only [mul_re, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (w₁.re * w₂.im - w₁.im * w₂.re) * Real.cos_sq_add_sin_sq θ

/-- The unique `v` with `w₁ · v = α` and `w₂ · v = β` (Cramer's rule). -/
def solve2 (w₁ w₂ : ℂ) (α β : ℝ) : ℂ :=
  ⟨(α * w₂.im - β * w₁.im) / det2 w₁ w₂, (β * w₁.re - α * w₂.re) / det2 w₁ w₂⟩

section solve2

variable {w₁ w₂ : ℂ}

lemma dot_solve2_left (h : det2 w₁ w₂ ≠ 0) (α β : ℝ) : dot w₁ (solve2 w₁ w₂ α β) = α := by
  unfold dot solve2
  simp only
  field_simp
  unfold det2
  ring

lemma dot_solve2_right (h : det2 w₁ w₂ ≠ 0) (α β : ℝ) : dot w₂ (solve2 w₁ w₂ α β) = β := by
  unfold dot solve2
  simp only
  field_simp
  unfold det2
  ring

lemma eq_solve2 (h : det2 w₁ w₂ ≠ 0) {v : ℂ} {α β : ℝ} (h1 : dot w₁ v = α) (h2 : dot w₂ v = β) :
    v = solve2 w₁ w₂ α β := by
  apply Complex.ext
  · simp only [solve2]
    rw [eq_div_iff h, ← h1, ← h2]
    unfold dot det2
    ring
  · simp only [solve2]
    rw [eq_div_iff h, ← h1, ← h2]
    unfold dot det2
    ring

lemma solve2_sub (h : det2 w₁ w₂ ≠ 0) (α β α' β' : ℝ) :
    solve2 w₁ w₂ α β - solve2 w₁ w₂ α' β' = solve2 w₁ w₂ (α - α') (β - β') := by
  apply eq_solve2 h
  · rw [dot_sub_right, dot_solve2_left h, dot_solve2_left h]
  · rw [dot_sub_right, dot_solve2_right h, dot_solve2_right h]

/-- Norm bound for the solution of a 2 × 2 system (Lemma 4.3). -/
lemma norm_solve2_le (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1) (hγ : |dot w₁ w₂| < 1) {α β s : ℝ}
    (hα : |α| ≤ s) (hβ : |β| ≤ s) :
    ‖solve2 w₁ w₂ α β‖ ≤ Real.sqrt (2 / (1 - |dot w₁ w₂|)) * s := by
  have hd := det2_ne_zero h₁ h₂ hγ
  have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hα
  have hsq := sq_norm_le_of_abs_dot_le (q := solve2 w₁ w₂ α β) (s := s) h₁ h₂ hγ
    (by rw [dot_solve2_left hd]; exact hα) (by rw [dot_solve2_right hd]; exact hβ)
  have hpos : 0 < 1 - |dot w₁ w₂| := by linarith
  rw [← Real.sqrt_sq (norm_nonneg (solve2 w₁ w₂ α β)), ← Real.sqrt_sq hs0,
    ← Real.sqrt_mul (div_nonneg (by norm_num) hpos.le)]
  apply Real.sqrt_le_sqrt
  calc ‖solve2 w₁ w₂ α β‖ ^ 2 ≤ 2 * s ^ 2 / (1 - |dot w₁ w₂|) := hsq
    _ = 2 / (1 - |dot w₁ w₂|) * s ^ 2 := by ring

lemma solve2_eq (w₁ w₂ : ℂ) (α β : ℝ) : solve2 w₁ w₂ α β =
    (((α * w₂.im - β * w₁.im) / det2 w₁ w₂ : ℝ) : ℂ) +
      (((β * w₁.re - α * w₂.re) / det2 w₁ w₂ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [solve2]

lemma continuous_det2 : Continuous fun p : ℂ × ℂ => det2 p.1 p.2 := by
  unfold det2
  exact ((Complex.continuous_re.comp continuous_fst).mul (Complex.continuous_im.comp continuous_snd)).sub
    ((Complex.continuous_im.comp continuous_fst).mul (Complex.continuous_re.comp continuous_snd))

/-- Continuity of the solution of a 2 × 2 system with respect to the data. -/
lemma continuous_solve2 {X : Type*} [TopologicalSpace X] {v₁ v₂ : X → ℂ} {α β : X → ℝ}
    (h₁ : Continuous v₁) (h₂ : Continuous v₂) (hα : Continuous α) (hβ : Continuous β)
    (hdet : ∀ x, det2 (v₁ x) (v₂ x) ≠ 0) :
    Continuous fun x => solve2 (v₁ x) (v₂ x) (α x) (β x) := by
  have hd : Continuous fun x => det2 (v₁ x) (v₂ x) := continuous_det2.comp (h₁.prodMk h₂)
  simp only [solve2_eq]
  have hre : Continuous fun x => (α x * (v₂ x).im - β x * (v₁ x).im) / det2 (v₁ x) (v₂ x) :=
    ((hα.mul (Complex.continuous_im.comp h₂)).sub (hβ.mul (Complex.continuous_im.comp h₁))).div hd hdet
  have him : Continuous fun x => (β x * (v₁ x).re - α x * (v₂ x).re) / det2 (v₁ x) (v₂ x) :=
    ((hβ.mul (Complex.continuous_re.comp h₁)).sub (hα.mul (Complex.continuous_re.comp h₂))).div hd hdet
  exact (Complex.continuous_ofReal.comp hre).add
    ((Complex.continuous_ofReal.comp him).mul continuous_const)

end solve2

end Wobbly
