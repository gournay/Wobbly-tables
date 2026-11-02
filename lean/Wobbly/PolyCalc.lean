import Wobbly.Taylor
import Wobbly.Orbit
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The terrain `g₁ = Re(z^k) + ½(|z|² - 1) Re(b z^{2k})` (calculus for Theorem 5.7)

`g₁` has the gradient `G₁(z) = conj(k z^{k-1}) + Re(b z^{2k}) z + ½(|z|² - 1) conj(2k b z^{2k-1})`
(along every segment), `|G₁| ≤ k + |b|` on the closed unit disc (for `k = 4, 5`), and `G₁` is
`(k(k-1) + (4k+1)|b|)`-Lipschitz on the closed unit disc; hence the second order Taylor estimate of
Proposition 5.2 holds with `M₁ = k(k-1) + (4k+1)|b|`.
-/

open Complex ComplexConjugate

namespace Wobbly

/-- The second order Taylor estimate, from a Lipschitz gradient and derivatives along segments. -/
theorem taylor_of_lipschitz_grad' {g : ℂ → ℝ} {G : ℂ → ℂ} {M : ℝ}
    (hd : ∀ u w : ℂ, ∀ t : ℝ, ‖u + t • w‖ ≤ 1 →
      HasDerivAt (fun s : ℝ => g (u + s • w)) (dot (G (u + t • w)) w) t)
    (hL : ∀ x y : ℂ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖G x - G y‖ ≤ M * ‖x - y‖)
    (u x : ℂ) (hu : ‖u‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    |g x - g u - dot (G u) (x - u)| ≤ M / 2 * ‖x - u‖ ^ 2 := by
  set v := x - u
  let p : ℝ → ℂ := fun t => u + t • v
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖p t‖ ≤ 1 := by
    rintro t ⟨h0, h1⟩
    have : p t = (1 - t) • u + t • x := by simp only [p, v]; module
    rw [this]
    calc ‖(1 - t) • u + t • x‖ ≤ ‖(1 - t) • u‖ + ‖t • x‖ := norm_add_le _ _
      _ = (1 - t) * ‖u‖ + t * ‖x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
      _ ≤ (1 - t) * 1 + t * 1 := by gcongr
      _ = 1 := by ring
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => g (p t)) (dot (G (p t)) v) t :=
    fun t ht => hd u v t (hp t ht)
  have hpu : ∀ t, 0 ≤ t → ‖p t - u‖ = t * ‖v‖ := fun t ht => by
    simp only [p, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |dot (G (p t)) v - dot (G u) v| ≤ M * ‖v‖ ^ 2 * t := by
    intro t ht
    rw [← dot_sub_left]
    calc _ ≤ ‖G (p t) - G u‖ * ‖v‖ := abs_dot_le _ _
      _ ≤ M * ‖p t - u‖ * ‖v‖ := by gcongr; exact hL _ _ (hp t ht) hu
      _ = M * ‖v‖ ^ 2 * t := by rw [hpu t ht.1]; ring
  have anti : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → AntitoneOn
      (fun t => σ * (g (p t) - t * dot (G u) v) - M * ‖v‖ ^ 2 * (t * t) / 2) (Set.Icc 0 1) := by
    intro σ hσ
    have hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
        (fun t => σ * (g (p t) - t * dot (G u) v) - M * ‖v‖ ^ 2 * (t * t) / 2)
        (σ * (dot (G (p t)) v - dot (G u) v) - M * ‖v‖ ^ 2 * t) t := by
      intro t ht
      have h1 := hderiv t ht
      have h2 := ((hasDerivAt_id t).mul_const (dot (G u) v))
      have h3 := (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (M * ‖v‖ ^ 2)).div_const 2
      exact (((h1.sub h2).const_mul σ).sub h3).congr_deriv (by simp; ring)
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro t ht; exact (hD t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hD t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hb := hbound t (Set.Ioo_subset_Icc_self ht)
      rcases hσ with rfl | rfl
      · have := le_abs_self (dot (G (p t)) v - dot (G u) v); nlinarith
      · have := neg_abs_le (dot (G (p t)) v - dot (G u) v); nlinarith
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e0 : p 0 = u := by simp [p]
  have e1 : p 1 = x := by simp [p, v]
  have a1 := anti 1 (Or.inl rfl) h01 h11 zero_le_one
  have a2 := anti (-1) (Or.inr rfl) h01 h11 zero_le_one
  simp only [e0, e1] at a1 a2
  rw [abs_le]
  constructor <;> nlinarith

/-- The terrain `g₁(z) = Re(z^k) + ½(|z|² - 1) Re(b z^{2k})`. -/
noncomputable def gk (k : ℕ) (b : ℂ) (z : ℂ) : ℝ :=
  (z ^ k).re + (1 / 2) * (Complex.normSq z - 1) * (b * z ^ (2 * k)).re

/-- Its gradient. -/
noncomputable def Gk (k : ℕ) (b : ℂ) (z : ℂ) : ℂ :=
  conj ((k : ℂ) * z ^ (k - 1)) + (((b * z ^ (2 * k)).re : ℝ) : ℂ) * z
    + (((Complex.normSq z - 1) / 2 : ℝ) : ℂ) * conj ((2 * k : ℂ) * b * z ^ (2 * k - 1))

lemma normSq_eq_mul_conj (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj]

lemma re_eq (z : ℂ) : ((z.re : ℝ) : ℂ) = (z + conj z) / 2 := by rw [Complex.re_eq_add_conj]

/-- The complex-valued versions (with `Re` and `|·|²` written with `conj`). -/
lemma gk_eq (k : ℕ) (b z : ℂ) : ((gk k b z : ℝ) : ℂ) =
    (z ^ k + conj z ^ k) / 2 + (1 / 2) * (z * conj z - 1) * ((b * z ^ (2 * k) + conj b * conj z ^ (2 * k)) / 2) := by
  simp only [gk]; push_cast
  rw [re_eq, re_eq, normSq_eq_mul_conj]
  simp only [map_mul, map_pow]

lemma Gk_eq (k : ℕ) (b z : ℂ) : Gk k b z =
    (k : ℂ) * conj z ^ (k - 1) + ((b * z ^ (2 * k) + conj b * conj z ^ (2 * k)) / 2) * z
      + ((z * conj z - 1) / 2) * ((2 * k : ℂ) * conj b * conj z ^ (2 * k - 1)) := by
  simp only [Gk]; push_cast
  rw [re_eq, normSq_eq_mul_conj]
  simp only [map_mul, map_pow, map_natCast, map_ofNat]

lemma hasDerivAt_conj {p : ℝ → ℂ} {w : ℂ} {t : ℝ} (h : HasDerivAt p w t) :
    HasDerivAt (fun s => conj (p s)) (conj w) t := h.star

lemma hasDerivAt_line (u w : ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => u + s • w) w t :=
  (((hasDerivAt_id t).smul_const w).const_add u).congr_deriv (by simp)

/-- The derivative of `g₁` along a segment is given by the gradient `G₁`. -/
theorem hasDerivAt_gk (k : ℕ) (hk : 1 ≤ k) (b u w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gk k b (u + s • w)) (dot (Gk k b (u + t • w)) w) t := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have e1 : n + 1 - 1 = n := rfl
  have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  set p : ℝ → ℂ := fun s => u + s • w
  have hp : HasDerivAt p w t := hasDerivAt_line u w t
  have hpc : HasDerivAt (fun s => conj (p s)) (conj w) t := hasDerivAt_conj hp
  set H : ℝ → ℂ := fun s => (p s ^ (n + 1) + conj (p s) ^ (n + 1)) / 2 + (1 / 2) * (p s * conj (p s) - 1) *
    ((b * p s ^ (2 * (n + 1)) + conj b * conj (p s) ^ (2 * (n + 1))) / 2)
  have hH : HasDerivAt H
      (((n + 1 : ℕ) * p t ^ n * w + (n + 1 : ℕ) * conj (p t) ^ n * conj w) / 2 +
        (1 / 2) * (w * conj (p t) + p t * conj w) *
          ((b * p t ^ (2 * (n + 1)) + conj b * conj (p t) ^ (2 * (n + 1))) / 2) +
        (1 / 2) * (p t * conj (p t) - 1) * ((b * ((2 * (n + 1) : ℕ) * p t ^ (2 * n + 1) * w) +
          conj b * ((2 * (n + 1) : ℕ) * conj (p t) ^ (2 * n + 1) * conj w)) / 2)) t := by
    have a1 := hp.fun_pow (n + 1)
    have a2 := hpc.fun_pow (n + 1)
    have a3 := hp.fun_pow (2 * (n + 1))
    have a4 := hpc.fun_pow (2 * (n + 1))
    have a5 := hp.mul hpc
    simp only [e1, e2] at a1 a2 a3 a4
    exact ((((a1.add a2).div_const 2).add ((((a5.sub_const 1).const_mul (1 / 2 : ℂ)).mul
      (((a3.const_mul b).add (a4.const_mul (conj b))).div_const 2))))).congr_deriv
        (by simp only [Pi.mul_apply, Pi.add_apply]; push_cast; ring)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hH
  have hfun : (fun s : ℝ => gk (n + 1) b (u + s • w)) = fun s => (H s).re := by
    ext s
    have := gk_eq (n + 1) b (p s)
    apply Complex.ofReal_injective
    rw [this, re_eq]
    simp only [H, map_add, map_div₀, map_mul, map_sub, map_one, map_pow, Complex.conj_conj, map_ofNat]
    ring
  rw [hfun]
  convert hre using 1
  · ext s; simp
  simp only [Complex.reCLM_apply]
  apply Complex.ofReal_injective
  rw [dot_eq_complex, re_eq, Gk_eq]
  simp only [p, e1, e2, Complex.real_smul, map_add, map_div₀, map_mul, map_sub, map_one, map_pow,
    Complex.conj_conj, map_ofNat, map_natCast, Complex.conj_ofReal]
  push_cast
  ring

/-- The complex form of the derivative of `G₁` in the direction `w` (for `k = m + 2`). -/
noncomputable def DGk (m : ℕ) (b z w : ℂ) : ℂ :=
  ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * conj z ^ m * conj w
    + ((((2 * m + 4 : ℕ) : ℂ) * b * z ^ (2 * m + 3) * w + ((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3) * conj w) / 2) * z
    + ((b * z ^ (2 * m + 4) + conj b * conj z ^ (2 * m + 4)) / 2) * w
    + ((w * conj z + z * conj w) / 2) * (((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3))
    + ((z * conj z - 1) / 2) * (((2 * m + 4 : ℕ) : ℂ) * ((2 * m + 3 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 2) * conj w)

/-- The derivative of `G₁` along a segment. -/
theorem hasDerivAt_Gk (m : ℕ) (b u w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Gk (m + 2) b (u + s • w)) (DGk m b (u + t • w) w) t := by
  have e1 : m + 2 - 1 = m + 1 := rfl
  have e2 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  have e3 : 2 * (m + 2) = 2 * m + 4 := by ring
  set p : ℝ → ℂ := fun s => u + s • w
  have hp : HasDerivAt p w t := hasDerivAt_line u w t
  have hpc : HasDerivAt (fun s => conj (p s)) (conj w) t := hasDerivAt_conj hp
  have hfun : (fun s : ℝ => Gk (m + 2) b (u + s • w)) = fun s =>
      ((m + 2 : ℕ) : ℂ) * conj (p s) ^ (m + 1) + ((b * p s ^ (2 * m + 4) + conj b * conj (p s) ^ (2 * m + 4)) / 2) * p s
        + ((p s * conj (p s) - 1) / 2) * (((2 * m + 4 : ℕ) : ℂ) * conj b * conj (p s) ^ (2 * m + 3)) := by
    ext s; rw [Gk_eq]; simp only [e1, e3, p]; push_cast; ring
  rw [hfun]
  have a1 := hpc.fun_pow (m + 1)
  have a2 := hp.fun_pow (2 * m + 4)
  have a3 := hpc.fun_pow (2 * m + 4)
  have a4 := hpc.fun_pow (2 * m + 3)
  have a5 := hp.mul hpc
  simp only [Nat.add_sub_cancel] at a1 a2 a3 a4
  have e4 : 2 * m + 4 - 1 = 2 * m + 3 := by omega
  have e5 : 2 * m + 3 - 1 = 2 * m + 2 := by omega
  rw [e4] at a2 a3
  rw [e5] at a4
  exact (((a1.const_mul ((m + 2 : ℕ) : ℂ)).add ((((a2.const_mul b).add (a3.const_mul (conj b))).div_const 2).mul hp)).add
    (((a5.sub_const 1).div_const 2).mul (a4.const_mul (((2 * m + 4 : ℕ) : ℂ) * conj b)))).congr_deriv
      (by simp only [DGk, Pi.mul_apply, Pi.add_apply, p]; push_cast; ring)

lemma norm_re_half_le (z : ℂ) : ‖(z + conj z) / 2‖ ≤ ‖z‖ := by
  rw [← re_eq, Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm z

/-- Bound for the derivative of `G₁`, for `‖z‖ ≤ 1`. -/
theorem norm_DGk_le (m : ℕ) (b z w : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖DGk m b z w‖ ≤ ((m + 2) * (m + 1) * ‖z‖ ^ m + ‖b‖ * ((4 * m + 9) * ‖z‖ ^ (2 * m + 4)
      + (m + 2) * (2 * m + 3) * (1 - ‖z‖ ^ 2) * ‖z‖ ^ (2 * m + 2))) * ‖w‖ := by
  set ρ := ‖z‖
  have hρ : 0 ≤ ρ := norm_nonneg z
  have hzz : z * conj z = ((ρ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcz : ‖conj z‖ = ρ := Complex.norm_conj z
  unfold DGk
  have t1 : ‖((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * conj z ^ m * conj w‖ = (m + 2) * (m + 1) * ρ ^ m * ‖w‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, norm_pow, hcz,
      Complex.norm_conj]; push_cast; ring
  have t2 : ‖((((2 * m + 4 : ℕ) : ℂ) * b * z ^ (2 * m + 3) * w + ((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3) * conj w) / 2) * z‖
      ≤ (2 * m + 4) * ‖b‖ * ρ ^ (2 * m + 4) * ‖w‖ := by
    rw [norm_mul]
    have : ((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3) * conj w =
        conj (((2 * m + 4 : ℕ) : ℂ) * b * z ^ (2 * m + 3) * w) := by
      simp only [map_mul, map_pow, map_natCast]
    rw [this]
    calc _ ≤ ‖((2 * m + 4 : ℕ) : ℂ) * b * z ^ (2 * m + 3) * w‖ * ρ := by gcongr; exact norm_re_half_le _
      _ = _ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow]; push_cast; ring
  have t3 : ‖((b * z ^ (2 * m + 4) + conj b * conj z ^ (2 * m + 4)) / 2) * w‖ ≤ ‖b‖ * ρ ^ (2 * m + 4) * ‖w‖ := by
    rw [norm_mul]
    have : conj b * conj z ^ (2 * m + 4) = conj (b * z ^ (2 * m + 4)) := by
      simp only [map_mul, map_pow]
    rw [this]
    calc _ ≤ ‖b * z ^ (2 * m + 4)‖ * ‖w‖ := by gcongr; exact norm_re_half_le _
      _ = _ := by rw [norm_mul, norm_pow]
  have t4 : ‖((w * conj z + z * conj w) / 2) * (((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3))‖
      ≤ (2 * m + 4) * ‖b‖ * ρ ^ (2 * m + 4) * ‖w‖ := by
    rw [norm_mul]
    have : w * conj z + z * conj w = w * conj z + conj (w * conj z) := by
      simp only [map_mul, Complex.conj_conj]; ring
    rw [this]
    calc _ ≤ ‖w * conj z‖ * ‖((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3)‖ := by
          gcongr; exact norm_re_half_le _
      _ = _ := by
          simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_natCast]; push_cast; ring
  have t5 : ‖((z * conj z - 1) / 2) * (((2 * m + 4 : ℕ) : ℂ) * ((2 * m + 3 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 2) * conj w)‖
      = (m + 2) * (2 * m + 3) * (1 - ρ ^ 2) * ‖b‖ * ρ ^ (2 * m + 2) * ‖w‖ := by
    rw [hzz, norm_mul]
    have h1 : ‖(((ρ ^ 2 : ℝ) : ℂ) - 1) / 2‖ = (1 - ρ ^ 2) / 2 := by
      rw [show (((ρ ^ 2 : ℝ) : ℂ) - 1) / 2 = (((ρ ^ 2 - 1) / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
      ring
    rw [h1]
    simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_natCast]; push_cast; ring
  calc _ ≤ ‖((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * conj z ^ m * conj w‖
        + ‖((((2 * m + 4 : ℕ) : ℂ) * b * z ^ (2 * m + 3) * w + ((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3) * conj w) / 2) * z‖
        + ‖((b * z ^ (2 * m + 4) + conj b * conj z ^ (2 * m + 4)) / 2) * w‖
        + ‖((w * conj z + z * conj w) / 2) * (((2 * m + 4 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 3))‖
        + ‖((z * conj z - 1) / 2) * (((2 * m + 4 : ℕ) : ℂ) * ((2 * m + 3 : ℕ) : ℂ) * conj b * conj z ^ (2 * m + 2) * conj w)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ (m + 2) * (m + 1) * ρ ^ m * ‖w‖ + (2 * m + 4) * ‖b‖ * ρ ^ (2 * m + 4) * ‖w‖
        + ‖b‖ * ρ ^ (2 * m + 4) * ‖w‖ + (2 * m + 4) * ‖b‖ * ρ ^ (2 * m + 4) * ‖w‖
        + (m + 2) * (2 * m + 3) * (1 - ρ ^ 2) * ‖b‖ * ρ ^ (2 * m + 2) * ‖w‖ := by
        rw [t1, t5]; gcongr
    _ = _ := by ring

lemma norm_line_le {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖y + t • (x - y)‖ ≤ 1 := by
  have : y + t • (x - y) = (1 - t) • y + t • x := by module
  rw [this]
  calc ‖(1 - t) • y + t • x‖ ≤ ‖(1 - t) • y‖ + ‖t • x‖ := norm_add_le _ _
    _ = (1 - t) * ‖y‖ + t * ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]), Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * 1 + t * 1 := by gcongr <;> linarith [ht.1, ht.2]
    _ = 1 := by ring

/-- `G₁` is Lipschitz on the closed unit disc (`k = m + 2`), given the polynomial inequality. -/
theorem lipschitz_Gk (m : ℕ) (b : ℂ)
    (hpoly : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (4 * m + 9) * ρ ^ (2 * m + 4) + (m + 2) * (2 * m + 3) * (1 - ρ ^ 2) * ρ ^ (2 * m + 2) ≤ 4 * m + 9)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖Gk (m + 2) b x - Gk (m + 2) b y‖ ≤ ((m + 2) * (m + 1) + (4 * m + 9) * ‖b‖) * ‖x - y‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => Gk (m + 2) b (y + t • (x - y))) (f' := fun t => DGk m b (y + t • (x - y)) (x - y))
    (C := ((m + 2) * (m + 1) + (4 * m + 9) * ‖b‖) * ‖x - y‖) (a := 0) (b := 1)
    (fun t _ => (hasDerivAt_Gk m b y (x - y) t).hasDerivWithinAt)
    (fun t ht => by
      have hz := norm_line_le hx hy (Set.Ico_subset_Icc_self ht)
      refine (norm_DGk_le m b _ _ hz).trans ?_
      set ρ := ‖y + t • (x - y)‖
      have hρ : 0 ≤ ρ := norm_nonneg _
      have h1 : ρ ^ m ≤ 1 := pow_le_one₀ hρ hz
      have h2 := hpoly ρ hρ hz
      have hb := norm_nonneg b
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left h2 hb, mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ) ≤ (m + 2) * (m + 1))])
    1 ⟨zero_le_one, le_rfl⟩
  simpa using key

lemma poly_four (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (4 * (2 : ℕ) + 9 : ℝ) * ρ ^ (2 * 2 + 4) + ((2 : ℕ) + 2) * (2 * (2 : ℕ) + 3) * (1 - ρ ^ 2) * ρ ^ (2 * 2 + 2)
      ≤ 4 * (2 : ℕ) + 9 := by
  push_cast
  have hx : 0 ≤ ρ ^ 2 := sq_nonneg _
  have hx1 : ρ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  set x := ρ ^ 2
  have e : ρ ^ 8 = x ^ 4 := by rw [← pow_mul]
  have e' : ρ ^ 6 = x ^ 3 := by rw [← pow_mul]
  rw [e, e']
  nlinarith [mul_nonneg (sub_nonneg.2 hx1) (pow_nonneg hx 3), mul_nonneg (sub_nonneg.2 hx1) (pow_nonneg hx 2),
    mul_nonneg (sub_nonneg.2 hx1) hx, pow_le_one₀ hx hx1 (n := 3), pow_le_one₀ hx hx1 (n := 4)]

lemma poly_five (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (4 * (3 : ℕ) + 9 : ℝ) * ρ ^ (2 * 3 + 4) + ((3 : ℕ) + 2) * (2 * (3 : ℕ) + 3) * (1 - ρ ^ 2) * ρ ^ (2 * 3 + 2)
      ≤ 4 * (3 : ℕ) + 9 := by
  push_cast
  have hx : 0 ≤ ρ ^ 2 := sq_nonneg _
  have hx1 : ρ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  set x := ρ ^ 2
  have e : ρ ^ 10 = x ^ 5 := by rw [← pow_mul]
  have e' : ρ ^ 8 = x ^ 4 := by rw [← pow_mul]
  rw [e, e']
  nlinarith [mul_nonneg (sub_nonneg.2 hx1) (pow_nonneg hx 4), mul_nonneg (sub_nonneg.2 hx1) (pow_nonneg hx 3),
    mul_nonneg (sub_nonneg.2 hx1) (pow_nonneg hx 2), mul_nonneg (sub_nonneg.2 hx1) hx,
    pow_le_one₀ hx hx1 (n := 4), pow_le_one₀ hx hx1 (n := 5)]

/-- Bound for `G₁` on the closed unit disc, given the polynomial inequality. -/
theorem norm_Gk_le (k : ℕ) (hk : 1 ≤ k) (b z : ℂ) (hz : ‖z‖ ≤ 1)
    (hpoly : ‖z‖ ^ (2 * k + 1) + k * (1 - ‖z‖ ^ 2) * ‖z‖ ^ (2 * k - 1) ≤ 1) :
    ‖Gk k b z‖ ≤ k + ‖b‖ := by
  set ρ := ‖z‖
  have hρ : 0 ≤ ρ := norm_nonneg z
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have e1 : n + 1 - 1 = n := rfl
  have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [e2] at hpoly
  unfold Gk
  rw [e1, e2]
  have t1 : ‖conj (((n + 1 : ℕ) : ℂ) * z ^ n)‖ ≤ (n + 1 : ℕ) := by
    rw [Complex.norm_conj, norm_mul, Complex.norm_natCast, norm_pow]
    have : ρ ^ n ≤ 1 := pow_le_one₀ hρ hz
    push_cast; nlinarith
  have t2 : ‖(((b * z ^ (2 * (n + 1))).re : ℝ) : ℂ) * z‖ ≤ ‖b‖ * ρ ^ (2 * n + 3) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |(b * z ^ (2 * (n + 1))).re| * ρ ≤ ‖b * z ^ (2 * (n + 1))‖ * ρ := by
          gcongr; exact Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_pow]; ring
  have t3 : ‖(((Complex.normSq z - 1) / 2 : ℝ) : ℂ) * conj ((2 * (n + 1 : ℕ) : ℂ) * b * z ^ (2 * n + 1))‖
      = (n + 1) * (1 - ρ ^ 2) * ‖b‖ * ρ ^ (2 * n + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.normSq_eq_norm_sq,
      abs_of_nonpos (by nlinarith), Complex.norm_conj]
    simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
    push_cast; ring
  calc _ ≤ ‖conj (((n + 1 : ℕ) : ℂ) * z ^ n)‖ + ‖(((b * z ^ (2 * (n + 1))).re : ℝ) : ℂ) * z‖
        + ‖(((Complex.normSq z - 1) / 2 : ℝ) : ℂ) * conj ((2 * (n + 1 : ℕ) : ℂ) * b * z ^ (2 * n + 1))‖ :=
        norm_add₃_le
    _ ≤ (n + 1 : ℕ) + ‖b‖ * ρ ^ (2 * n + 3) + (n + 1) * (1 - ρ ^ 2) * ‖b‖ * ρ ^ (2 * n + 1) := by
        rw [t3]; gcongr
    _ ≤ (n + 1 : ℕ) + ‖b‖ := by
        have hb := norm_nonneg b
        have := mul_le_mul_of_nonneg_left hpoly hb
        push_cast at this ⊢
        have e3 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
        rw [e3] at this
        nlinarith

lemma polyG_four (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ρ ^ (2 * 4 + 1) + (4 : ℕ) * (1 - ρ ^ 2) * ρ ^ (2 * 4 - 1) ≤ 1 := by
  norm_num
  have a : ∀ i j : ℕ, i ≤ j → ρ ^ j ≤ ρ ^ i := fun i j h => pow_le_pow_of_le_one h0 h1 h
  have hQ : 0 ≤ 1 + ρ + ρ ^ 2 + ρ ^ 3 + ρ ^ 4 + ρ ^ 5 + ρ ^ 6 - 3 * ρ ^ 7 - 3 * ρ ^ 8 := by
    have := a 4 7 (by norm_num); have := a 5 7 (by norm_num); have := a 6 7 (by norm_num)
    have := a 1 8 (by norm_num); have := a 2 8 (by norm_num); have := a 3 8 (by norm_num)
    have := pow_le_one₀ h0 h1 (n := 8)
    simp only [pow_one] at *
    linarith
  have key : 1 - (ρ ^ 9 + 4 * (1 - ρ ^ 2) * ρ ^ 7) =
      (1 - ρ) * (1 + ρ + ρ ^ 2 + ρ ^ 3 + ρ ^ 4 + ρ ^ 5 + ρ ^ 6 - 3 * ρ ^ 7 - 3 * ρ ^ 8) := by ring
  nlinarith [mul_nonneg (sub_nonneg.2 h1) hQ]

lemma polyG_five (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ρ ^ (2 * 5 + 1) + (5 : ℕ) * (1 - ρ ^ 2) * ρ ^ (2 * 5 - 1) ≤ 1 := by
  norm_num
  have a : ∀ i j : ℕ, i ≤ j → ρ ^ j ≤ ρ ^ i := fun i j h => pow_le_pow_of_le_one h0 h1 h
  have hQ : 0 ≤ 1 + ρ + ρ ^ 2 + ρ ^ 3 + ρ ^ 4 + ρ ^ 5 + ρ ^ 6 + ρ ^ 7 + ρ ^ 8 - 4 * ρ ^ 9
      - 4 * ρ ^ 10 := by
    have := a 5 9 (by norm_num); have := a 6 9 (by norm_num); have := a 7 9 (by norm_num)
    have := a 8 9 (by norm_num); have := a 1 10 (by norm_num); have := a 2 10 (by norm_num)
    have := a 3 10 (by norm_num); have := a 4 10 (by norm_num)
    have := pow_le_one₀ h0 h1 (n := 10)
    simp only [pow_one] at *
    linarith
  have key : 1 - (ρ ^ 11 + 5 * (1 - ρ ^ 2) * ρ ^ 9) = (1 - ρ) * (1 + ρ + ρ ^ 2 + ρ ^ 3 + ρ ^ 4
      + ρ ^ 5 + ρ ^ 6 + ρ ^ 7 + ρ ^ 8 - 4 * ρ ^ 9 - 4 * ρ ^ 10) := by ring
  nlinarith [mul_nonneg (sub_nonneg.2 h1) hQ]

end Wobbly
