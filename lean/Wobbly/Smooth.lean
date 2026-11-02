import Wobbly.Wobble
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Proposition 4.4: regularity of the equal hovering position

If the terrain `g` is `C^k` (`1 ≤ k ≤ ∞`), then the tilt `q_AC` and the height `c_AC` of the equal
hovering position are `C^k` functions of `θ` (`Table.contDiff_tilt`, `Table.contDiff_cAC`).

The proof applies the implicit function theorem (`ContDiffAt.implicitFunction`) to
`F(θ, q) = Q_θ(q) - q` at `(θ₀, q_AC(θ₀))`: `F` is `C^k` on `‖q‖ < 1`, and `∂_q F = D Q_θ - 1` is
invertible because `Q_θ` is a contraction near its fixed point (`‖D Q_θ‖ < 1`). The implicit
function coincides with `q_AC` near `θ₀` by uniqueness of the fixed point.
-/

open Complex Filter Topology
open scoped ContDiff NNReal

namespace Wobbly

variable {n : ℕ∞}

lemma contDiff_rot' : ContDiff ℝ n rot := by
  unfold rot
  exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

lemma contDiff_dot' (u : ℂ) : ContDiff ℝ n fun q : ℂ => dot u q := by
  unfold dot
  exact (contDiff_const.mul Complex.reCLM.contDiff).add (contDiff_const.mul Complex.imCLM.contDiff)

lemma contDiff_dot_pair : ContDiff ℝ n fun p : ℂ × ℂ => dot p.1 p.2 := by
  unfold dot
  exact ((Complex.reCLM.contDiff.comp contDiff_fst).mul (Complex.reCLM.contDiff.comp contDiff_snd)).add
    ((Complex.imCLM.contDiff.comp contDiff_fst).mul (Complex.imCLM.contDiff.comp contDiff_snd))

/-- `q ↦ f(‖q‖²)` is smooth on the open unit disc. -/
lemma contDiffAt_f_norm {q : ℂ} (hq : ‖q‖ < 1) :
    ContDiffAt ℝ n (fun q : ℂ => f (‖q‖ ^ 2)) q := by
  have h1 : ContDiffAt ℝ n (fun q : ℂ => 1 - ‖q‖ ^ 2) q :=
    (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt
  have hpos : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have h2 := h1.sqrt hpos.ne'
  unfold f
  exact contDiffAt_const.div (contDiffAt_const.add h2) (by positivity)

/-- `(u, q) ↦ foot u q` is smooth on `‖q‖ < 1`. -/
lemma contDiffAt_foot {p : ℂ × ℂ} (hq : ‖p.2‖ < 1) :
    ContDiffAt ℝ n (fun p : ℂ × ℂ => foot p.1 p.2) p := by
  unfold foot Φ
  have hf : ContDiffAt ℝ n (fun p : ℂ × ℂ => f (‖p.2‖ ^ 2)) p :=
    (contDiffAt_f_norm hq).comp p contDiff_snd.contDiffAt
  have hr : ContDiffAt ℝ n (fun p : ℂ × ℂ => ((f (‖p.2‖ ^ 2) * dot p.1 p.2 : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (hf.mul contDiff_dot_pair.contDiffAt)
  exact contDiff_fst.contDiffAt.sub (hr.mul contDiff_snd.contDiffAt)

namespace Table

variable {T : Table} {g : ℂ → ℝ} {L : ℝ}

/-- `(θ, q) ↦ g(foot(R_θ a, q))` is `C^k` on `‖q‖ < 1` if `g` is. -/
lemma contDiffAt_g_foot (hgs : ContDiff ℝ n g) (a : ℂ) {p : ℝ × ℂ} (hq : ‖p.2‖ < 1) :
    ContDiffAt ℝ n (fun p : ℝ × ℂ => g (foot (rot p.1 * a) p.2)) p := by
  have hu : ContDiff ℝ n (fun p : ℝ × ℂ => (rot p.1 * a, p.2)) :=
    ((contDiff_rot'.comp contDiff_fst).mul contDiff_const).prodMk contDiff_snd
  have := (contDiffAt_foot (n := n) (p := (rot p.1 * a, p.2)) hq).comp p hu.contDiffAt
  exact hgs.contDiffAt.comp p this

/-- `(θ, q) ↦ Q_θ(q)` is `C^k` on `‖q‖ < 1` if `g` is. -/
lemma contDiffAt_Q (hgs : ContDiff ℝ n g) {p : ℝ × ℂ} (hq : ‖p.2‖ < 1) :
    ContDiffAt ℝ n (fun p : ℝ × ℂ => T.Q g p.1 p.2) p := by
  set w₁ : ℝ × ℂ → ℂ := fun p => rot p.1 * T.e₁
  set w₂ : ℝ × ℂ → ℂ := fun p => rot p.1 * T.e₂
  set α : ℝ × ℂ → ℝ := fun p => (g (foot (rot p.1 * T.A) p.2) - g (foot (rot p.1 * T.C) p.2)) / T.d₁
  set β : ℝ × ℂ → ℝ := fun p => (g (foot (rot p.1 * T.B) p.2) - g (foot (rot p.1 * T.D) p.2)) / T.d₂
  have hw₁ : ContDiff ℝ n w₁ := (contDiff_rot'.comp contDiff_fst).mul contDiff_const
  have hw₂ : ContDiff ℝ n w₂ := (contDiff_rot'.comp contDiff_fst).mul contDiff_const
  have hα : ContDiffAt ℝ n α p :=
    ((contDiffAt_g_foot hgs T.A hq).sub (contDiffAt_g_foot hgs T.C hq)).div_const _
  have hβ : ContDiffAt ℝ n β p :=
    ((contDiffAt_g_foot hgs T.B hq).sub (contDiffAt_g_foot hgs T.D hq)).div_const _
  have re : ∀ {h : ℝ × ℂ → ℂ}, ContDiff ℝ n h → ContDiffAt ℝ n (fun p => (h p).re) p :=
    fun hh => (Complex.reCLM.contDiff.comp hh).contDiffAt
  have im : ∀ {h : ℝ × ℂ → ℂ}, ContDiff ℝ n h → ContDiffAt ℝ n (fun p => (h p).im) p :=
    fun hh => (Complex.imCLM.contDiff.comp hh).contDiffAt
  have hdet : ContDiffAt ℝ n (fun p => det2 (w₁ p) (w₂ p)) p := by
    unfold det2; exact ((re hw₁).mul (im hw₂)).sub ((im hw₁).mul (re hw₂))
  have hd0 : det2 (w₁ p) (w₂ p) ≠ 0 := T.det_rot_ne p.1
  have hx : ContDiffAt ℝ n (fun p => (α p * (w₂ p).im - β p * (w₁ p).im) / det2 (w₁ p) (w₂ p)) p :=
    ((hα.mul (im hw₂)).sub (hβ.mul (im hw₁))).div hdet hd0
  have hy : ContDiffAt ℝ n (fun p => (β p * (w₁ p).re - α p * (w₂ p).re) / det2 (w₁ p) (w₂ p)) p :=
    ((hβ.mul (re hw₁)).sub (hα.mul (re hw₂))).div hdet hd0
  have e : (fun p : ℝ × ℂ => T.Q g p.1 p.2) = fun p =>
      (((α p * (w₂ p).im - β p * (w₁ p).im) / det2 (w₁ p) (w₂ p) : ℝ) : ℂ) +
        (((β p * (w₁ p).re - α p * (w₂ p).re) / det2 (w₁ p) (w₂ p) : ℝ) : ℂ) * I := by
    funext p
    apply Complex.ext <;> simp [Q, solve2, α, β, w₁, w₂]
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p hx).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hy).mul contDiffAt_const)

/-- A real number `t ∈ ]LK, 1[` for which `Q_θ` is still a contraction on the disc of radius `t`. -/
lemma exists_contract_radius (hs : SmallL T L) :
    ∃ t, L * T.K < t ∧ t < 1 ∧ T.K * (2 * L * T.r * ψ t / T.dmin) < 1 := by
  have hl := lam_lt_one hs
  have h1 := LK_lt_one hs
  have hc : ContinuousAt (fun t => T.K * (2 * L * T.r * ψ t / T.dmin)) (L * T.K) := by
    have hpos : 0 < 1 - (L * T.K) ^ 2 := by
      have := mul_nonneg hs.nonneg T.K_nonneg; nlinarith
    have hsq : ContinuousAt (fun t : ℝ => Real.sqrt (1 - t ^ 2)) (L * T.K) :=
      (continuous_const.sub (continuous_pow 2)).sqrt.continuousAt
    have hsq0 : Real.sqrt (1 - (L * T.K) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    unfold ψ
    refine continuousAt_const.mul (((continuousAt_const.mul ?_).div_const _))
    have hd1 : (1 : ℝ) + Real.sqrt (1 - (L * T.K) ^ 2) ≠ 0 := by positivity
    refine ((continuousAt_const.mul continuousAt_id).div (continuousAt_const.add hsq)
      hd1).add ((continuous_pow 3).continuousAt.div (hsq.mul ((continuousAt_const.add hsq).pow 2))
      (mul_ne_zero hsq0 (pow_ne_zero _ hd1)))
  have hev : ∀ᶠ t in 𝓝 (L * T.K), T.K * (2 * L * T.r * ψ t / T.dmin) < 1 :=
    hc.eventually (gt_mem_nhds hl)
  have hev2 : ∀ᶠ t in 𝓝[>] (L * T.K), t < 1 ∧ T.K * (2 * L * T.r * ψ t / T.dmin) < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hev.and (gt_mem_nhds h1)).mono fun t ht => ⟨ht.2, ht.1⟩)
  obtain ⟨t, ⟨h2, h3⟩, h4⟩ := (hev2.and self_mem_nhdsWithin).exists
  exact ⟨t, h4, h2, h3⟩

/-- **Proposition 4.4 (regularity)**: if `g` is `C^k` (`k ≥ 1`), the tilt `q_AC` of the equal
hovering position is a `C^k` function of `θ`. -/
theorem contDiff_tilt (hg : IsLip g L) (hs : SmallL T L) (hn : n ≠ 0) (hgs : ContDiff ℝ n g) :
    ContDiff ℝ n (tilt T g L) := by
  rw [contDiff_iff_contDiffAt]
  intro θ₀
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_contract_radius hs
  set q₀ := tilt T g L θ₀
  have hq₀ : ‖q₀‖ < t := lt_of_le_of_lt (norm_tilt_le hg hs θ₀) ht1
  set Fq : ℝ × ℂ → ℂ := fun p => T.Q g p.1 p.2 - p.2
  set u : ℝ × ℂ := (θ₀, q₀)
  have hn' : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast hn
  have cdf : ContDiffAt ℝ n Fq u :=
    (contDiffAt_Q hgs (lt_trans hq₀ ht2)).sub contDiff_snd.contDiffAt
  -- `∂_q F = D Q_{θ₀} - 1`, and `‖D Q_{θ₀}‖ < 1`
  set D := fderiv ℝ (fun q => T.Q g θ₀ q) q₀
  have hdiffF : DifferentiableAt ℝ Fq u := cdf.differentiableAt (by exact_mod_cast hn')
  have hpart : fderiv ℝ Fq u ∘L ContinuousLinearMap.inr ℝ ℝ ℂ = D - 1 := by
    have h1 : HasFDerivAt (fun q => Fq (θ₀, q)) (fderiv ℝ Fq u ∘L ContinuousLinearMap.inr ℝ ℝ ℂ) q₀ :=
      hdiffF.hasFDerivAt.comp q₀ (hasFDerivAt_prodMk_right θ₀ q₀)
    have hQd : DifferentiableAt ℝ (fun q => T.Q g θ₀ q) q₀ := by
      have : ContDiffAt ℝ n (fun q => T.Q g θ₀ q) q₀ :=
        (contDiffAt_Q (p := (θ₀, q₀)) hgs (lt_trans hq₀ ht2)).comp q₀
          ((contDiffAt_const).prodMk contDiffAt_id)
      exact this.differentiableAt (by exact_mod_cast hn')
    have h2 : HasFDerivAt (fun q => Fq (θ₀, q)) (D - ContinuousLinearMap.id ℝ ℂ) q₀ :=
      hQd.hasFDerivAt.sub (hasFDerivAt_id q₀)
    rw [h1.unique h2]; rfl
  have hDn : ‖D‖ < 1 := by
    set c : ℝ := T.K * (2 * L * T.r * ψ t / T.dmin)
    have hc0 : 0 ≤ c := by
      have := ψ_nonneg (le_trans (norm_nonneg _) hq₀.le)
      have := T.r_nonneg; have := T.dmin_pos; have := T.K_nonneg; have := hg.nonneg
      positivity
    have hlip : LipschitzOnWith (Real.toNNReal c) (fun q => T.Q g θ₀ q) (Metric.ball 0 t) := by
      refine LipschitzOnWith.of_dist_le_mul fun q hq q' hq' => ?_
      rw [Metric.mem_ball, dist_zero_right] at hq hq'
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc0]
      have := norm_Q_sub_le (T := T) hg hg.nonneg θ₀ hq.le hq'.le ht2
      linarith [mul_assoc T.K (2 * L * T.r * ψ t / T.dmin) ‖q - q'‖]
    have := norm_fderiv_le_of_lipschitzOn ℝ
      (Metric.isOpen_ball.mem_nhds (by rwa [Metric.mem_ball, dist_zero_right])) hlip
    rw [Real.coe_toNNReal _ hc0] at this
    exact lt_of_le_of_lt this ht3
  have hinv : (fderiv ℝ Fq u ∘L ContinuousLinearMap.inr ℝ ℝ ℂ).IsInvertible := by
    rw [hpart]
    set U := Units.oneSub D hDn
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ ℂ (-U), ?_⟩
    ext1 x
    simp [U]
  -- the implicit function
  set φ := cdf.implicitFunction hn' hinv
  have hφ0 : φ θ₀ = q₀ := cdf.implicitFunction_apply_self hn' hinv
  have hφc : ContDiffAt ℝ n φ θ₀ := cdf.contDiffAt_implicitFunction hn' hinv
  have hFu : Fq u = 0 := by simp [Fq, u, q₀, Q_tilt hg hs θ₀]
  have hev := cdf.eventually_apply_implicitFunction hn' hinv
  rw [hFu] at hev
  have hcont : ContinuousAt φ θ₀ := hφc.continuousAt
  have hev2 : ∀ᶠ θ in 𝓝 θ₀, ‖φ θ‖ < 1 := by
    have : ∀ᶠ θ in 𝓝 θ₀, φ θ ∈ Metric.ball (0 : ℂ) 1 :=
      hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_zero_right, hφ0]; exact lt_trans hq₀ ht2))
    exact this.mono fun θ h => by rwa [Metric.mem_ball, dist_zero_right] at h
  have heq : tilt T g L =ᶠ[𝓝 θ₀] φ := by
    filter_upwards [hev, hev2] with θ h1 h2
    have hfix : T.Q g θ (φ θ) = φ θ := sub_eq_zero.1 h1
    exact fixed_unique hg hs θ (norm_tilt_lt_one hg hs θ) (Q_tilt hg hs θ) h2 hfix
  exact hφc.congr_of_eventuallyEq heq

/-- **Proposition 4.4 (regularity)**: if `g` is `C^k` (`k ≥ 1`), the height `c_AC` of the equal
hovering position is a `C^k` function of `θ`. -/
theorem contDiff_cAC (hg : IsLip g L) (hs : SmallL T L) (hn : n ≠ 0) (hgs : ContDiff ℝ n g) :
    ContDiff ℝ n (cAC T g L) := by
  have ht := contDiff_tilt hg hs hn hgs
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hp : ContDiff ℝ n fun θ : ℝ => (θ, tilt T g L θ) := contDiff_id.prodMk ht
  have h1 : ContDiffAt ℝ n (fun θ => g (foot (rot θ * T.A) (tilt T g L θ))) θ :=
    ContDiffAt.comp (g := fun p : ℝ × ℂ => g (foot (rot p.1 * T.A) p.2)) θ
      (contDiffAt_g_foot (p := (θ, tilt T g L θ)) hgs T.A (norm_tilt_lt_one hg hs θ)) hp.contDiffAt
  have h2 : ContDiffAt ℝ n (fun θ => dot (rot θ * T.A) (tilt T g L θ)) θ :=
    (contDiff_dot_pair.comp (((contDiff_rot'.mul contDiff_const)).prodMk ht)).contDiffAt
  exact h1.sub h2

end Table

end Wobbly
