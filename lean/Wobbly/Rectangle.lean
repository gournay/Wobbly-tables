import Wobbly.Rational

/-!
# Theorem 5.1: rectangles

For a rectangle (`C = -A`, `D = -B`, feet on the circle of radius `r`), the height `c_AC(θ)` of
the equal hovering position only depends on the direction `e` of the shadow `x_A(θ)` of `A`: with
`h(x) = ½(g(x) - g(-x))`, `x_A = ρ e` where `ρ² + h(ρ e)² = r²`, which determines `ρ` (the rod
argument of [BLPR]), and `c_AC = ½(g(ρ e) + g(-ρ e))`. The same holds for `c_BD` and `x_B`, and
`w_AC = c_AC - c_BD`. Since the directions of `x_A` and `x_B` take all values (an intermediate
value argument, instead of the degree argument of the paper), `c_AC` and `c_BD` have the same
maximum, so `w_AC` takes both signs and vanishes somewhere.
-/

open Complex

namespace Wobbly

/-- `|foot u q|² + (u·q)² = |u|²`: the foot moves on the sphere of radius `|u|`. -/
lemma norm_foot_sq {u q : ℂ} (hq : ‖q‖ ≤ 1) : ‖foot u q‖ ^ 2 + dot u q ^ 2 = ‖u‖ ^ 2 := by
  have key0 : 1 - 2 * f (‖q‖ ^ 2) + f (‖q‖ ^ 2) ^ 2 * ‖q‖ ^ 2 = 0 := by
    have hs1 : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
    have hc2 := Real.sq_sqrt (show 0 ≤ 1 - ‖q‖ ^ 2 by linarith)
    have hc0 := Real.sqrt_nonneg (1 - ‖q‖ ^ 2)
    unfold f
    generalize Real.sqrt (1 - ‖q‖ ^ 2) = c at hc2 hc0 ⊢
    have : ‖q‖ ^ 2 = 1 - c ^ 2 := by linarith
    rw [this]; field_simp; ring
  have e1 := sq_norm_eq (foot u q)
  have e2 := sq_norm_eq u
  have e3 := sq_norm_eq q
  rw [e1, e2]
  unfold foot Φ dot
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [e3] at key0 ⊢
  linear_combination (u.re * q.re + u.im * q.im) ^ 2 * key0

lemma foot_neg (u q : ℂ) : foot (-u) q = -foot u q := by
  unfold foot Φ dot
  apply Complex.ext <;> simp <;> ring

/-- The shadow of a foot stays in the open half-plane of its idealised position. -/
lemma dot_foot_pos {u q : ℂ} (hq : ‖q‖ < 1) (hu : 0 < ‖u‖) : 0 < dot (foot u q) u := by
  have h1 : dot (foot u q) u = ‖u‖ ^ 2 - f (‖q‖ ^ 2) * dot u q ^ 2 := by
    unfold foot Φ
    rw [dot_sub_left, dot_real_mul_left, dot_self, dot_comm q u]; ring
  have hd := abs_dot_le u q
  have hd2 : dot u q ^ 2 ≤ ‖u‖ ^ 2 * ‖q‖ ^ 2 := by
    rw [← mul_pow]; exact sq_le_sq' (abs_le.1 hd).1 (abs_le.1 hd).2
  have hf := f_le_one (‖q‖ ^ 2)
  have hf0 := f_pos (‖q‖ ^ 2)
  have hq2 : ‖q‖ ^ 2 < 1 := by nlinarith [norm_nonneg q]
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  rw [h1]
  have : f (‖q‖ ^ 2) * dot u q ^ 2 ≤ 1 * (‖u‖ ^ 2 * ‖q‖ ^ 2) :=
    mul_le_mul hf hd2 (sq_nonneg _) (by norm_num)
  nlinarith

/-- `h(x) = ½(g(x) - g(-x))`. -/
noncomputable def hodd (g : ℂ → ℝ) (x : ℂ) : ℝ := (g x - g (-x)) / 2

/-- The rod equation `ρ² + h(ρ e)² = r²` has at most one solution `ρ ≥ 0` (`L < 1`). -/
lemma rod_unique {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) (hL : L < 1) {e : ℂ} (he : ‖e‖ = 1)
    {ρ ρ' r : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ')
    (h : ρ ^ 2 + hodd g ((ρ : ℂ) * e) ^ 2 = r ^ 2) (h' : ρ' ^ 2 + hodd g ((ρ' : ℂ) * e) ^ 2 = r ^ 2) :
    ρ = ρ' := by
  have hL0 := hg.nonneg
  have hlip : ∀ x y : ℂ, |hodd g x - hodd g y| ≤ L * ‖x - y‖ := by
    intro x y
    have h1 := hg x y
    have h2 := hg (-x) (-y)
    rw [show -x - -y = -(x - y) by ring, norm_neg] at h2
    unfold hodd
    rw [show (g x - g (-x)) / 2 - (g y - g (-y)) / 2 = ((g x - g y) - (g (-x) - g (-y))) / 2 by ring,
      abs_div, abs_two]
    have := abs_sub (g x - g y) (g (-x) - g (-y))
    linarith
  have hn : ∀ t : ℝ, 0 ≤ t → |hodd g ((t : ℂ) * e)| ≤ L * t := by
    intro t ht
    have := hlip ((t : ℂ) * e) 0
    have h0 : hodd g 0 = 0 := by simp [hodd]
    rw [h0, sub_zero, sub_zero, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht] at this
    exact this
  have hd : |hodd g ((ρ : ℂ) * e) - hodd g ((ρ' : ℂ) * e)| ≤ L * |ρ - ρ'| := by
    have := hlip ((ρ : ℂ) * e) ((ρ' : ℂ) * e)
    rwa [← sub_mul, norm_mul, he, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at this
  have hs : |hodd g ((ρ : ℂ) * e) + hodd g ((ρ' : ℂ) * e)| ≤ L * (ρ + ρ') := by
    have := abs_add_le (hodd g ((ρ : ℂ) * e)) (hodd g ((ρ' : ℂ) * e))
    linarith [hn ρ hρ, hn ρ' hρ']
  -- `(ρ - ρ')(ρ + ρ') = (h' - h)(h' + h)`
  have e1 : (ρ - ρ') * (ρ + ρ') = -((hodd g ((ρ : ℂ) * e) - hodd g ((ρ' : ℂ) * e)) *
      (hodd g ((ρ : ℂ) * e) + hodd g ((ρ' : ℂ) * e))) := by linear_combination h - h'
  have e2 : |ρ - ρ'| * (ρ + ρ') ≤ L * |ρ - ρ'| * (L * (ρ + ρ')) := by
    have := congrArg abs e1
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ρ + ρ')] at this
    rw [this]
    exact mul_le_mul hd hs (abs_nonneg _) (by positivity)
  have e3 : |ρ - ρ'| * (ρ + ρ') * (1 - L ^ 2) ≤ 0 := by nlinarith
  have hL2 : 0 < 1 - L ^ 2 := by nlinarith
  have e4 : |ρ - ρ'| * (ρ + ρ') ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith
  rcases (mul_nonpos_iff.1 e4) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · have := abs_nonneg (ρ - ρ')
    have h0 : |ρ - ρ'| = 0 := le_antisymm h1 this
    linarith [abs_eq_zero.1 h0]

lemma rot_eq_cos_sin (α : ℝ) : rot α = (Real.cos α : ℂ) + (Real.sin α : ℂ) * I := by
  rw [rot, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Decomposition in the orthonormal basis `(e, i e)`. -/
lemma eq_dot_mul_add {e : ℂ} (he : ‖e‖ = 1) (X : ℂ) :
    X = (dot X e : ℂ) * e + (dot X (I * e) : ℂ) * (I * e) := by
  have h := sq_norm_eq e
  rw [he, one_pow] at h
  unfold dot
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · linear_combination X.re * h
  · linear_combination X.im * h

lemma dot_rot_mul (X e : ℂ) (r α : ℝ) :
    dot X (rot α * ((r : ℂ) * e)) = r * (Real.cos α * dot X e + Real.sin α * dot X (I * e)) := by
  rw [rot_eq_cos_sin]
  unfold dot
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma exists_max_of_periodic {F : ℝ → ℝ} (hF : Continuous F) (hp : Function.Periodic F (2 * Real.pi)) :
    ∃ θ₀, ∀ θ, F θ ≤ F θ₀ := by
  obtain ⟨θ₀, -, h⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
    hF.continuousOn
  refine ⟨θ₀, fun θ => ?_⟩
  obtain ⟨y, hy, e⟩ := hp.exists_mem_Ico₀ (by positivity) θ
  rw [e]
  exact h ⟨hy.1, hy.2.le⟩

namespace Table

variable {T : Table} {g : ℂ → ℝ} {L : ℝ}

/-- A rectangle inscribed in the circle of radius `r`. -/
structure IsRectangle (T : Table) : Prop where
  hC : T.C = -T.A
  hD : T.D = -T.B
  nA : ‖T.A‖ = T.r
  nB : ‖T.B‖ = T.r
  hr : 0 < T.r

/-- The height of the equal hovering position with respect to `BD` (in the common tilt). -/
noncomputable def cBD (T : Table) (g : ℂ → ℝ) (L θ : ℝ) : ℝ :=
  g (foot (rot θ * T.B) (tilt T g L θ)) - dot (rot θ * T.B) (tilt T g L θ)

lemma wob_eq_cAC_sub_cBD (θ : ℝ) : wob T g L θ = cAC T g L θ - cBD T g L θ := by
  unfold wob resid cBD; ring

lemma dot_neg_left' (u q : ℂ) : dot (-u) q = -dot u q := by unfold dot; simp; ring

/-- For a rectangle, in the equal hovering position: `u_A · q = h(x_A)` and `c_AC = ½(g(x_A) + g(-x_A))`,
and `|x_A|² + h(x_A)² = r²`. -/
lemma rect_A (hR : T.IsRectangle) (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    cAC T g L θ = (g (foot (rot θ * T.A) (tilt T g L θ)) + g (-foot (rot θ * T.A) (tilt T g L θ))) / 2 ∧
    ‖foot (rot θ * T.A) (tilt T g L θ)‖ ^ 2 + hodd g (foot (rot θ * T.A) (tilt T g L θ)) ^ 2 = T.r ^ 2 := by
  obtain ⟨hA, hC, -, -⟩ := resid_hover hg hs θ
  have hq := norm_tilt_lt_one hg hs θ
  unfold resid at hA hC
  rw [hR.hC, mul_neg, dot_neg_left', foot_neg] at hC
  have hd : dot (rot θ * T.A) (tilt T g L θ) = hodd g (foot (rot θ * T.A) (tilt T g L θ)) := by
    unfold hodd; linarith
  refine ⟨by linarith, ?_⟩
  rw [← hd, norm_foot_sq hq.le, norm_rot_mul, hR.nA]

lemma rect_B (hR : T.IsRectangle) (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    cBD T g L θ = (g (foot (rot θ * T.B) (tilt T g L θ)) + g (-foot (rot θ * T.B) (tilt T g L θ))) / 2 ∧
    ‖foot (rot θ * T.B) (tilt T g L θ)‖ ^ 2 + hodd g (foot (rot θ * T.B) (tilt T g L θ)) ^ 2 = T.r ^ 2 := by
  obtain ⟨-, -, hB, hD⟩ := resid_hover hg hs θ
  have hq := norm_tilt_lt_one hg hs θ
  unfold resid at hB hD
  rw [hR.hD, mul_neg, dot_neg_left', foot_neg] at hD
  have hd : dot (rot θ * T.B) (tilt T g L θ) = hodd g (foot (rot θ * T.B) (tilt T g L θ)) := by
    unfold hodd; linarith
  refine ⟨by unfold cBD; linarith, ?_⟩
  rw [← hd, norm_foot_sq hq.le, norm_rot_mul, hR.nB]

lemma L_lt_one (hs : SmallL T L) : L < 1 := by
  have h2 := sqrt_two_le_K T
  have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  nlinarith [hs.hK, hs.nonneg]

/-- If the shadows of `A` (at `θ₁`) and of `B` (at `θ₂`) have the same direction, then
`c_AC(θ₁) = c_BD(θ₂)`. -/
lemma cAC_eq_cBD (hR : T.IsRectangle) (hg : IsLip g L) (hs : SmallL T L) {θ₁ θ₂ ρ₁ ρ₂ : ℝ} {e : ℂ}
    (he : ‖e‖ = 1) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (h₁ : foot (rot θ₁ * T.A) (tilt T g L θ₁) = (ρ₁ : ℂ) * e)
    (h₂ : foot (rot θ₂ * T.B) (tilt T g L θ₂) = (ρ₂ : ℂ) * e) :
    cAC T g L θ₁ = cBD T g L θ₂ := by
  obtain ⟨c1, n1⟩ := rect_A hR hg hs θ₁
  obtain ⟨c2, n2⟩ := rect_B hR hg hs θ₂
  rw [h₁] at c1 n1
  rw [h₂] at c2 n2
  have nρ : ∀ ρ : ℝ, 0 < ρ → ‖(ρ : ℂ) * e‖ = ρ := fun ρ hρ => by
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  rw [nρ _ hρ₁] at n1
  rw [nρ _ hρ₂] at n2
  have := rod_unique hg (L_lt_one hs) he hρ₁.le hρ₂.le n1 n2
  rw [c1, c2, this]

/-- The direction of the shadow of a foot takes all values. -/
lemma exists_foot_dir (hg : IsLip g L) (hs : SmallL T L) {a : ℂ} (ha : ‖a‖ = T.r) (hr : 0 < T.r)
    {e : ℂ} (he : ‖e‖ = 1) : ∃ θ ρ : ℝ, 0 < ρ ∧ foot (rot θ * a) (tilt T g L θ) = (ρ : ℂ) * e := by
  obtain ⟨φ, hφ⟩ := exists_rot_mul (a := a) (b := (T.r : ℂ) * e)
    (by rw [ha, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr])
  have hu : ∀ θ, rot θ * a = rot (θ - φ) * ((T.r : ℂ) * e) := fun θ => by
    rw [hφ, ← mul_assoc, ← rot_add]; ring_nf
  set X : ℝ → ℂ := fun θ => foot (rot θ * a) (tilt T g L θ) with hX
  have hXc : Continuous X :=
    continuous_foot.comp ((continuous_rot.mul continuous_const).prodMk (continuous_tilt hg hs))
  set D : ℝ → ℝ := fun θ => dot (X θ) (I * e) with hD
  have hDc : Continuous D := continuous_dot.comp (hXc.prodMk continuous_const)
  have hpos : ∀ θ, 0 < T.r * (Real.cos (θ - φ) * dot (X θ) e + Real.sin (θ - φ) * D θ) := by
    intro θ
    have := dot_foot_pos (u := rot θ * a) (norm_tilt_lt_one hg hs θ)
      (by rw [norm_rot_mul, ha]; exact hr)
    have e := dot_rot_mul (X θ) e T.r (θ - φ)
    rw [← hu θ] at e
    rw [← e]; exact this
  have hm : D (φ - Real.pi / 2) < 0 := by
    have := hpos (φ - Real.pi / 2)
    rw [show φ - Real.pi / 2 - φ = -(Real.pi / 2) by ring, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two] at this
    nlinarith
  have hp : 0 < D (φ + Real.pi / 2) := by
    have := hpos (φ + Real.pi / 2)
    rw [show φ + Real.pi / 2 - φ = Real.pi / 2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two] at this
    nlinarith
  obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc (by linarith [Real.pi_pos]) hDc.continuousOn
    ⟨hm.le, hp.le⟩
  have hcos : 0 ≤ Real.cos (θ - φ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 := hpos θ
  rw [hθ0, mul_zero, add_zero] at h1
  have hP : 0 < dot (X θ) e := by
    by_contra hc; push Not at hc
    have : Real.cos (θ - φ) * dot (X θ) e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcos hc
    nlinarith
  refine ⟨θ, dot (X θ) e, hP, ?_⟩
  have := eq_dot_mul_add he (X θ)
  rw [show dot (X θ) (I * e) = D θ from rfl, hθ0] at this
  simpa using this

lemma tilt_periodic (θ : ℝ) : tilt T g L (θ + 2 * Real.pi) = tilt T g L θ := by
  have hQ : T.Q g (θ + 2 * Real.pi) = T.Q g θ := by
    funext q; unfold Q; simp only [rot_add_two_pi]
  unfold tilt; rw [hQ]

/-- **Theorem 5.1**: a rectangle can be stabilised by rotating it, on every terrain satisfying the
smallness assumption (4.3). -/
theorem rectangle_wob_zero (hR : T.IsRectangle) (hg : IsLip g L) (hs : SmallL T L) :
    ∃ θ, wob T g L θ = 0 := by
  have ht := continuous_tilt hg hs
  have hfoot : ∀ a : ℂ, Continuous fun θ : ℝ => foot (rot θ * a) (tilt T g L θ) :=
    fun a => continuous_foot.comp ((continuous_rot.mul continuous_const).prodMk ht)
  have hdot : ∀ a : ℂ, Continuous fun θ : ℝ => dot (rot θ * a) (tilt T g L θ) :=
    fun a => continuous_dot.comp ((continuous_rot.mul continuous_const).prodMk ht)
  have hcA : Continuous (cAC T g L) := (hg.continuous.comp (hfoot T.A)).sub (hdot T.A)
  have hcB : Continuous (cBD T g L) := (hg.continuous.comp (hfoot T.B)).sub (hdot T.B)
  have hpA : Function.Periodic (cAC T g L) (2 * Real.pi) := fun θ => by
    unfold cAC; rw [tilt_periodic, rot_add_two_pi]
  have hpB : Function.Periodic (cBD T g L) (2 * Real.pi) := fun θ => by
    unfold cBD; rw [tilt_periodic, rot_add_two_pi]
  have hne : ∀ (a : ℂ) (θ : ℝ), ‖a‖ = T.r → foot (rot θ * a) (tilt T g L θ) ≠ 0 := by
    intro a θ ha h0
    have := dot_foot_pos (u := rot θ * a) (norm_tilt_lt_one hg hs θ) (by rw [norm_rot_mul, ha]; exact hR.hr)
    rw [h0] at this; simp [dot] at this
  have hunit : ∀ z : ℂ, z ≠ 0 → z = ((‖z‖ : ℝ) : ℂ) * unit z ∧ ‖unit z‖ = 1 := by
    intro z hz
    refine ⟨?_, norm_unit hz⟩
    rw [unit, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz)]; simp
  -- a point where `w ≤ 0`
  obtain ⟨θa, hθa⟩ := exists_max_of_periodic hcA hpA
  obtain ⟨h1, he1⟩ := hunit _ (hne T.A θa hR.nA)
  obtain ⟨θ₂, ρ₂, hρ₂, h₂⟩ := exists_foot_dir hg hs hR.nB hR.hr he1
  have e₂ := cAC_eq_cBD hR hg hs he1 (norm_pos_iff.2 (hne T.A θa hR.nA)) hρ₂ h1 h₂
  have hw₂ : wob T g L θ₂ ≤ 0 := by rw [wob_eq_cAC_sub_cBD, ← e₂]; linarith [hθa θ₂]
  -- a point where `w ≥ 0`
  obtain ⟨θb, hθb⟩ := exists_max_of_periodic hcB hpB
  obtain ⟨h1', he1'⟩ := hunit _ (hne T.B θb hR.nB)
  obtain ⟨θ₁, ρ₁, hρ₁, h₁⟩ := exists_foot_dir hg hs hR.nA hR.hr he1'
  have e₁ := cAC_eq_cBD hR hg hs he1' hρ₁ (norm_pos_iff.2 (hne T.B θb hR.nB)) h₁ h1'
  have hw₁ : 0 ≤ wob T g L θ₁ := by rw [wob_eq_cAC_sub_cBD, e₁]; linarith [hθb θ₁]
  obtain ⟨θ, hθ⟩ := intermediate_value_univ θ₂ θ₁ (continuous_wob hg hs) ⟨hw₂, hw₁⟩
  exact ⟨θ, hθ⟩

/-- **Theorem 5.1**: there is an angle `θ` at which the rectangle stands on its four feet. -/
theorem rectangle_stable (hR : T.IsRectangle) (hg : IsLip g L) (hs : SmallL T L) :
    ∃ θ q c, ‖q‖ < 1 ∧ resid g θ q c T.A = 0 ∧ resid g θ q c T.B = 0 ∧
      resid g θ q c T.C = 0 ∧ resid g θ q c T.D = 0 := by
  obtain ⟨θ, hθ⟩ := rectangle_wob_zero hR hg hs
  exact ⟨θ, (four_feet_iff hg hs θ).2 hθ⟩

end Table

end Wobbly
