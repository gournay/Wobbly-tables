import Wobbly.Degenerate
import Wobbly.PolyCalc
import Wobbly.Hexagon
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Corollary 4.11, Proposition 5.4 and Corollary 5.5

* `exists_stable_of_F₀` (Corollary 4.11): for a cyclic table, if the idealised wobbling function
  `F₀` of `g₁` is not identically `0`, then the table can be stabilised on `ε g₁` for `ε` small.
* `sum_w3_orbit` (Proposition 5.4): for a rational table and a terrain `g₁` which is affine on the
  orbits of the rotations by `2π/n` (this is what `ĝ` supported in `𝒦_n` means), `F₀ ≡ 0` and the
  sum of `w₃` over an orbit vanishes; `exists_stable_of_w3` is the consequence.
* `hexagon_stable` (Corollary 5.5).
-/

open Complex ComplexConjugate Finset

namespace Wobbly

/-! ### Integrals over a period -/

lemma rot_add_two_pi (θ : ℝ) : rot (θ + 2 * Real.pi) = rot θ := by
  rw [rot_add]
  have : rot (2 * Real.pi) = 1 := by
    rw [rot]; push_cast; exact Complex.exp_two_pi_mul_I
  rw [this, mul_one]

lemma exists_rot_mul {a b : ℂ} (h : ‖a‖ = ‖b‖) : ∃ φ : ℝ, b = rot φ * a := by
  refine ⟨Complex.arg b - Complex.arg a, ?_⟩
  have ea := Complex.norm_mul_exp_arg_mul_I a
  have eb := Complex.norm_mul_exp_arg_mul_I b
  have e : Complex.exp (((Complex.arg b - Complex.arg a : ℝ) : ℂ) * I) * Complex.exp (Complex.arg a * I) =
      Complex.exp (Complex.arg b * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  calc b = (‖b‖ : ℂ) * Complex.exp (Complex.arg b * I) := eb.symm
    _ = Complex.exp (((Complex.arg b - Complex.arg a : ℝ) : ℂ) * I) * ((‖a‖ : ℂ) * Complex.exp (Complex.arg a * I)) := by
        rw [h, ← e]; ring
    _ = rot (Complex.arg b - Complex.arg a) * a := by rw [ea, rot]

/-- The integral of `g` on a circle does not depend on the starting point. -/
lemma integral_rot_eq {g : ℂ → ℝ} {a b : ℂ} (h : ‖a‖ = ‖b‖) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, g (rot θ * b) = ∫ θ in (0 : ℝ)..2 * Real.pi, g (rot θ * a) := by
  obtain ⟨φ, rfl⟩ := exists_rot_mul h
  have hp : Function.Periodic (fun θ => g (rot θ * a)) (2 * Real.pi) := fun θ => by
    simp only [rot_add_two_pi]
  simp only [← mul_assoc, ← rot_add]
  rw [intervalIntegral.integral_comp_add_right (fun θ => g (rot θ * a)) φ, zero_add,
    add_comm (2 * Real.pi) φ, hp.intervalIntegral_add_eq φ 0, zero_add]

/-- A continuous `2π`-periodic function with integral `0` over a period which is not identically
`0` takes both signs. -/
lemma exists_pos_of_integral_zero {F : ℝ → ℝ} (hF : Continuous F)
    (hp : Function.Periodic F (2 * Real.pi)) (hI : ∫ θ in (0 : ℝ)..2 * Real.pi, F θ = 0)
    {θ₀ : ℝ} (h₀ : F θ₀ < 0) : ∃ θ, 0 < F θ := by
  by_contra hne
  push Not at hne
  have hpn : Function.Periodic (fun θ => -F θ) (2 * Real.pi) := fun θ => by simp only [hp θ]
  have hI' : ∫ θ in (θ₀ - Real.pi)..(θ₀ - Real.pi) + 2 * Real.pi, -F θ = 0 := by
    rw [hpn.intervalIntegral_add_eq (θ₀ - Real.pi) 0, zero_add, intervalIntegral.integral_neg,
      hI, neg_zero]
  have hpos : 0 < ∫ θ in (θ₀ - Real.pi)..(θ₀ - Real.pi) + 2 * Real.pi, -F θ := by
    apply intervalIntegral.integral_pos (by linarith [Real.pi_pos]) hF.neg.continuousOn
    · intro x _; show 0 ≤ -F x; linarith [hne x]
    · exact ⟨θ₀, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, show 0 < -F θ₀ by linarith⟩
  linarith

lemma exists_pos_neg_of_integral_zero {F : ℝ → ℝ} (hF : Continuous F)
    (hp : Function.Periodic F (2 * Real.pi)) (hI : ∫ θ in (0 : ℝ)..2 * Real.pi, F θ = 0)
    {θ₀ : ℝ} (h₀ : F θ₀ ≠ 0) : (∃ θ, 0 < F θ) ∧ ∃ θ, F θ < 0 := by
  have hn : ∀ {θ₁ : ℝ}, 0 < F θ₁ → ∃ θ, F θ < 0 := fun {θ₁} h₁ => by
    obtain ⟨θ, hθ⟩ := exists_pos_of_integral_zero (F := fun θ => -F θ) hF.neg
      (fun θ => by simp only [hp θ])
      (by rw [intervalIntegral.integral_neg, hI, neg_zero]) (θ₀ := θ₁) (by simpa using h₁)
    exact ⟨θ, by simpa using hθ⟩
  rcases h₀.lt_or_gt with h | h
  · obtain ⟨θ, hθ⟩ := exists_pos_of_integral_zero hF hp hI h
    exact ⟨⟨θ, hθ⟩, hn hθ⟩
  · exact ⟨⟨θ₀, h⟩, hn h⟩

namespace Table

variable {T : Table}

/-- A table is cyclic if its feet are on the circle of radius `r`. -/
structure Cyclic (T : Table) : Prop where
  hA : ‖T.A‖ = T.r
  hB : ‖T.B‖ = T.r
  hC : ‖T.C‖ = T.r
  hD : ‖T.D‖ = T.r

lemma continuous_F₀ {g : ℂ → ℝ} (hg : Continuous g) (τ μ : ℝ) : Continuous (F₀ T g τ μ) := by
  have hr : ∀ a : ℂ, Continuous fun θ : ℝ => g (rot θ * a) :=
    fun a => hg.comp (continuous_rot.mul continuous_const)
  unfold F₀
  exact ((((hr _).const_smul τ).add ((hr _).const_smul (1 - τ))).sub ((hr _).const_smul μ)).sub
    ((hr _).const_smul (1 - μ))

lemma periodic_F₀ (g : ℂ → ℝ) (τ μ : ℝ) : Function.Periodic (F₀ T g τ μ) (2 * Real.pi) := by
  intro θ; simp only [F₀, rot_add_two_pi]

/-- For a cyclic table, `∫ F₀ = 0` over a period (the argument of §2). -/
lemma integral_F₀ (hc : T.Cyclic) {g : ℂ → ℝ} (hg : Continuous g) (τ μ : ℝ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, F₀ T g τ μ θ = 0 := by
  have hr : ∀ a : ℂ, IntervalIntegrable (fun θ : ℝ => g (rot θ * a)) MeasureTheory.volume 0 (2 * Real.pi) :=
    fun a => (hg.comp (continuous_rot.mul continuous_const)).intervalIntegrable _ _
  unfold F₀
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rot_eq (g := g) (hc.hA.trans hc.hB.symm), integral_rot_eq (g := g) (hc.hA.trans hc.hC.symm),
    integral_rot_eq (g := g) (hc.hA.trans hc.hD.symm)]
  · ring
  all_goals first
    | exact ((hr _).const_mul _)
    | exact ((hr _).const_mul _).add ((hr _).const_mul _)
    | exact (((hr _).const_mul _).add ((hr _).const_mul _)).sub ((hr _).const_mul _)

/-- A sufficient condition for the smallness assumption (4.3). -/
lemma smallL_of_le {L : ℝ} (hL : 0 ≤ L) (h1 : L * T.K ≤ 1 / 2) (h2 : L * T.K ≤ T.dmin / (4 * T.r + 1)) :
    SmallL T L := by
  refine ⟨hL, h1, ?_⟩
  have hr := T.r_nonneg
  have hd := T.dmin_pos
  have hLK : 0 ≤ L * T.K := mul_nonneg hL T.K_nonneg
  have h3 : 1 ≤ Real.sqrt 3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsq : (L * T.K) ^ 2 ≤ T.dmin / (2 * (4 * T.r + 1)) := by
    have := mul_le_mul h1 h2 hLK (by norm_num)
    rw [sq]; calc L * T.K * (L * T.K) ≤ 1 / 2 * (T.dmin / (4 * T.r + 1)) := by nlinarith
      _ = _ := by field_simp
  calc 4 / Real.sqrt 3 * (T.r / T.dmin) * (L * T.K) ^ 2 ≤ 4 / 1 * (T.r / T.dmin) *
        (T.dmin / (2 * (4 * T.r + 1))) := by
        gcongr
    _ = 2 * T.r / (4 * T.r + 1) := by field_simp; ring
    _ < 1 := by rw [div_lt_one (by linarith)]; linarith

/-- **Corollary 4.11**: for a cyclic table, if `F₀[g₁] ≢ 0`, then for every `ε` small enough the
table can be stabilised (four feet on the ground) by rotating it on the terrain `ε g₁`. -/
theorem exists_stable_of_F₀ (hc : T.Cyclic) {g₁ : ℂ → ℝ} {L₁ τ μ : ℝ} (hg : IsLip g₁ L₁)
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {θ₀ : ℝ} (h₀ : F₀ T g₁ τ μ θ₀ ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ θ, wob T (fun z => ε * g₁ z) (ε * L₁) θ = 0 := by
  obtain ⟨⟨θ₁, h₁⟩, ⟨θ₂, h₂⟩⟩ := exists_pos_neg_of_integral_zero (continuous_F₀ hg.continuous τ μ)
    (periodic_F₀ g₁ τ μ) (integral_F₀ hc hg.continuous τ μ) h₀
  have hL₁ := hg.nonneg
  have hK := T.K_nonneg
  have hr := T.r_nonneg
  have hd := T.dmin_pos
  set m := min (F₀ T g₁ τ μ θ₁) (-F₀ T g₁ τ μ θ₂)
  have hm : 0 < m := lt_min h₁ (by linarith)
  set C := L₁ * T.K + 1
  have hC : 0 < C := by positivity
  set ε₀ := min (min (1 / (2 * C)) (T.dmin / ((4 * T.r + 1) * C))) (min 1 (m / (4 * C ^ 2 * (L₁ * T.r + 1))))
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  have e1 : ε ≤ 1 / (2 * C) := hεε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : ε ≤ T.dmin / ((4 * T.r + 1) * C) := hεε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : ε ≤ 1 := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε ≤ m / (4 * C ^ 2 * (L₁ * T.r + 1)) := hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLK : ε * L₁ * T.K ≤ ε * C := by
    have : L₁ * T.K ≤ C := by linarith
    nlinarith
  have hLK0 : 0 ≤ ε * L₁ * T.K := by positivity
  have hεC1 : ε * C ≤ 1 / 2 := by rw [le_div_iff₀ (by positivity)] at e1; linarith
  have hεC2 : ε * C ≤ T.dmin / (4 * T.r + 1) := by
    rw [le_div_iff₀ (by positivity)] at e2; rw [le_div_iff₀ (by positivity)]; linarith
  have hs : SmallL T (ε * L₁) := smallL_of_le (by positivity) (by linarith) (by linarith)
  have hgε : IsLip (fun z => ε * g₁ z) (ε * L₁) := fun x y => by
    simp only
    rw [← mul_sub, abs_mul, abs_of_pos hε, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg x y) hε.le
  have hF : ∀ θ, F₀ T (fun z => ε * g₁ z) τ μ θ = ε * F₀ T g₁ τ μ θ := fun θ => by
    simp only [F₀]; ring
  -- the error of Proposition 4.10 is at most `ε m / 2`
  have herr : ∀ θ, |wob T (fun z => ε * g₁ z) (ε * L₁) θ - ε * F₀ T g₁ τ μ θ| ≤ ε * m / 2 := by
    intro θ
    have h := abs_wob_sub_F₀_le hgε hs θ hX hτ0 hτ1 hμ0 hμ1
    rw [hF] at h
    refine h.trans ?_
    have hf := f_le_one ((ε * L₁ * T.K) ^ 2)
    have hf0 := f_pos ((ε * L₁ * T.K) ^ 2)
    have hsq : (ε * L₁ * T.K) ^ 2 ≤ (ε * C) ^ 2 := pow_le_pow_left₀ hLK0 hLK 2
    have h4 : 4 * C ^ 2 * (L₁ * T.r + 1) * ε ≤ m := by
      rw [le_div_iff₀ (by positivity)] at e4; linarith
    calc 2 * (ε * L₁ * (f ((ε * L₁ * T.K) ^ 2) * T.r * (ε * L₁ * T.K) ^ 2))
        ≤ 2 * (ε * L₁ * (1 * T.r * (ε * C) ^ 2)) := by gcongr
      _ = ε * (2 * ε ^ 2 * C ^ 2 * (L₁ * T.r)) := by ring
      _ ≤ ε * (m / 2) := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          have : ε ^ 2 ≤ ε := by nlinarith
          have : 0 ≤ L₁ * T.r := by positivity
          nlinarith
      _ = ε * m / 2 := by ring
  have hpos : 0 < wob T (fun z => ε * g₁ z) (ε * L₁) θ₁ := by
    have := (abs_le.1 (herr θ₁)).1
    have : ε * m ≤ ε * F₀ T g₁ τ μ θ₁ := mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le
    nlinarith
  have hneg : wob T (fun z => ε * g₁ z) (ε * L₁) θ₂ < 0 := by
    have := (abs_le.1 (herr θ₂)).2
    have : ε * m ≤ ε * (-F₀ T g₁ τ μ θ₂) := mul_le_mul_of_nonneg_left (min_le_right _ _) hε.le
    nlinarith
  obtain ⟨θ, hθ⟩ := intermediate_value_univ θ₂ θ₁ (continuous_wob hgε hs) ⟨hneg.le, hpos.le⟩
  exact ⟨θ, hθ⟩

/-! ### Proposition 5.4: rational tables -/

/-- `g` is affine on every orbit of the rotations by `2π/n` on the circle of radius `r`: this is
what "the Fourier modes of `g` on the circle are in `𝒦_n`" means. -/
def AffineOnOrbits (g : ℂ → ℝ) (n : ℕ) (r : ℝ) : Prop :=
  ∀ θ : ℝ, ∃ c : ℝ, ∃ p : ℂ, ∀ i : ZMod n, g (vtx n r θ i) = c + dot (vtx n r θ i) p

/-- If the values of `g` at the four feet are those of an affine function, `F₀ = 0`. -/
lemma F₀_of_affine {g : ℂ → ℝ} {θ c : ℝ} {p : ℂ} {τ μ : ℝ}
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)
    (hA : g (rot θ * T.A) = c + dot (rot θ * T.A) p) (hB : g (rot θ * T.B) = c + dot (rot θ * T.B) p)
    (hC : g (rot θ * T.C) = c + dot (rot θ * T.C) p) (hD : g (rot θ * T.D) = c + dot (rot θ * T.D) p) :
    F₀ T g τ μ θ = 0 := by
  have h : (τ : ℂ) * (rot θ * T.A) + ((1 - τ : ℝ) : ℂ) * (rot θ * T.C) =
      (μ : ℂ) * (rot θ * T.B) + ((1 - μ : ℝ) : ℂ) * (rot θ * T.D) := by
    linear_combination rot θ * hX
  unfold F₀
  rw [hA, hB, hC, hD]
  generalize rot θ * T.A = vA at h ⊢
  generalize rot θ * T.B = vB at h ⊢
  generalize rot θ * T.C = vC at h ⊢
  generalize rot θ * T.D = vD at h ⊢
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hre him
  unfold dot
  linear_combination p.re * hre + p.im * him

/-- If the values of `g` at the four feet are those of an affine function with gradient `p`, the
idealised tilt is `p`. -/
lemma Q_of_affine {g : ℂ → ℝ} {θ c : ℝ} {p : ℂ}
    (hA : g (rot θ * T.A) = c + dot (rot θ * T.A) p) (hB : g (rot θ * T.B) = c + dot (rot θ * T.B) p)
    (hC : g (rot θ * T.C) = c + dot (rot θ * T.C) p) (hD : g (rot θ * T.D) = c + dot (rot θ * T.D) p) :
    T.Q g θ 0 = p := by
  unfold Q
  simp only [foot_zero_tilt]
  symm
  apply eq_solve2 (T.det_rot_ne θ)
  · rw [hA, hC, eq_div_iff T.d₁_pos.ne']
    have := T.rot_A_sub_C θ
    have e : dot (rot θ * T.A) p - dot (rot θ * T.C) p = T.d₁ * dot (rot θ * T.e₁) p := by
      rw [← dot_sub_left, this, dot_real_mul_left]
    linarith
  · rw [hB, hD, eq_div_iff T.d₂_pos.ne']
    have := T.rot_B_sub_D θ
    have e : dot (rot θ * T.B) p - dot (rot θ * T.D) p = T.d₂ * dot (rot θ * T.e₂) p := by
      rw [← dot_sub_left, this, dot_real_mul_left]
    linarith

variable {n : ℕ} [NeZero n] {iA iB iC iD : ZMod n} {τ μ : ℝ}

lemma rot_θj_A (hR : IsRational T n iA iB iC iD τ μ) (θ : ℝ) (j : ZMod n) :
    rot (θj n θ j) * T.A = vtx n T.r θ (iA + j) := by rw [hR.hA]; exact rot_θj_mul θ T.r iA j
lemma rot_θj_B (hR : IsRational T n iA iB iC iD τ μ) (θ : ℝ) (j : ZMod n) :
    rot (θj n θ j) * T.B = vtx n T.r θ (iB + j) := by rw [hR.hB]; exact rot_θj_mul θ T.r iB j
lemma rot_θj_C (hR : IsRational T n iA iB iC iD τ μ) (θ : ℝ) (j : ZMod n) :
    rot (θj n θ j) * T.C = vtx n T.r θ (iC + j) := by rw [hR.hC]; exact rot_θj_mul θ T.r iC j
lemma rot_θj_D (hR : IsRational T n iA iB iC iD τ μ) (θ : ℝ) (j : ZMod n) :
    rot (θj n θ j) * T.D = vtx n T.r θ (iD + j) := by rw [hR.hD]; exact rot_θj_mul θ T.r iD j

omit [NeZero n] in
lemma θj_zero (θ : ℝ) : θj n θ 0 = θ := by simp [θj]

/-- **Proposition 5.4** (first part): `F₀ ≡ 0`. -/
theorem F₀_eq_zero_of_affine (hR : IsRational T n iA iB iC iD τ μ) {g : ℂ → ℝ}
    (hg : AffineOnOrbits g n T.r) (θ : ℝ) : F₀ T g τ μ θ = 0 := by
  obtain ⟨c, p, hp⟩ := hg θ
  have hA := rot_θj_A hR θ 0; have hB := rot_θj_B hR θ 0
  have hC := rot_θj_C hR θ 0; have hD := rot_θj_D hR θ 0
  rw [θj_zero] at hA hB hC hD
  exact F₀_of_affine hR.hX (by rw [hA]; exact hp _) (by rw [hB]; exact hp _) (by rw [hC]; exact hp _)
    (by rw [hD]; exact hp _)

/-- **Proposition 5.4**: for a rational table and a terrain `g₁` which is affine on the orbits,
all the rotated tables of an orbit have the same idealised tilt, and the sum of `w₃` over the
orbit vanishes. -/
theorem sum_w3_orbit (hR : IsRational T n iA iB iC iD τ μ) {g : ℂ → ℝ}
    (hg : AffineOnOrbits g n T.r) (G₁ : ℂ → ℂ) (θ : ℝ) :
    ∑ j : ZMod n, T.w3 G₁ τ μ (θj n θ j) (T.Q g (θj n θ j) 0) = 0 := by
  obtain ⟨c, p, hp⟩ := hg θ
  set G : ℂ → ℝ := fun v => dot (G₁ v) p * dot v p
  have hj : ∀ j : ZMod n, T.w3 G₁ τ μ (θj n θ j) (T.Q g (θj n θ j) 0) =
      -(1 / 2) * (τ * G (vtx n T.r θ (iA + j)) - μ * G (vtx n T.r θ (iB + j))
        + (1 - τ) * G (vtx n T.r θ (iC + j)) - (1 - μ) * G (vtx n T.r θ (iD + j))) := by
    intro j
    rw [Q_of_affine (c := c) (by rw [rot_θj_A hR]; exact hp _) (by rw [rot_θj_B hR]; exact hp _)
      (by rw [rot_θj_C hR]; exact hp _) (by rw [rot_θj_D hR]; exact hp _)]
    unfold Table.w3
    rw [rot_θj_A hR, rot_θj_B hR, rot_θj_C hR, rot_θj_D hR]
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_shift (F := fun i => G (vtx n T.r θ i))]
  ring

/-- The idealised tilt of a function which is `L`-Lipschitz on the disc of radius `r`. -/
lemma norm_Q_zero_le {g : ℂ → ℝ} {L : ℝ}
    (hg : ∀ x y : ℂ, ‖x‖ ≤ T.r → ‖y‖ ≤ T.r → |g x - g y| ≤ L * ‖x - y‖) (θ : ℝ) :
    ‖T.Q g θ 0‖ ≤ T.K * L := by
  have key : ∀ (u v : ℂ) (d : ℝ), ‖u‖ ≤ T.r → ‖v‖ ≤ T.r → d = ‖u - v‖ → 0 < d →
      |(g (foot (rot θ * u) 0) - g (foot (rot θ * v) 0)) / d| ≤ L := by
    intro u v d hu hv hd hd0
    rw [foot_zero_tilt, foot_zero_tilt, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    have hu' : ‖rot θ * u‖ ≤ T.r := by rw [norm_rot_mul]; exact hu
    have hv' : ‖rot θ * v‖ ≤ T.r := by rw [norm_rot_mul]; exact hv
    have := hg _ _ hu' hv'
    rwa [← mul_sub, norm_rot_mul, ← hd] at this
  have h := norm_solve2_le (T.norm_rot_e₁ θ) (T.norm_rot_e₂ θ) (T.γ_rot_lt_one θ)
    (key T.A T.C T.d₁ T.normA T.normC rfl T.d₁_pos)
    (key T.B T.D T.d₂ T.normB T.normD rfl T.d₂_pos)
  rw [T.γ_rot] at h
  exact h

/-- **Proposition 5.4** (consequence): for a rational table (with `r = 1`) and a terrain `g₁`
which is affine on the orbits, with a gradient `G₁` satisfying the Taylor estimate of
Proposition 5.2, if `w₃ ≢ 0` then for every `ε` small enough the table can be stabilised (four
feet on the ground) by rotating it on the terrain `ε g₁`. -/
theorem exists_stable_of_w3 (hR : IsRational T n iA iB iC iD τ μ) (hr : T.r = 1) {g₁ : ℂ → ℝ}
    {G₁ : ℂ → ℂ} {L₁ M₁ : ℝ} (hg : IsLip g₁ L₁) (haff : AffineOnOrbits g₁ n T.r)
    (hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 → |g₁ x - g₁ u - dot (G₁ u) (x - u)| ≤ M₁ / 2 * ‖x - u‖ ^ 2)
    (hM : 0 ≤ M₁) (hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖G₁ u‖ ≤ L₁) {θ₀ : ℝ}
    (h₀ : T.w3 G₁ τ μ θ₀ (T.Q g₁ θ₀ 0) ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ θ, wob T (fun z => ε * g₁ z) (ε * L₁) θ = 0 := by
  set W : ℝ → ℝ := fun θ => T.w3 G₁ τ μ θ (T.Q g₁ θ 0) with hW
  -- `W` takes both signs, by the orbit identity
  have hsum := sum_w3_orbit hR haff G₁ θ₀
  have h0 : θj n θ₀ 0 = θ₀ := θj_zero θ₀
  have hsigns : (∃ θ, 0 < W θ) ∧ ∃ θ, W θ < 0 := by
    rcases h₀.lt_or_gt with h | h
    · refine ⟨?_, ⟨θ₀, h⟩⟩
      by_contra hne; push Not at hne
      have := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) (f := fun j : ZMod n => W (θj n θ₀ j))
        (g := fun _ => (0 : ℝ)) Finset.univ_nonempty (fun j _ => ?_)
      · simp only [Finset.sum_const_zero] at this; exact absurd hsum this.ne
      · exact lt_of_le_of_ne (hne _) fun e => by
          have := Finset.sum_eq_zero_iff_of_nonpos (s := Finset.univ) (f := fun j : ZMod n => W (θj n θ₀ j))
            (fun j _ => hne _)
          have h' := (this.1 hsum) 0 (Finset.mem_univ _)
          simp only [h0] at h'; linarith
    · refine ⟨⟨θ₀, h⟩, ?_⟩
      by_contra hne; push Not at hne
      have := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := fun j : ZMod n => W (θj n θ₀ j))
        (fun j _ => hne _)
      have h' := (this.1 hsum) 0 (Finset.mem_univ _)
      simp only [h0] at h'; linarith
  obtain ⟨⟨θ₁, h₁⟩, ⟨θ₂, h₂⟩⟩ := hsigns
  have hL₁ := hg.nonneg
  have hK := T.K_nonneg
  have hd := T.dmin_pos
  have hr0 := T.r_nonneg
  set m := min (W θ₁) (-W θ₂)
  have hm : 0 < m := lt_min h₁ (by linarith)
  set C := L₁ * T.K + 1
  have hC : 0 < C := by positivity
  set ε₁ := min (1 / (2 * C)) (T.dmin / ((4 * T.r + 1) * C))
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁C : ε₁ * C ≤ 1 / 2 := by
    have := min_le_left (1 / (2 * C)) (T.dmin / ((4 * T.r + 1) * C))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hε₁C' : ε₁ * C ≤ T.dmin / (4 * T.r + 1) := by
    have := min_le_right (1 / (2 * C)) (T.dmin / ((4 * T.r + 1) * C))
    rw [le_div_iff₀ (by positivity)] at this; rw [le_div_iff₀ (by positivity)]; linarith
  set R₁ := Rem T.K T.dmin L₁ M₁ 0 (T.K * L₁) 0 ε₁
  set B := max 0 (R₁ / ε₁ ^ 5)
  have hB : 0 ≤ B := le_max_left _ _
  set ε₀ := min ε₁ (min 1 (m / (2 * (B + 1))))
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  have e1 : ε ≤ ε₁ := hεε.trans (min_le_left _ _)
  have e2 : ε ≤ 1 := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : ε ≤ m / (2 * (B + 1)) := hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLK : ε * L₁ * T.K ≤ ε₁ * C := by
    have : L₁ * T.K ≤ C := by linarith
    have : ε * (L₁ * T.K) ≤ ε₁ * C := mul_le_mul e1 this (by positivity) hε₁.le
    linarith
  have hs : SmallL T (ε * L₁ + ε ^ 3 * 0) := by
    rw [mul_zero, add_zero]
    exact smallL_of_le (by positivity) (by linarith) (by linarith)
  have hgε : IsLip (fun z => ε * g₁ z) (ε * L₁ + ε ^ 3 * 0) := fun x y => by
    simp only [mul_zero, add_zero]
    rw [← mul_sub, abs_mul, abs_of_pos hε, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg x y) hε.le
  have hP : ∀ θ, ‖T.Q g₁ θ 0‖ ≤ T.K * L₁ := norm_Q_zero_le (fun x y _ _ => hg x y)
  have hP₃ : ∀ θ, ‖T.Q (fun _ => (0 : ℝ)) θ 0‖ ≤ 0 := fun θ => by
    have := norm_Q_zero_le (T := T) (g := fun _ => (0 : ℝ)) (L := 0) (fun x y _ _ => by simp) θ
    rwa [mul_zero] at this
  have hRem : Rem T.K T.dmin L₁ M₁ 0 (T.K * L₁) 0 ε ≤ ε ^ 3 * (m / 2) := by
    have h := Rem_le_scale hK hd hL₁ hM le_rfl (mul_nonneg hK hL₁) le_rfl hε e1
      (by nlinarith)
    refine h.trans ?_
    have hR₁ : R₁ ≤ B * ε₁ ^ 5 := by
      have : R₁ / ε₁ ^ 5 ≤ B := le_max_right _ _
      rwa [div_le_iff₀ (by positivity)] at this
    have hq : 0 ≤ (ε / ε₁) ^ 5 := by positivity
    calc (ε / ε₁) ^ 5 * R₁ ≤ (ε / ε₁) ^ 5 * (B * ε₁ ^ 5) := mul_le_mul_of_nonneg_left hR₁ hq
      _ = ε ^ 3 * (ε ^ 2 * B) := by field_simp
      _ ≤ ε ^ 3 * (m / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h2 : ε ^ 2 ≤ ε := by nlinarith
          have h3 : ε * (2 * (B + 1)) ≤ m := by rw [le_div_iff₀ (by positivity)] at e3; exact e3
          nlinarith
  have hmain : ∀ θ, |wob T (fun z => ε * g₁ z) (ε * L₁) θ - ε ^ 3 * W θ| ≤ ε ^ 3 * (m / 2) := by
    intro θ
    have h := abs_wob_sub_third_order_le (T := T) (g₁ := g₁) (g₃ := fun _ => (0 : ℝ)) (G₁ := G₁)
      hr hε.le hgε hs (fun x _ => by ring) hT hM hG (fun x y _ _ => by simp) hP hP₃ hR.hX hR.hτ0 hR.hτ1
      hR.hμ0 hR.hμ1 θ
    have hF₁ : F₀ T g₁ τ μ θ = 0 := F₀_eq_zero_of_affine hR haff θ
    have hF₃ : F₀ T (fun _ => (0 : ℝ)) τ μ θ = 0 := by simp [F₀]
    simp only [hF₁, hF₃, mul_zero, add_zero, sub_zero] at h
    exact h.trans hRem
  have hε3 : 0 < ε ^ 3 := by positivity
  have hpos : 0 < wob T (fun z => ε * g₁ z) (ε * L₁) θ₁ := by
    have := (abs_le.1 (hmain θ₁)).1
    have : ε ^ 3 * m ≤ ε ^ 3 * W θ₁ := mul_le_mul_of_nonneg_left (min_le_left _ _) hε3.le
    nlinarith
  have hneg : wob T (fun z => ε * g₁ z) (ε * L₁) θ₂ < 0 := by
    have := (abs_le.1 (hmain θ₂)).2
    have : ε ^ 3 * m ≤ ε ^ 3 * (-W θ₂) := mul_le_mul_of_nonneg_left (min_le_right _ _) hε3.le
    nlinarith
  have hs' : SmallL T (ε * L₁) := by simpa using hs
  have hg' : IsLip (fun z => ε * g₁ z) (ε * L₁) := by simpa using hgε
  obtain ⟨θ, hθ⟩ := intermediate_value_univ θ₂ θ₁ (continuous_wob hg' hs') ⟨hneg.le, hpos.le⟩
  exact ⟨θ, hθ⟩

/-! ### Corollary 5.5: the hexagonal table -/

/-- The kernel of the circulant operator of the hexagonal table: the solutions are the affine
functions on the hexagon (modes `0, ±1`). -/
lemma hex_circ_affine (a : ZMod 6 → ℝ)
    (E0 : 1 / 3 * a 0 - 2 / 3 * a 1 + (1 - 1 / 3) * a 2 - (1 - 2 / 3) * a 3 = 0)
    (E1 : 1 / 3 * a 1 - 2 / 3 * a 2 + (1 - 1 / 3) * a 3 - (1 - 2 / 3) * a 4 = 0)
    (E2 : 1 / 3 * a 2 - 2 / 3 * a 3 + (1 - 1 / 3) * a 4 - (1 - 2 / 3) * a 5 = 0)
    (i : ZMod 6) :
    a i = (∑ k, a k) / 6 + dot (ω 6 ^ i.val) (∑ k, ((a k / 3 : ℝ) : ℂ) * ω 6 ^ k.val) := by
  have s3 := sqrt3_sq
  have key : ∀ m : ℕ, m < 6 → a m = (∑ k, a k) / 6 + dot (ω 6 ^ m) (∑ k, ((a k / 3 : ℝ) : ℂ) * ω 6 ^ k.val) := by
    intro m hm
    rw [sum_zmod6, sum_zmod6_complex]
    simp only [show (0 : ZMod 6).val = 0 from rfl, show (1 : ZMod 6).val = 1 from rfl,
      show (2 : ZMod 6).val = 2 from rfl, show (3 : ZMod 6).val = 3 from rfl,
      show (4 : ZMod 6).val = 4 from rfl, show (5 : ZMod 6).val = 5 from rfl]
    interval_cases m <;>
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one, ω6_pow_two, ω6_pow_three,
      ω6_pow_four, ω6_pow_five] <;>
    simp only [ω6_eq, dot, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im, Complex.neg_re, Complex.neg_im] <;>
    ring_nf <;> (try rw [s3]) <;> linarith
  have := key i.val (ZMod.val_lt i)
  rwa [ZMod.natCast_zmod_val] at this

lemma hexTable_vtx (θ : ℝ) (i : ZMod 6) : vtx 6 hexTable.r θ i = rot θ * ω 6 ^ i.val := by
  simp [vtx, hexTable]

/-- For the hexagonal table, `F₀ ≡ 0` means that `g` is affine on the orbits (`ĝ` is supported in
`𝒦 = 𝒦₆`). -/
theorem hex_affine_of_F₀ {g : ℂ → ℝ} (hF : ∀ θ, F₀ hexTable g (1 / 3) (2 / 3) θ = 0) :
    AffineOnOrbits g 6 hexTable.r := by
  intro θ
  set a : ZMod 6 → ℝ := fun i => g (vtx 6 hexTable.r θ i)
  have hE : ∀ j : ZMod 6, 1 / 3 * a (0 + j) - 2 / 3 * a (1 + j) + (1 - 1 / 3) * a (2 + j)
      - (1 - 2 / 3) * a (3 + j) = 0 := by
    intro j
    have := hF (θj 6 θ j)
    unfold F₀ at this
    rw [rot_θj_A hex_rational, rot_θj_B hex_rational, rot_θj_C hex_rational,
      rot_θj_D hex_rational] at this
    simp only [a]; linarith
  have E0 : 1 / 3 * a 0 - 2 / 3 * a 1 + (1 - 1 / 3) * a 2 - (1 - 2 / 3) * a 3 = 0 := hE 0
  have E1 : 1 / 3 * a 1 - 2 / 3 * a 2 + (1 - 1 / 3) * a 3 - (1 - 2 / 3) * a 4 = 0 := hE 1
  have E2 : 1 / 3 * a 2 - 2 / 3 * a 3 + (1 - 1 / 3) * a 4 - (1 - 2 / 3) * a 5 = 0 := hE 2
  refine ⟨(∑ k, a k) / 6, rot θ * ∑ k, ((a k / 3 : ℝ) : ℂ) * ω 6 ^ k.val, fun i => ?_⟩
  have h := hex_circ_affine a E0 E1 E2 i
  rw [hexTable_vtx, dot_rot, ← h]
  simp only [a, hexTable_vtx]

lemma norm_ω6 : ‖ω 6‖ = 1 := by simpa using norm_ω_pow 6 1

lemma hex_cyclic : hexTable.Cyclic where
  hA := by simp [hexTable]
  hB := by simp [hexTable, norm_ω6]
  hC := by simp [hexTable, norm_ω6]
  hD := by simp [hexTable, norm_ω6]

/-- **Corollary 5.5**: for the hexagonal table and a terrain `g₁` (Lipschitz, with a gradient `G₁`
satisfying the Taylor estimate of Proposition 5.2), if `F₀ ≢ 0`, or if `F₀ ≡ 0` and `w₃ ≢ 0`,
then for every `ε` small enough the table can be stabilised by rotating it on `ε g₁`. -/
theorem hexagon_stable {g₁ : ℂ → ℝ} {G₁ : ℂ → ℂ} {L₁ M₁ : ℝ} (hg : IsLip g₁ L₁)
    (hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 → |g₁ x - g₁ u - dot (G₁ u) (x - u)| ≤ M₁ / 2 * ‖x - u‖ ^ 2)
    (hM : 0 ≤ M₁) (hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖G₁ u‖ ≤ L₁)
    (h : (∃ θ₀, F₀ hexTable g₁ (1 / 3) (2 / 3) θ₀ ≠ 0) ∨
      ((∀ θ, F₀ hexTable g₁ (1 / 3) (2 / 3) θ = 0) ∧
        ∃ θ₀, hexTable.w3 G₁ (1 / 3) (2 / 3) θ₀ (hexTable.Q g₁ θ₀ 0) ≠ 0)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ θ, wob hexTable (fun z => ε * g₁ z) (ε * L₁) θ = 0 := by
  rcases h with ⟨θ₀, h₀⟩ | ⟨hF, θ₀, h₀⟩
  · exact exists_stable_of_F₀ hex_cyclic hg hex_rational.hX hex_rational.hτ0 hex_rational.hτ1
      hex_rational.hμ0 hex_rational.hμ1 h₀
  · exact exists_stable_of_w3 hex_rational rfl hg (hex_affine_of_F₀ hF) hT hM hG h₀

end Table

end Wobbly
