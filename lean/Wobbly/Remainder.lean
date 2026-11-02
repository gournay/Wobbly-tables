import Wobbly.Wobble

/-!
# The third order term with an explicit remainder (Proposition 5.2 of the paper)

The table has `r = 1`, the terrain is `g = ε g₁ + ε³ g₃` on the closed unit disc (and is
`L`-Lipschitz on `ℂ`, with `L = ε L₁ + ε³ L₃`). The function `g₁` has a gradient `G₁` which satisfies
a second order Taylor estimate with constant `M₁` on the disc (see `taylor_of_lipschitz_grad` for the
fact that this follows from `G₁` being `M₁`-Lipschitz), and `g₃` is `L₃`-Lipschitz on the disc.

The idealised tilts are `q₀ = Q_θ[g₁](0)` and `q₃ = Q_θ[g₃](0)` (the map `Q` of Proposition 4.4 at
tilt `0`, where the feet are at their idealised positions).
-/

open Complex

namespace Wobbly

lemma Φ_zero (u : ℂ) : Φ u 0 = 0 := by simp [Φ]

lemma foot_zero_tilt (u : ℂ) : foot u 0 = u := by simp [foot, Φ_zero]

lemma f_zero : f 0 = 1 / 2 := by
  unfold f; norm_num

lemma half_le_f {s : ℝ} (hs : 0 ≤ s) : 1 / 2 ≤ f s := f_zero ▸ f_mono hs

section solve2

variable {w₁ w₂ : ℂ}

lemma solve2_add (h : det2 w₁ w₂ ≠ 0) (α β α' β' : ℝ) :
    solve2 w₁ w₂ (α + α') (β + β') = solve2 w₁ w₂ α β + solve2 w₁ w₂ α' β' := by
  symm
  apply eq_solve2 h
  · rw [dot_add_right, dot_solve2_left h, dot_solve2_left h]
  · rw [dot_add_right, dot_solve2_right h, dot_solve2_right h]

lemma solve2_smul (h : det2 w₁ w₂ ≠ 0) (a α β : ℝ) :
    solve2 w₁ w₂ (a * α) (a * β) = (a : ℂ) * solve2 w₁ w₂ α β := by
  symm
  apply eq_solve2 h
  · rw [dot_real_mul_right, dot_solve2_left h]
  · rw [dot_real_mul_right, dot_solve2_right h]

end solve2

/-- The remainder `R(ε)` of Proposition 5.2. -/
noncomputable def Rem (K dmin L₁ M₁ L₃ P P₃ ε : ℝ) : ℝ :=
  let L := ε * L₁ + ε ^ 3 * L₃
  let t₀ := L * K
  let t₁ := min t₀ (ε * P + ε ^ 3 * P₃ + 2 * K * L / dmin * (f (t₀ ^ 2) * t₀ ^ 2))
  let Φ₁ := f (t₁ ^ 2) * t₁ ^ 2
  let δ := ε ^ 3 * P₃ + 2 * K * L / dmin * Φ₁
  ε * M₁ * Φ₁ ^ 2 + 2 * ε * L₁ * ((f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 + 1 / 2 * (t₁ + ε * P) * δ) +
    2 * ε ^ 3 * L₃ * Φ₁

namespace Table

variable {T : Table}

/-- The third order term `w₃(θ) = -½ Σ_E c_E (∇g₁(u_E)·q₀)(u_E·q₀)` for a gradient `G₁` and a
tilt `q₀`. -/
noncomputable def w3 (T : Table) (G₁ : ℂ → ℂ) (τ μ θ : ℝ) (q₀ : ℂ) : ℝ :=
  -(1 / 2) * (τ * (dot (G₁ (rot θ * T.A)) q₀ * dot (rot θ * T.A) q₀)
    - μ * (dot (G₁ (rot θ * T.B)) q₀ * dot (rot θ * T.B) q₀)
    + (1 - τ) * (dot (G₁ (rot θ * T.C)) q₀ * dot (rot θ * T.C) q₀)
    - (1 - μ) * (dot (G₁ (rot θ * T.D)) q₀ * dot (rot θ * T.D) q₀))

/-- `Q_θ(q) - Q_θ(0)` is controlled by the displacements of the feet. -/
lemma norm_Q_sub_Q_zero_le {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) (θ : ℝ) (q : ℂ) {m : ℝ}
    (hA : ‖Φ (rot θ * T.A) q‖ ≤ m) (hB : ‖Φ (rot θ * T.B) q‖ ≤ m)
    (hC : ‖Φ (rot θ * T.C) q‖ ≤ m) (hD : ‖Φ (rot θ * T.D) q‖ ≤ m) :
    ‖T.Q g θ q - T.Q g θ 0‖ ≤ T.K * (2 * L * m / T.dmin) := by
  have hL := hg.nonneg
  have hd := T.det_rot_ne θ
  have hm : 0 ≤ m := le_trans (norm_nonneg _) hA
  have key : ∀ (a b : ℂ) (d : ℝ), ‖Φ (rot θ * a) q‖ ≤ m → ‖Φ (rot θ * b) q‖ ≤ m → 0 < d →
      T.dmin ≤ d →
      |(g (foot (rot θ * a) q) - g (foot (rot θ * b) q)) / d -
          (g (foot (rot θ * a) 0) - g (foot (rot θ * b) 0)) / d| ≤ 2 * L * m / T.dmin := by
    intro a b d ha hb hd0 hdmin
    rw [foot_zero_tilt, foot_zero_tilt]
    have e : (g (foot (rot θ * a) q) - g (foot (rot θ * b) q)) / d -
        (g (rot θ * a) - g (rot θ * b)) / d =
        ((g (foot (rot θ * a) q) - g (rot θ * a)) - (g (foot (rot θ * b) q) - g (rot θ * b))) / d := by
      ring
    have hfa : ‖foot (rot θ * a) q - rot θ * a‖ = ‖Φ (rot θ * a) q‖ := by
      rw [foot, sub_sub_cancel_left, norm_neg]
    have hfb : ‖foot (rot θ * b) q - rot θ * b‖ = ‖Φ (rot θ * b) q‖ := by
      rw [foot, sub_sub_cancel_left, norm_neg]
    rw [e, abs_div, abs_of_pos hd0]
    have hnum : |(g (foot (rot θ * a) q) - g (rot θ * a)) - (g (foot (rot θ * b) q) - g (rot θ * b))|
        ≤ 2 * L * m := by
      calc _ ≤ |g (foot (rot θ * a) q) - g (rot θ * a)| + |g (foot (rot θ * b) q) - g (rot θ * b)| :=
            abs_sub _ _
        _ ≤ L * ‖foot (rot θ * a) q - rot θ * a‖ + L * ‖foot (rot θ * b) q - rot θ * b‖ :=
            add_le_add (hg _ _) (hg _ _)
        _ ≤ L * m + L * m := by
            rw [hfa, hfb]; gcongr
        _ = 2 * L * m := by ring
    calc _ ≤ 2 * L * m / d := by gcongr
      _ ≤ 2 * L * m / T.dmin := div_le_div_of_nonneg_left (by positivity) T.dmin_pos hdmin
  unfold Q
  rw [solve2_sub hd]
  have := norm_solve2_le (T.norm_rot_e₁ θ) (T.norm_rot_e₂ θ) (T.γ_rot_lt_one θ)
    (key T.A T.C T.d₁ hA hC T.d₁_pos T.dmin_le_d₁) (key T.B T.D T.d₂ hB hD T.d₂_pos T.dmin_le_d₂)
  rwa [T.γ_rot] at this

/-- At tilt `0`, `Q_θ` only depends on the values of the terrain at the idealised positions of
the feet, and is linear in the terrain. -/
lemma Q_zero_eq {g g₁ g₃ : ℂ → ℝ} {ε : ℝ} (hr : T.r = 1)
    (hg : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * g₁ x + ε ^ 3 * g₃ x) (θ : ℝ) :
    T.Q g θ 0 = (ε : ℂ) * T.Q g₁ θ 0 + ((ε ^ 3 : ℝ) : ℂ) * T.Q g₃ θ 0 := by
  have hd := T.det_rot_ne θ
  have hn : ∀ a : ℂ, ‖a‖ ≤ T.r → ‖rot θ * a‖ ≤ 1 := fun a ha => by rw [norm_rot_mul, ← hr]; exact ha
  unfold Q
  simp only [foot_zero_tilt]
  rw [hg _ (hn _ T.normA), hg _ (hn _ T.normB), hg _ (hn _ T.normC), hg _ (hn _ T.normD),
    ← solve2_smul hd, ← solve2_smul hd, ← solve2_add hd]
  congr 1 <;> ring

variable {g g₁ g₃ : ℂ → ℝ} {G₁ : ℂ → ℂ} {ε L₁ M₁ L₃ P P₃ τ μ : ℝ}

/-- One foot: the error made by replacing `g(x_E)` by its third order expansion. -/
lemma foot_error {u q q₀ : ℂ} (hu : ‖u‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hε : 0 ≤ ε)
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * g₁ x + ε ^ 3 * g₃ x)
    (hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 → |g₁ x - g₁ u - dot (G₁ u) (x - u)| ≤ M₁ / 2 * ‖x - u‖ ^ 2)
    (hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖G₁ u‖ ≤ L₁)
    (h3 : ∀ x y : ℂ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → |g₃ x - g₃ y| ≤ L₃ * ‖x - y‖)
    (hM : 0 ≤ M₁) {Φm Δ : ℝ} (hΦ : ‖Φ u q‖ ≤ Φm)
    (hΔ : ‖Φ u q - (((ε ^ 2 / 2) * dot u q₀ : ℝ) : ℂ) * q₀‖ ≤ Δ) :
    |g (foot u q) - ε * g₁ u - ε ^ 3 * g₃ u +
        ε * dot (G₁ u) ((((ε ^ 2 / 2) * dot u q₀ : ℝ) : ℂ) * q₀)| ≤
      ε * L₁ * Δ + ε * (M₁ / 2 * Φm ^ 2) + ε ^ 3 * (L₃ * Φm) := by
  have hx : ‖foot u q‖ ≤ 1 := by
    unfold foot; exact (norm_sub_Φ_le hq).trans hu
  have hxu : foot u q - u = -Φ u q := by unfold foot; ring
  set v := (((ε ^ 2 / 2) * dot u q₀ : ℝ) : ℂ) * q₀
  rw [hgd _ hx]
  have e : ε * g₁ (foot u q) + ε ^ 3 * g₃ (foot u q) - ε * g₁ u - ε ^ 3 * g₃ u + ε * dot (G₁ u) v =
      ε * (g₁ (foot u q) - g₁ u - dot (G₁ u) (foot u q - u))
        - ε * dot (G₁ u) (Φ u q - v) + ε ^ 3 * (g₃ (foot u q) - g₃ u) := by
    rw [hxu, dot_sub_right]
    have : dot (G₁ u) (-Φ u q) = -dot (G₁ u) (Φ u q) := by simp [dot]; ring
    rw [this]; ring
  rw [e]
  have h1 := hT u (foot u q) hu hx
  rw [hxu, norm_neg] at h1
  have h2 : |dot (G₁ u) (Φ u q - v)| ≤ L₁ * Δ :=
    (abs_dot_le _ _).trans (mul_le_mul (hG u hu) hΔ (norm_nonneg _) ((norm_nonneg _).trans (hG u hu)))
  have h3' : |g₃ (foot u q) - g₃ u| ≤ L₃ * Φm := by
    have := h3 _ _ hx hu
    rw [hxu, norm_neg] at this
    have hL3 : 0 ≤ L₃ := by
      have := h3 1 0 (by simp) (by simp); simp at this; linarith [abs_nonneg (g₃ 1 - g₃ 0)]
    exact this.trans (by gcongr)
  have h1' : |g₁ (foot u q) - g₁ u - dot (G₁ u) (foot u q - u)| ≤ M₁ / 2 * Φm ^ 2 := by
    rw [hxu]
    exact h1.trans (by gcongr)
  have hε3 : 0 ≤ ε ^ 3 := by positivity
  calc _ ≤ |ε * (g₁ (foot u q) - g₁ u - dot (G₁ u) (foot u q - u))| + |ε * dot (G₁ u) (Φ u q - v)|
        + |ε ^ 3 * (g₃ (foot u q) - g₃ u)| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = ε * |g₁ (foot u q) - g₁ u - dot (G₁ u) (foot u q - u)| + ε * |dot (G₁ u) (Φ u q - v)|
        + ε ^ 3 * |g₃ (foot u q) - g₃ u| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg hε3]
    _ ≤ ε * (M₁ / 2 * Φm ^ 2) + ε * (L₁ * Δ) + ε ^ 3 * (L₃ * Φm) := by gcongr
    _ = _ := by ring

/-- The displacement of a foot compared to its second order approximation. -/
lemma norm_Φ_sub_approx_le {u q q₀ : ℂ} {t δ : ℝ} (hu : ‖u‖ ≤ 1) (hq : ‖q‖ ≤ t) (hε : 0 ≤ ε)
    (hq₀ : ‖q₀‖ ≤ P) (hδ : ‖q - (ε : ℂ) * q₀‖ ≤ δ) :
    ‖Φ u q - (((ε ^ 2 / 2) * dot u q₀ : ℝ) : ℂ) * q₀‖ ≤
      (f (t ^ 2) - 1 / 2) * t ^ 2 + 1 / 2 * (t + ε * P) * δ := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hq
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  set q' := (ε : ℂ) * q₀ with hq'
  have hdq' : dot u q' = ε * dot u q₀ := by rw [hq', dot_real_mul_right]
  have e : Φ u q - (((ε ^ 2 / 2) * dot u q₀ : ℝ) : ℂ) * q₀ =
      (((f (‖q‖ ^ 2) - 1 / 2) * dot u q : ℝ) : ℂ) * q + ((dot u q / 2 : ℝ) : ℂ) * (q - q')
        + ((dot u (q - q') / 2 : ℝ) : ℂ) * q' := by
    rw [dot_sub_right, hdq', hq']
    simp only [Φ]
    push_cast
    ring
  have hf1 : 1 / 2 ≤ f (‖q‖ ^ 2) := half_le_f (by positivity)
  have hf2 : f (‖q‖ ^ 2) ≤ f (t ^ 2) := f_mono (by gcongr)
  have hdot : |dot u q| ≤ ‖q‖ := (abs_dot_le _ _).trans (by nlinarith [norm_nonneg q])
  have hq'P : ‖q'‖ ≤ ε * P := by
    rw [hq', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]; gcongr
  rw [e]
  have n1 : ‖(((f (‖q‖ ^ 2) - 1 / 2) * dot u q : ℝ) : ℂ) * q‖ ≤ (f (t ^ 2) - 1 / 2) * t ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith)]
    calc (f (‖q‖ ^ 2) - 1 / 2) * |dot u q| * ‖q‖ ≤ (f (t ^ 2) - 1 / 2) * ‖q‖ * ‖q‖ := by
          gcongr; linarith
      _ ≤ (f (t ^ 2) - 1 / 2) * t * t := by
          have : 0 ≤ f (t ^ 2) - 1 / 2 := by linarith
          gcongr
      _ = _ := by ring
  have n2 : ‖((dot u q / 2 : ℝ) : ℂ) * (q - q')‖ ≤ 1 / 2 * t * δ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    calc |dot u q| / 2 * ‖q - q'‖ ≤ ‖q‖ / 2 * δ := by gcongr
      _ ≤ t / 2 * δ := by gcongr
      _ = _ := by ring
  have n3 : ‖((dot u (q - q') / 2 : ℝ) : ℂ) * q'‖ ≤ 1 / 2 * δ * (ε * P) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    have : |dot u (q - q')| ≤ δ := (abs_dot_le _ _).trans (by nlinarith [norm_nonneg (q - q')])
    calc |dot u (q - q')| / 2 * ‖q'‖ ≤ δ / 2 * (ε * P) := by gcongr
      _ = _ := by ring
  calc _ ≤ ‖(((f (‖q‖ ^ 2) - 1 / 2) * dot u q : ℝ) : ℂ) * q‖ + ‖((dot u q / 2 : ℝ) : ℂ) * (q - q')‖
        + ‖((dot u (q - q') / 2 : ℝ) : ℂ) * q'‖ := norm_add₃_le
    _ ≤ (f (t ^ 2) - 1 / 2) * t ^ 2 + 1 / 2 * t * δ + 1 / 2 * δ * (ε * P) := by gcongr
    _ = _ := by ring

/-- **Proposition 5.2**: explicit bound for the remainder of the third order expansion of the
wobbling function, for the terrain `g = ε g₁ + ε³ g₃` on the unit disc. -/
theorem abs_wob_sub_third_order_le (hr : T.r = 1) (hε : 0 ≤ ε)
    (hg : IsLip g (ε * L₁ + ε ^ 3 * L₃)) (hs : SmallL T (ε * L₁ + ε ^ 3 * L₃))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * g₁ x + ε ^ 3 * g₃ x)
    (hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 → |g₁ x - g₁ u - dot (G₁ u) (x - u)| ≤ M₁ / 2 * ‖x - u‖ ^ 2)
    (hM : 0 ≤ M₁) (hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖G₁ u‖ ≤ L₁)
    (h3 : ∀ x y : ℂ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → |g₃ x - g₃ y| ≤ L₃ * ‖x - y‖)
    (hP : ∀ θ, ‖T.Q g₁ θ 0‖ ≤ P) (hP₃ : ∀ θ, ‖T.Q g₃ θ 0‖ ≤ P₃)
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (θ : ℝ) :
    |wob T g (ε * L₁ + ε ^ 3 * L₃) θ - ε * F₀ T g₁ τ μ θ
        - ε ^ 3 * (w3 T G₁ τ μ θ (T.Q g₁ θ 0) + F₀ T g₃ τ μ θ)| ≤
      Rem T.K T.dmin L₁ M₁ L₃ P P₃ ε := by
  set L := ε * L₁ + ε ^ 3 * L₃ with hLdef
  set q := tilt T g L θ with hqdef
  set q₀ := T.Q g₁ θ 0 with hq₀def
  set q₃ := T.Q g₃ θ 0 with hq₃def
  have hL0 : 0 ≤ L := hg.nonneg
  have hK0 := T.K_nonneg
  have hdmin := T.dmin_pos
  set t₀ := L * T.K with ht₀
  have ht₀0 : 0 ≤ t₀ := by positivity
  have ht₀1 : t₀ ≤ 1 := by have := hs.hK; linarith
  have hn : ∀ a : ℂ, ‖a‖ ≤ T.r → ‖rot θ * a‖ ≤ 1 := fun a ha => by rw [norm_rot_mul, ← hr]; exact ha
  have hΦ : ∀ a : ℂ, ‖a‖ ≤ T.r → ∀ t, ‖q‖ ≤ t → ‖Φ (rot θ * a) q‖ ≤ f (t ^ 2) * t ^ 2 :=
    fun a ha t hqt => by
      have := norm_Φ_le (hn a ha) hqt; simpa using this
  have hq0 : ‖q‖ ≤ t₀ := norm_tilt_le hg hs θ
  have hQq : T.Q g θ q = q := Q_tilt hg hs θ
  have hQ0 : T.Q g θ 0 = (ε : ℂ) * q₀ + ((ε ^ 3 : ℝ) : ℂ) * q₃ := Q_zero_eq hr hgd θ
  have hq₃n : ‖((ε ^ 3 : ℝ) : ℂ) * q₃‖ ≤ ε ^ 3 * P₃ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hP₃ θ) (by positivity)
  have hq₀n : ‖(ε : ℂ) * q₀‖ ≤ ε * P := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (hP θ) hε
  -- the tilt is close to the idealised one
  have hdiff : ∀ t, ‖q‖ ≤ t → ‖q - T.Q g θ 0‖ ≤ 2 * T.K * L / T.dmin * (f (t ^ 2) * t ^ 2) := by
    intro t hqt
    have := norm_Q_sub_Q_zero_le (T := T) hg θ q (hΦ _ T.normA t hqt) (hΦ _ T.normB t hqt)
      (hΦ _ T.normC t hqt) (hΦ _ T.normD t hqt)
    rw [hQq] at this
    calc _ ≤ T.K * (2 * L * (f (t ^ 2) * t ^ 2) / T.dmin) := this
      _ = _ := by ring
  set t₁ := min t₀ (ε * P + ε ^ 3 * P₃ + 2 * T.K * L / T.dmin * (f (t₀ ^ 2) * t₀ ^ 2)) with ht₁
  have hq1 : ‖q‖ ≤ t₁ := by
    refine le_min hq0 ?_
    calc ‖q‖ ≤ ‖T.Q g θ 0‖ + ‖q - T.Q g θ 0‖ := by
          have := norm_add_le (T.Q g θ 0) (q - T.Q g θ 0); simpa using this
      _ ≤ (ε * P + ε ^ 3 * P₃) + 2 * T.K * L / T.dmin * (f (t₀ ^ 2) * t₀ ^ 2) := by
          gcongr
          · rw [hQ0]; exact (norm_add_le _ _).trans (add_le_add hq₀n hq₃n)
          · exact hdiff t₀ hq0
      _ = _ := by ring
  have ht₁1 : t₁ ≤ 1 := (min_le_left _ _).trans ht₀1
  set Φ₁ := f (t₁ ^ 2) * t₁ ^ 2 with hΦ₁
  set δ := ε ^ 3 * P₃ + 2 * T.K * L / T.dmin * Φ₁ with hδ
  have hqδ : ‖q - (ε : ℂ) * q₀‖ ≤ δ := by
    have e : q - (ε : ℂ) * q₀ = (q - T.Q g θ 0) + ((ε ^ 3 : ℝ) : ℂ) * q₃ := by rw [hQ0]; ring
    rw [e]
    calc _ ≤ ‖q - T.Q g θ 0‖ + ‖((ε ^ 3 : ℝ) : ℂ) * q₃‖ := norm_add_le _ _
      _ ≤ 2 * T.K * L / T.dmin * Φ₁ + ε ^ 3 * P₃ := add_le_add (hdiff t₁ hq1) hq₃n
      _ = δ := by ring
  set Δ := (f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 + 1 / 2 * (t₁ + ε * P) * δ with hΔ
  have hqle : ‖q‖ ≤ 1 := hq1.trans ht₁1
  -- the four feet
  have foot_E : ∀ a : ℂ, ‖a‖ ≤ T.r →
      |g (foot (rot θ * a) q) - ε * g₁ (rot θ * a) - ε ^ 3 * g₃ (rot θ * a) +
        ε * dot (G₁ (rot θ * a)) ((((ε ^ 2 / 2) * dot (rot θ * a) q₀ : ℝ) : ℂ) * q₀)| ≤
      ε * L₁ * Δ + ε * (M₁ / 2 * Φ₁ ^ 2) + ε ^ 3 * (L₃ * Φ₁) := fun a ha =>
    foot_error (hn a ha) hqle hε hgd hT hG h3 hM (hΦ a ha t₁ hq1)
      (norm_Φ_sub_approx_le (hn a ha) hq1 hε (hP θ) hqδ)
  have eA := foot_E T.A T.normA
  have eB := foot_E T.B T.normB
  have eC := foot_E T.C T.normC
  have eD := foot_E T.D T.normD
  set b := ε * L₁ * Δ + ε * (M₁ / 2 * Φ₁ ^ 2) + ε ^ 3 * (L₃ * Φ₁) with hb
  have hdotG : ∀ a : ℂ, dot (G₁ (rot θ * a)) ((((ε ^ 2 / 2) * dot (rot θ * a) q₀ : ℝ) : ℂ) * q₀) =
      ε ^ 2 / 2 * (dot (G₁ (rot θ * a)) q₀ * dot (rot θ * a) q₀) := by
    intro a; rw [dot_real_mul_right]; ring
  rw [wob_eq hg hs θ hX]
  unfold F₀ w3
  simp only [hdotG] at eA eB eC eD
  set xA := g (foot (rot θ * T.A) q)
  set xB := g (foot (rot θ * T.B) q)
  set xC := g (foot (rot θ * T.C) q)
  set xD := g (foot (rot θ * T.D) q)
  have e : τ * xA + (1 - τ) * xC - μ * xB - (1 - μ) * xD - ε * (τ * g₁ (rot θ * T.A) +
      (1 - τ) * g₁ (rot θ * T.C) - μ * g₁ (rot θ * T.B) - (1 - μ) * g₁ (rot θ * T.D)) -
      ε ^ 3 * (-(1 / 2) * (τ * (dot (G₁ (rot θ * T.A)) q₀ * dot (rot θ * T.A) q₀) -
        μ * (dot (G₁ (rot θ * T.B)) q₀ * dot (rot θ * T.B) q₀) +
        (1 - τ) * (dot (G₁ (rot θ * T.C)) q₀ * dot (rot θ * T.C) q₀) -
        (1 - μ) * (dot (G₁ (rot θ * T.D)) q₀ * dot (rot θ * T.D) q₀)) +
        (τ * g₃ (rot θ * T.A) + (1 - τ) * g₃ (rot θ * T.C) - μ * g₃ (rot θ * T.B) -
          (1 - μ) * g₃ (rot θ * T.D))) =
      τ * (xA - ε * g₁ (rot θ * T.A) - ε ^ 3 * g₃ (rot θ * T.A) +
          ε * (ε ^ 2 / 2 * (dot (G₁ (rot θ * T.A)) q₀ * dot (rot θ * T.A) q₀)))
      + (1 - τ) * (xC - ε * g₁ (rot θ * T.C) - ε ^ 3 * g₃ (rot θ * T.C) +
          ε * (ε ^ 2 / 2 * (dot (G₁ (rot θ * T.C)) q₀ * dot (rot θ * T.C) q₀)))
      - μ * (xB - ε * g₁ (rot θ * T.B) - ε ^ 3 * g₃ (rot θ * T.B) +
          ε * (ε ^ 2 / 2 * (dot (G₁ (rot θ * T.B)) q₀ * dot (rot θ * T.B) q₀)))
      - (1 - μ) * (xD - ε * g₁ (rot θ * T.D) - ε ^ 3 * g₃ (rot θ * T.D) +
          ε * (ε ^ 2 / 2 * (dot (G₁ (rot θ * T.D)) q₀ * dot (rot θ * T.D) q₀))) := by ring
  rw [e]
  have hR : Rem T.K T.dmin L₁ M₁ L₃ P P₃ ε = 2 * b := by
    simp only [Rem, hb, hΔ, hδ, hΦ₁, ht₁, ht₀, hLdef]; ring
  rw [hR]
  have h1τ : 0 ≤ 1 - τ := by linarith
  have h1μ : 0 ≤ 1 - μ := by linarith
  calc _ ≤ τ * b + (1 - τ) * b + μ * b + (1 - μ) * b := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
        rw [abs_mul] <;> [rw [abs_of_nonneg hτ0]; rw [abs_of_nonneg h1τ]; rw [abs_of_nonneg hμ0];
          rw [abs_of_nonneg h1μ]] <;> gcongr
    _ = 2 * b := by ring

end Table

end Wobbly
