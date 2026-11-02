import Wobbly.Remainder
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Complements to Proposition 5.2

* `taylor_of_lipschitz_grad`: the second order Taylor estimate used in Proposition 5.2 holds as
  soon as `g₁` is differentiable on the closed unit disc with an `M₁`-Lipschitz gradient (for
  instance if `‖D² g₁‖ ≤ M₁` on the disc).
* `Rem_le_scale`: `R(ε) ≤ (ε/ε')⁵ R(ε')` for `0 < ε ≤ ε'`, i.e. `R(ε)/ε⁵` is non-decreasing.
-/

open Complex

namespace Wobbly

/-- The linear form `v ↦ a · v`. -/
noncomputable def dotCLM (a : ℂ) : ℂ →L[ℝ] ℝ := a.re • Complex.reCLM + a.im • Complex.imCLM

@[simp] lemma dotCLM_apply (a v : ℂ) : dotCLM a v = dot a v := by
  simp [dotCLM, dot]

/-- Second order Taylor estimate for a function with a Lipschitz gradient on the closed unit disc. -/
theorem taylor_of_lipschitz_grad {g : ℂ → ℝ} {G : ℂ → ℂ} {M : ℝ}
    (hd : ∀ x : ℂ, ‖x‖ ≤ 1 → HasFDerivAt g (dotCLM (G x)) x)
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
  have hpd : ∀ t, HasDerivAt p v t := fun t =>
    (((hasDerivAt_id t).smul_const v).const_add u).congr_deriv (by simp)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => g (p t)) (dot (G (p t)) v) t :=
    fun t ht => ((hd (p t) (hp t ht)).comp_hasDerivAt t (hpd t)).congr_deriv (by simp)
  have hpu : ∀ t, 0 ≤ t → ‖p t - u‖ = t * ‖v‖ := fun t ht => by
    simp only [p, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |dot (G (p t)) v - dot (G u) v| ≤ M * ‖v‖ ^ 2 * t := by
    intro t ht
    rw [← dot_sub_left]
    calc _ ≤ ‖G (p t) - G u‖ * ‖v‖ := abs_dot_le _ _
      _ ≤ M * ‖p t - u‖ * ‖v‖ := by gcongr; exact hL _ _ (hp t ht) hu
      _ = M * ‖v‖ ^ 2 * t := by rw [hpu t ht.1]; ring
  -- the two auxiliary functions are antitone on `[0, 1]`
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

/-- `f s - 1/2 = s h(s)` with `h(s) = 1 / (2 (1 + √(1 - s))²)`, which is non-decreasing. -/
lemma f_sub_half {s : ℝ} (hs : s ≤ 1) : f s - 1 / 2 = s * (1 / (2 * (1 + Real.sqrt (1 - s)) ^ 2)) := by
  have hc := Real.sq_sqrt (show 0 ≤ 1 - s by linarith)
  have hp : 0 < 1 + Real.sqrt (1 - s) := by positivity
  unfold f
  field_simp
  nlinarith [hc]

lemma h_mono {s s' : ℝ} (h : s ≤ s') :
    1 / (2 * (1 + Real.sqrt (1 - s)) ^ 2) ≤ 1 / (2 * (1 + Real.sqrt (1 - s')) ^ 2) := by
  apply one_div_le_one_div_of_le (by positivity)
  have : Real.sqrt (1 - s') ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
  gcongr

/-- Monotonicity of the building blocks of `R`. -/
lemma Rem_blocks {L₁ L₃ P P₃ ε ε' l : ℝ} (hL₃ : 0 ≤ L₃) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hε' : 0 ≤ ε') (hεl : ε = l * ε') :
    ε * L₁ + ε ^ 3 * L₃ ≤ l * (ε' * L₁ + ε' ^ 3 * L₃) ∧ ε ^ 3 * P₃ ≤ l ^ 3 * (ε' ^ 3 * P₃) ∧
      ε * P ≤ l * (ε' * P) := by
  have hl3 : l ^ 3 ≤ l := by simpa using pow_le_pow_of_le_one hl0 hl1 (by norm_num : 1 ≤ 3)
  subst hεl
  refine ⟨?_, by rw [mul_pow]; ring_nf; exact le_rfl, by ring_nf; exact le_rfl⟩
  have : (l * ε') ^ 3 * L₃ ≤ l * (ε' ^ 3 * L₃) := by
    rw [mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_right hl3 (by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- `R(ε) ≤ (ε/ε')⁵ R(ε')`: `R(ε)/ε⁵` is non-decreasing. -/
theorem Rem_le_scale {K dmin L₁ M₁ L₃ P P₃ ε ε' : ℝ} (hK : 0 ≤ K) (hd : 0 < dmin) (hL₁ : 0 ≤ L₁)
    (hM₁ : 0 ≤ M₁) (hL₃ : 0 ≤ L₃) (hP : 0 ≤ P) (hP₃ : 0 ≤ P₃) (hε : 0 < ε) (hεε : ε ≤ ε')
    (ht : (ε' * L₁ + ε' ^ 3 * L₃) * K ≤ 1) :
    Rem K dmin L₁ M₁ L₃ P P₃ ε ≤ (ε / ε') ^ 5 * Rem K dmin L₁ M₁ L₃ P P₃ ε' := by
  have hε' : 0 < ε' := hε.trans_le hεε
  obtain ⟨l, hl⟩ : ∃ l, l = ε / ε' := ⟨_, rfl⟩
  rw [← hl]
  have hl0 : 0 < l := hl ▸ div_pos hε hε'
  have hl1 : l ≤ 1 := hl ▸ (div_le_one hε').2 hεε
  have hεl : ε = l * ε' := by rw [hl]; field_simp
  have hl2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0.le hl1
  have hl3 : l ^ 3 ≤ l := by simpa using pow_le_pow_of_le_one hl0.le hl1 (by norm_num : 1 ≤ 3)
  obtain ⟨hLL, hP3l, hPl⟩ := Rem_blocks (L₁ := L₁) (P := P) (P₃ := P₃) hL₃ hl0.le hl1 hε'.le hεl
  have hf0 : ∀ s, 0 ≤ f s := fun s => (f_pos s).le
  simp only [Rem]
  generalize hL' : ε' * L₁ + ε' ^ 3 * L₃ = L' at hLL ht ⊢
  generalize hL : ε * L₁ + ε ^ 3 * L₃ = L at hLL ⊢
  have hL'0 : 0 ≤ L' := hL' ▸ by positivity
  have hL0 : 0 ≤ L := hL ▸ by positivity
  generalize ht₀' : L' * K = t₀' at ht ⊢
  generalize ht₀ : L * K = t₀ at ⊢
  have ht₀le : t₀ ≤ l * t₀' := by
    rw [← ht₀, ← ht₀', ← mul_assoc]; exact mul_le_mul_of_nonneg_right hLL hK
  have ht₀0 : 0 ≤ t₀ := ht₀ ▸ mul_nonneg hL0 hK
  have ht₀'0 : 0 ≤ t₀' := ht₀' ▸ mul_nonneg hL'0 hK
  have hsq₀ : t₀ ^ 2 ≤ t₀' ^ 2 :=
    pow_le_pow_left₀ ht₀0 (ht₀le.trans (mul_le_of_le_one_left ht₀'0 hl1)) 2
  generalize hS' : ε' * P + ε' ^ 3 * P₃ + 2 * K * L' / dmin * (f (t₀' ^ 2) * t₀' ^ 2) = S' at ⊢
  generalize hS : ε * P + ε ^ 3 * P₃ + 2 * K * L / dmin * (f (t₀ ^ 2) * t₀ ^ 2) = S at ⊢
  have hSle : S ≤ l * S' := by
    rw [← hS, ← hS']
    have X1 : 2 * K * L ≤ 2 * K * (l * L') := mul_le_mul_of_nonneg_left hLL (by positivity)
    have X2 : f (t₀ ^ 2) * t₀ ^ 2 ≤ f (t₀' ^ 2) * t₀' ^ 2 :=
      mul_le_mul (f_mono hsq₀) hsq₀ (sq_nonneg _) (hf0 _)
    have a3 : 2 * K * L / dmin * (f (t₀ ^ 2) * t₀ ^ 2) ≤ l * (2 * K * L' / dmin * (f (t₀' ^ 2) * t₀' ^ 2)) := by
      have e : l * (2 * K * L' / dmin * (f (t₀' ^ 2) * t₀' ^ 2)) =
          2 * K * (l * L') / dmin * (f (t₀' ^ 2) * t₀' ^ 2) := by ring
      rw [e]
      exact mul_le_mul (div_le_div_of_nonneg_right X1 hd.le) X2
        (mul_nonneg (hf0 _) (sq_nonneg _)) (div_nonneg (by positivity) hd.le)
    have a2 : ε ^ 3 * P₃ ≤ l * (ε' ^ 3 * P₃) :=
      hP3l.trans (mul_le_mul_of_nonneg_right hl3 (by positivity))
    linarith
  have hS0 : 0 ≤ S := hS ▸ by have := hf0 (t₀ ^ 2); positivity
  have hS'0 : 0 ≤ S' := hS' ▸ by have := hf0 (t₀' ^ 2); positivity
  generalize ht₁' : min t₀' S' = t₁' at ⊢
  generalize ht₁ : min t₀ S = t₁ at ⊢
  have ht₁le : t₁ ≤ l * t₁' := by
    rw [← ht₁, ← ht₁', mul_min_of_nonneg _ _ hl0.le]; exact min_le_min ht₀le hSle
  have ht₁0 : 0 ≤ t₁ := ht₁ ▸ le_min ht₀0 hS0
  have ht₁'1 : t₁' ≤ 1 := ht₁' ▸ (min_le_left _ _).trans ht
  have ht₁'0 : 0 ≤ t₁' := ht₁' ▸ le_min ht₀'0 hS'0
  have ht₁1 : t₁ ≤ 1 := ht₁le.trans ((mul_le_mul hl1 ht₁'1 ht₁'0 zero_le_one).trans_eq (one_mul 1))
  have hsq : t₁ ^ 2 ≤ l ^ 2 * t₁' ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ ht₁0 ht₁le 2
  have hsq' : t₁ ^ 2 ≤ t₁' ^ 2 := hsq.trans (mul_le_of_le_one_left (sq_nonneg _) hl2)
  generalize hΦ' : f (t₁' ^ 2) * t₁' ^ 2 = Φ' at ⊢
  generalize hΦ : f (t₁ ^ 2) * t₁ ^ 2 = Φ at ⊢
  have hΦle : Φ ≤ l ^ 2 * Φ' := by
    rw [← hΦ, ← hΦ']
    calc f (t₁ ^ 2) * t₁ ^ 2 ≤ f (t₁' ^ 2) * (l ^ 2 * t₁' ^ 2) :=
          mul_le_mul (f_mono hsq') hsq (by positivity) (hf0 _)
      _ = _ := by ring
  have hΦ0 : 0 ≤ Φ := hΦ ▸ mul_nonneg (hf0 _) (sq_nonneg _)
  have hΦ'0 : 0 ≤ Φ' := hΦ' ▸ mul_nonneg (hf0 _) (sq_nonneg _)
  generalize hδ' : ε' ^ 3 * P₃ + 2 * K * L' / dmin * Φ' = δ' at ⊢
  generalize hδ : ε ^ 3 * P₃ + 2 * K * L / dmin * Φ = δ at ⊢
  have hδle : δ ≤ l ^ 3 * δ' := by
    rw [← hδ, ← hδ']
    have : 2 * K * L / dmin * Φ ≤ 2 * K * (l * L') / dmin * (l ^ 2 * Φ') := by gcongr
    have e : l ^ 3 * (ε' ^ 3 * P₃ + 2 * K * L' / dmin * Φ') =
        l ^ 3 * (ε' ^ 3 * P₃) + 2 * K * (l * L') / dmin * (l ^ 2 * Φ') := by ring
    rw [e]; linarith
  have hδ0 : 0 ≤ δ := hδ ▸ by positivity
  have hh : (f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 ≤ l ^ 4 * ((f (t₁' ^ 2) - 1 / 2) * t₁' ^ 2) := by
    rw [f_sub_half (pow_le_one₀ ht₁0 ht₁1), f_sub_half (pow_le_one₀ ht₁'0 ht₁'1)]
    have h4 : t₁ ^ 2 * t₁ ^ 2 ≤ l ^ 4 * (t₁' ^ 2 * t₁' ^ 2) := by
      have := mul_le_mul hsq hsq (sq_nonneg _) (by positivity)
      calc _ ≤ l ^ 2 * t₁' ^ 2 * (l ^ 2 * t₁' ^ 2) := this
        _ = _ := by ring
    calc t₁ ^ 2 * (1 / (2 * (1 + Real.sqrt (1 - t₁ ^ 2)) ^ 2)) * t₁ ^ 2
        = (t₁ ^ 2 * t₁ ^ 2) * (1 / (2 * (1 + Real.sqrt (1 - t₁ ^ 2)) ^ 2)) := by ring
      _ ≤ (l ^ 4 * (t₁' ^ 2 * t₁' ^ 2)) * (1 / (2 * (1 + Real.sqrt (1 - t₁' ^ 2)) ^ 2)) :=
          mul_le_mul h4 (h_mono hsq') (by positivity) (by positivity)
      _ = _ := by ring
  have hmid : 1 / 2 * (t₁ + ε * P) * δ ≤ l ^ 4 * (1 / 2 * (t₁' + ε' * P) * δ') := by
    have h1 : t₁ + ε * P ≤ l * (t₁' + ε' * P) := by linarith
    calc 1 / 2 * (t₁ + ε * P) * δ ≤ 1 / 2 * (l * (t₁' + ε' * P)) * (l ^ 3 * δ') := by
          gcongr
      _ = _ := by ring
  have hhp : 0 ≤ (f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 := by
    have := half_le_f (sq_nonneg t₁); positivity
  -- conclusion
  have b1 : ε * M₁ * Φ ^ 2 ≤ l ^ 5 * (ε' * M₁ * Φ' ^ 2) := by
    have : Φ ^ 2 ≤ (l ^ 2 * Φ') ^ 2 := pow_le_pow_left₀ hΦ0 hΦle 2
    calc ε * M₁ * Φ ^ 2 ≤ l * ε' * M₁ * (l ^ 2 * Φ') ^ 2 := by rw [hεl]; gcongr
      _ = _ := by ring
  have b2 : 2 * ε * L₁ * ((f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 + 1 / 2 * (t₁ + ε * P) * δ) ≤
      l ^ 5 * (2 * ε' * L₁ * ((f (t₁' ^ 2) - 1 / 2) * t₁' ^ 2 + 1 / 2 * (t₁' + ε' * P) * δ')) := by
    calc _ ≤ 2 * ε * L₁ * (l ^ 4 * ((f (t₁' ^ 2) - 1 / 2) * t₁' ^ 2) +
          l ^ 4 * (1 / 2 * (t₁' + ε' * P) * δ')) :=
          mul_le_mul_of_nonneg_left (add_le_add hh hmid) (by positivity)
      _ = _ := by rw [hεl]; ring
  have b3 : 2 * ε ^ 3 * L₃ * Φ ≤ l ^ 5 * (2 * ε' ^ 3 * L₃ * Φ') := by
    calc 2 * ε ^ 3 * L₃ * Φ ≤ 2 * (l * ε') ^ 3 * L₃ * (l ^ 2 * Φ') := by rw [hεl]; gcongr
      _ = _ := by ring
  linarith

end Wobbly
