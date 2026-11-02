import Wobbly.Rational
import Wobbly.Coercive

/-!
# Statements closer to the paper

Corollaries which state results of the paper in the form in which the paper states them:

* `Table.exists_four_feet_of_F₀` (Corollary 4.11), `Table.exists_four_feet_of_w3`
  (Proposition 5.4) and `Table.hexagon_four_feet` (Corollary 5.5): the conclusion is that the
  smallness assumption (4.3) holds for the terrain `ε g₁` and the four feet are on the ground at some
  angle (the earlier `exists_stable_of_F₀`, `exists_stable_of_w3` and `hexagon_stable` only conclude
  `w_AC(θ) = 0` for some `θ`, which means "four feet on the ground" only under (4.3)).
* `Table.exists_balanced_of_paper` (Theorem 5.11): the hypotheses are exactly those of the paper
  (`t ≤ 1/2`, `λ' < 1`, `(n+1) A η < 1`, non-degeneracy); the smallness assumption (4.3) is derived
  from them instead of being assumed.
-/

noncomputable section

open Complex

namespace Wobbly

namespace Table

variable {T : Table}

/-- Upgrading a conclusion "`w_AC` vanishes somewhere on the terrain `ε g₁` for all small `ε`" to
"for all small `ε`, the smallness assumption (4.3) holds on `ε g₁` and the four feet are on the
ground at some angle" (Lemma 4.7). -/
theorem four_feet_of_wob_zero {g₁ : ℂ → ℝ} {L₁ : ℝ} (hg : IsLip g₁ L₁)
    (h : ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ θ, wob T (fun z => ε * g₁ z) (ε * L₁) θ = 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → SmallL T (ε * L₁) ∧
      ∃ θ q c, ‖q‖ < 1 ∧ resid (fun z => ε * g₁ z) θ q c T.A = 0 ∧
        resid (fun z => ε * g₁ z) θ q c T.B = 0 ∧ resid (fun z => ε * g₁ z) θ q c T.C = 0 ∧
        resid (fun z => ε * g₁ z) θ q c T.D = 0 := by
  obtain ⟨ε₁, hε₁, hstab⟩ := h
  have hL₁ := hg.nonneg
  have hK := T.K_nonneg
  have hr := T.r_nonneg
  have hd := T.dmin_pos
  set C := L₁ * T.K + 1 with hCdef
  have hC : 0 < C := by positivity
  refine ⟨min ε₁ (min (1 / (2 * C)) (T.dmin / ((4 * T.r + 1) * C))), by positivity,
    fun ε hε hεε => ?_⟩
  have e0 : ε ≤ ε₁ := hεε.trans (min_le_left _ _)
  have e1 : ε ≤ 1 / (2 * C) := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e2 : ε ≤ T.dmin / ((4 * T.r + 1) * C) :=
    hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLK : ε * L₁ * T.K ≤ ε * C := by
    have : L₁ * T.K ≤ C := by linarith
    nlinarith
  have hεC1 : ε * C ≤ 1 / 2 := by rw [le_div_iff₀ (by positivity)] at e1; linarith
  have hεC2 : ε * C ≤ T.dmin / (4 * T.r + 1) := by
    rw [le_div_iff₀ (by positivity)] at e2; rw [le_div_iff₀ (by positivity)]; linarith
  have hs : SmallL T (ε * L₁) := smallL_of_le (by positivity) (by linarith) (by linarith)
  have hgε : IsLip (fun z => ε * g₁ z) (ε * L₁) := fun x y => by
    simp only
    rw [← mul_sub, abs_mul, abs_of_pos hε, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg x y) hε.le
  obtain ⟨θ, hθ⟩ := hstab ε hε e0
  exact ⟨hs, θ, (four_feet_iff hgε hs θ).2 hθ⟩

/-- **Corollary 4.11** (in the form of the paper): for a cyclic table, if the idealised wobbling
function of `g₁` is not identically `0`, then there is `ε₀ > 0` such that for every
`0 < ε ≤ ε₀` the terrain `ε g₁` satisfies the smallness assumption (4.3) and there is an angle at
which the four feet of the table are on the ground. -/
theorem exists_four_feet_of_F₀ (hc : T.Cyclic) {g₁ : ℂ → ℝ} {L₁ τ μ : ℝ} (hg : IsLip g₁ L₁)
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) {θ₀ : ℝ} (h₀ : F₀ T g₁ τ μ θ₀ ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → SmallL T (ε * L₁) ∧
      ∃ θ q c, ‖q‖ < 1 ∧ resid (fun z => ε * g₁ z) θ q c T.A = 0 ∧
        resid (fun z => ε * g₁ z) θ q c T.B = 0 ∧ resid (fun z => ε * g₁ z) θ q c T.C = 0 ∧
        resid (fun z => ε * g₁ z) θ q c T.D = 0 :=
  four_feet_of_wob_zero hg (exists_stable_of_F₀ hc hg hX hτ0 hτ1 hμ0 hμ1 h₀)

/-- **Proposition 5.4** (conclusion in the form of the paper): for a rational table with `r = 1`
and `g₁` affine on the orbits of the rotations by `2π/n`, if `w₃ ≢ 0` then for every `ε` small
enough the smallness assumption (4.3) holds on `ε g₁` and the four feet are on the ground at some
angle. -/
theorem exists_four_feet_of_w3 {n : ℕ} [NeZero n] {iA iB iC iD : ZMod n} {τ μ : ℝ}
    (hR : IsRational T n iA iB iC iD τ μ) (hr : T.r = 1) {g₁ : ℂ → ℝ} {G₁ : ℂ → ℂ} {L₁ M₁ : ℝ}
    (hg : IsLip g₁ L₁) (haff : AffineOnOrbits g₁ n T.r)
    (hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 → |g₁ x - g₁ u - dot (G₁ u) (x - u)| ≤ M₁ / 2 * ‖x - u‖ ^ 2)
    (hM : 0 ≤ M₁) (hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖G₁ u‖ ≤ L₁) {θ₀ : ℝ}
    (h₀ : w3 T G₁ τ μ θ₀ (T.Q g₁ θ₀ 0) ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → SmallL T (ε * L₁) ∧
      ∃ θ q c, ‖q‖ < 1 ∧ resid (fun z => ε * g₁ z) θ q c T.A = 0 ∧
        resid (fun z => ε * g₁ z) θ q c T.B = 0 ∧ resid (fun z => ε * g₁ z) θ q c T.C = 0 ∧
        resid (fun z => ε * g₁ z) θ q c T.D = 0 :=
  four_feet_of_wob_zero hg (exists_stable_of_w3 hR hr hg haff hT hM hG h₀)

/-- **Corollary 5.5** (conclusion in the form of the paper): for the hexagonal table, if
`F₀[g₁] ≢ 0`, or `F₀[g₁] ≡ 0` and `w₃ ≢ 0`, then for every `ε` small enough the smallness
assumption (3) holds on `ε g₁` and the four feet are on the ground at some angle. -/
theorem hexagon_four_feet {g₁ : ℂ → ℝ} {G₁ : ℂ → ℂ} {L₁ M₁ : ℝ} (hg : IsLip g₁ L₁)
    (hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 → |g₁ x - g₁ u - dot (G₁ u) (x - u)| ≤ M₁ / 2 * ‖x - u‖ ^ 2)
    (hM : 0 ≤ M₁) (hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖G₁ u‖ ≤ L₁)
    (h : (∃ θ₀, F₀ hexTable g₁ (1 / 3) (2 / 3) θ₀ ≠ 0) ∨
      ((∀ θ, F₀ hexTable g₁ (1 / 3) (2 / 3) θ = 0) ∧
        ∃ θ₀, w3 hexTable G₁ (1 / 3) (2 / 3) θ₀ (hexTable.Q g₁ θ₀ 0) ≠ 0)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → SmallL hexTable (ε * L₁) ∧
      ∃ θ q c, ‖q‖ < 1 ∧ resid (fun z => ε * g₁ z) θ q c hexTable.A = 0 ∧
        resid (fun z => ε * g₁ z) θ q c hexTable.B = 0 ∧
        resid (fun z => ε * g₁ z) θ q c hexTable.C = 0 ∧
        resid (fun z => ε * g₁ z) θ q c hexTable.D = 0 :=
  four_feet_of_wob_zero hg (hexagon_stable hg hT hM hG h)

/-- The conditions of Theorem 5.11 (as stated in the paper) imply the smallness assumption (4.3). -/
lemma smallL_of_paper {L : ℝ} (hL : 0 ≤ L) (ht : Real.sqrt 2 * T.K * L ≤ 1 / 2)
    (hlam : 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * (Real.sqrt 2 * T.K * L) < 1) :
    SmallL T L := by
  have hK := T.K_nonneg
  have hr := T.r_nonneg
  have hd := T.dmin_pos
  have hs2 : 1 ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hLK : 0 ≤ L * T.K := mul_nonneg hL hK
  refine ⟨hL, ?_, ?_⟩
  · nlinarith
  · have hc : 0 ≤ 4 / Real.sqrt 3 * (T.r / T.dmin) := by positivity
    calc 4 / Real.sqrt 3 * (T.r / T.dmin) * (L * T.K) ^ 2
        ≤ 4 / Real.sqrt 3 * (T.r / T.dmin) * (Real.sqrt 2 * (L * T.K) ^ 2) := by
          gcongr; nlinarith [sq_nonneg (L * T.K)]
      _ = 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * (Real.sqrt 2 * T.K * L) := by ring
      _ < 1 := hlam

/-- **Theorem 5.11** with the hypotheses of the paper: a rational table (feet at `r ω^{i_E}`,
`ω = e^{2πi/n}`) which is non-degenerate (`σ ≤ |m(s)|` for `s ≢ 0, ±1 mod n`, with `σ > 0`)
stands on its four feet at some angle, on every `L`-Lipschitz terrain such that, with
`t = √2 K L`, `λ' = (4/√3)(r/d_min) K L t`, `η = (4/√3) r L t`, `A = 2K√n / (σ d_min (1 - λ'))`,
we have `t ≤ 1/2`, `λ' < 1` and `(n+1) A η < 1`. The smallness assumption (4.3) is not assumed:
it follows from these conditions (`smallL_of_paper`). -/
theorem exists_balanced_of_paper {n : ℕ} [NeZero n] {g : ℂ → ℝ} {L : ℝ} {iA iB iC iD : ZMod n}
    {τ μ σ : ℝ} (hR : IsRational T n iA iB iC iD τ μ) (hσ : 0 < σ)
    (hnd : ∀ s : ZMod n, s ≠ 0 → s ≠ 1 → s ≠ -1 → σ ≤ ‖mR iA iB iC iD τ μ s‖)
    (hg : IsLip g L) (hr : 0 < T.r)
    (ht : Real.sqrt 2 * T.K * L ≤ 1 / 2)
    (hlam : 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * (Real.sqrt 2 * T.K * L) < 1)
    (hmain : (n + 1) * (2 * T.K * Real.sqrt n / (σ * T.dmin *
        (1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * (Real.sqrt 2 * T.K * L)))) *
        (4 / Real.sqrt 3 * T.r * L * (Real.sqrt 2 * T.K * L)) < 1) :
    ∃ θ q c, ‖q‖ < 1 ∧ resid g θ q c T.A = 0 ∧ resid g θ q c T.B = 0 ∧
      resid g θ q c T.C = 0 ∧ resid g θ q c T.D = 0 :=
  exists_balanced_of_nondeg hR hnd hg (smallL_of_paper hg.nonneg ht hlam)
    (OrbitData.of_paper hg.nonneg hσ hr ht hlam hmain)

end Table

end Wobbly
