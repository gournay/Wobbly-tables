import Wobbly.Hover

/-!
# The wobbling function (Lemma 4.7, Propositions 4.8–4.10 of the paper)

In the position `(θ, q, c)`, the foot which is at `a` in the frame of the table is at height
`c + dot (rot θ * a) q` above the horizontal position `foot (rot θ * a) q`, where the ground is at
height `g (foot (rot θ * a) q)`. The difference is the *residual* `resid g θ q c a`.
-/

noncomputable section

open Complex

namespace Wobbly

/-- Height above the ground of the foot which is at `a` in the frame of the table, when the
table is in the position `(θ, q, c)`. -/
def resid (g : ℂ → ℝ) (θ : ℝ) (q : ℂ) (c : ℝ) (a : ℂ) : ℝ :=
  c + dot (rot θ * a) q - g (foot (rot θ * a) q)

lemma resid_add (g : ℂ → ℝ) (θ : ℝ) (q : ℂ) (c δ : ℝ) (a : ℂ) :
    resid g θ q (c + δ) a = resid g θ q c a + δ := by
  unfold resid; ring

namespace Table

variable {T : Table} {g : ℂ → ℝ} {L : ℝ}

lemma dot_rot_e₁ (θ : ℝ) (q : ℂ) :
    dot (rot θ * T.e₁) q * T.d₁ = dot (rot θ * T.A) q - dot (rot θ * T.C) q := by
  rw [← dot_sub_left, T.rot_A_sub_C, dot_real_mul_left]; ring

lemma dot_rot_e₂ (θ : ℝ) (q : ℂ) :
    dot (rot θ * T.e₂) q * T.d₂ = dot (rot θ * T.B) q - dot (rot θ * T.D) q := by
  rw [← dot_sub_left, T.rot_B_sub_D, dot_real_mul_left]; ring

/-- The fixed points of `Q_θ` are exactly the tilts for which `A, C` are equally high and `B, D`
are equally high above the ground (for any height `c`). -/
lemma Q_eq_self_iff (θ : ℝ) (q : ℂ) (c : ℝ) :
    T.Q g θ q = q ↔
      (resid g θ q c T.A = resid g θ q c T.C ∧ resid g θ q c T.B = resid g θ q c T.D) := by
  have hd := T.det_rot_ne θ
  have h₁ := T.d₁_pos
  have h₂ := T.d₂_pos
  constructor
  · intro hq
    have e1 : dot (rot θ * T.e₁) q =
        (g (foot (rot θ * T.A) q) - g (foot (rot θ * T.C) q)) / T.d₁ := by
      conv_lhs => rw [← hq]
      exact dot_solve2_left hd _ _
    have e2 : dot (rot θ * T.e₂) q =
        (g (foot (rot θ * T.B) q) - g (foot (rot θ * T.D) q)) / T.d₂ := by
      conv_lhs => rw [← hq]
      exact dot_solve2_right hd _ _
    have k1 := dot_rot_e₁ (T := T) θ q
    have k2 := dot_rot_e₂ (T := T) θ q
    rw [e1, div_mul_cancel₀ _ h₁.ne'] at k1
    rw [e2, div_mul_cancel₀ _ h₂.ne'] at k2
    unfold resid
    constructor <;> linarith
  · rintro ⟨hAC, hBD⟩
    unfold resid at hAC hBD
    symm
    apply eq_solve2 hd
    · rw [eq_div_iff h₁.ne', dot_rot_e₁]; linarith
    · rw [eq_div_iff h₂.ne', dot_rot_e₂]; linarith

/-! ### The equal hovering position and the wobbling function -/

/-- Height of the centre in the equal hovering position with respect to `AC`. -/
def cAC (T : Table) (g : ℂ → ℝ) (L θ : ℝ) : ℝ :=
  g (foot (rot θ * T.A) (tilt T g L θ)) - dot (rot θ * T.A) (tilt T g L θ)

/-- The wobbling function `w_AC(θ)`: the common height of `B` and `D` above the ground in the
equal hovering position with respect to `AC`. -/
def wob (T : Table) (g : ℂ → ℝ) (L θ : ℝ) : ℝ :=
  resid g θ (tilt T g L θ) (cAC T g L θ) T.B

lemma resid_A_hover (θ : ℝ) : resid g θ (tilt T g L θ) (cAC T g L θ) T.A = 0 := by
  unfold resid cAC; ring

lemma resid_hover (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    resid g θ (tilt T g L θ) (cAC T g L θ) T.A = 0 ∧
    resid g θ (tilt T g L θ) (cAC T g L θ) T.C = 0 ∧
    resid g θ (tilt T g L θ) (cAC T g L θ) T.B = wob T g L θ ∧
    resid g θ (tilt T g L θ) (cAC T g L θ) T.D = wob T g L θ := by
  have h := (Q_eq_self_iff (T := T) (g := g) θ (tilt T g L θ) (cAC T g L θ)).1
    (Q_tilt hg hs θ)
  have hA := resid_A_hover (T := T) (g := g) (L := L) θ
  refine ⟨hA, by rw [← h.1, hA], rfl, by rw [← h.2]; rfl⟩

/-- Lemma 4.7: there is a position at angle `θ` (with `‖q‖ < 1`) in which the four feet are on
the ground if and only if `w_AC(θ) = 0`. -/
theorem four_feet_iff (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    (∃ q c, ‖q‖ < 1 ∧ resid g θ q c T.A = 0 ∧ resid g θ q c T.B = 0 ∧
      resid g θ q c T.C = 0 ∧ resid g θ q c T.D = 0) ↔ wob T g L θ = 0 := by
  constructor
  · rintro ⟨q, c, hq, hA, hB, hC, hD⟩
    have hfix : T.Q g θ q = q :=
      (Q_eq_self_iff θ q c).2 ⟨by rw [hA, hC], by rw [hB, hD]⟩
    have hqt : q = tilt T g L θ :=
      fixed_unique hg hs θ hq hfix (norm_tilt_lt_one hg hs θ) (Q_tilt hg hs θ)
    subst hqt
    have hc : c = cAC T g L θ := by
      unfold resid at hA; unfold cAC; linarith
    subst hc
    exact hB
  · intro hw
    obtain ⟨hA, hC, hB, hD⟩ := resid_hover hg hs θ
    exact ⟨tilt T g L θ, cAC T g L θ, norm_tilt_lt_one hg hs θ, hA, by rw [hB, hw],
      hC, by rw [hD, hw]⟩

/-- Proposition 4.9 (common tilt): in the position `(θ, tilt, cAC - wob)`, the feet `B` and `D`
are on the ground and `A`, `C` are both at height `-w_AC(θ)`. -/
theorem hover_BD (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    resid g θ (tilt T g L θ) (cAC T g L θ - wob T g L θ) T.B = 0 ∧
    resid g θ (tilt T g L θ) (cAC T g L θ - wob T g L θ) T.D = 0 ∧
    resid g θ (tilt T g L θ) (cAC T g L θ - wob T g L θ) T.A = - wob T g L θ ∧
    resid g θ (tilt T g L θ) (cAC T g L θ - wob T g L θ) T.C = - wob T g L θ := by
  obtain ⟨hA, hC, hB, hD⟩ := resid_hover hg hs θ
  simp only [sub_eq_add_neg, resid_add, hA, hB, hC, hD]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Proposition 4.9 (uniqueness): a position (with `‖q‖ < 1`) in which `B, D` are on the ground and
`A, C` are equally high is `(θ, tilt, cAC - wob)`. In particular `w_BD = - w_AC`. -/
theorem hover_BD_unique (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) {q : ℂ} {c : ℝ} (hq : ‖q‖ < 1)
    (hB : resid g θ q c T.B = 0) (hD : resid g θ q c T.D = 0)
    (hAC : resid g θ q c T.A = resid g θ q c T.C) :
    q = tilt T g L θ ∧ c = cAC T g L θ - wob T g L θ := by
  have hfix : T.Q g θ q = q := (Q_eq_self_iff θ q c).2 ⟨hAC, by rw [hB, hD]⟩
  have hqt : q = tilt T g L θ :=
    fixed_unique hg hs θ hq hfix (norm_tilt_lt_one hg hs θ) (Q_tilt hg hs θ)
  refine ⟨hqt, ?_⟩
  subst hqt
  obtain ⟨-, -, hB', -⟩ := resid_hover hg hs θ
  unfold resid at hB hB'
  linarith

/-! ### The wobbling function in terms of the terrain (Propositions 4.8 and 4.10) -/

/-- Proposition 4.8: if `X = τ A + (1 - τ) C = μ B + (1 - μ) D` is the intersection of the
diagonals, then `w_AC = τ g(x_A) + (1-τ) g(x_C) - μ g(x_B) - (1-μ) g(x_D)`. -/
theorem wob_eq (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) {τ μ : ℝ}
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D) :
    wob T g L θ =
      τ * g (foot (rot θ * T.A) (tilt T g L θ)) + (1 - τ) * g (foot (rot θ * T.C) (tilt T g L θ))
      - μ * g (foot (rot θ * T.B) (tilt T g L θ))
      - (1 - μ) * g (foot (rot θ * T.D) (tilt T g L θ)) := by
  obtain ⟨hA, hC, hB, hD⟩ := resid_hover hg hs θ
  set q := tilt T g L θ
  set c := cAC T g L θ
  -- the heights are affine in the position of the foot
  have haff : τ * dot (rot θ * T.A) q + (1 - τ) * dot (rot θ * T.C) q =
      μ * dot (rot θ * T.B) q + (1 - μ) * dot (rot θ * T.D) q := by
    have e1 : dot (rot θ * ((τ : ℂ) * T.A + (1 - τ : ℝ) * T.C)) q =
        τ * dot (rot θ * T.A) q + (1 - τ) * dot (rot θ * T.C) q := by
      rw [mul_add, show rot θ * ((τ : ℂ) * T.A) = (τ : ℂ) * (rot θ * T.A) by ring,
        show rot θ * (((1 - τ : ℝ) : ℂ) * T.C) = ((1 - τ : ℝ) : ℂ) * (rot θ * T.C) by ring,
        dot_add_left, dot_real_mul_left, dot_real_mul_left]
    have e2 : dot (rot θ * ((μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)) q =
        μ * dot (rot θ * T.B) q + (1 - μ) * dot (rot θ * T.D) q := by
      rw [mul_add, show rot θ * ((μ : ℂ) * T.B) = (μ : ℂ) * (rot θ * T.B) by ring,
        show rot θ * (((1 - μ : ℝ) : ℂ) * T.D) = ((1 - μ : ℝ) : ℂ) * (rot θ * T.D) by ring,
        dot_add_left, dot_real_mul_left, dot_real_mul_left]
    rw [← e1, ← e2, hX]
  unfold resid at hA hB hC hD
  linear_combination τ * hA + (1 - τ) * hC - μ * hB - (1 - μ) * hD - haff

/-- The idealised wobbling function `F₀` of Remark 2.3 (b). -/
def F₀ (T : Table) (g : ℂ → ℝ) (τ μ θ : ℝ) : ℝ :=
  τ * g (rot θ * T.A) + (1 - τ) * g (rot θ * T.C) - μ * g (rot θ * T.B)
    - (1 - μ) * g (rot θ * T.D)

/-- Proposition 4.10: `|w_AC - F₀| ≤ 2 L f((LK)²) r (LK)²`, which is `≤ 4 (2 - √3) r K² L³`. -/
theorem abs_wob_sub_F₀_le (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) {τ μ : ℝ}
    (hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    |wob T g L θ - F₀ T g τ μ θ| ≤ 2 * (L * (f ((L * T.K) ^ 2) * T.r * (L * T.K) ^ 2)) := by
  set q := tilt T g L θ with hqdef
  have hq : ‖q‖ ≤ L * T.K := norm_tilt_le hg hs θ
  set M := L * (f ((L * T.K) ^ 2) * T.r * (L * T.K) ^ 2) with hM
  have hE : ∀ a : ℂ, ‖a‖ ≤ T.r → |g (foot (rot θ * a) q) - g (rot θ * a)| ≤ M := by
    intro a ha
    have ha' : ‖rot θ * a‖ ≤ T.r := by rw [norm_rot_mul]; exact ha
    calc |g (foot (rot θ * a) q) - g (rot θ * a)| ≤ L * ‖foot (rot θ * a) q - rot θ * a‖ := hg _ _
      _ = L * ‖Φ (rot θ * a) q‖ := by rw [foot, sub_sub_cancel_left, norm_neg]
      _ ≤ M := by
          rw [hM]
          gcongr
          · exact hs.nonneg
          · exact norm_Φ_le ha' hq
  have hA := hE T.A T.normA
  have hB := hE T.B T.normB
  have hC := hE T.C T.normC
  have hD := hE T.D T.normD
  rw [wob_eq hg hs θ hX, F₀]
  have e : τ * g (foot (rot θ * T.A) q) + (1 - τ) * g (foot (rot θ * T.C) q)
      - μ * g (foot (rot θ * T.B) q) - (1 - μ) * g (foot (rot θ * T.D) q)
      - (τ * g (rot θ * T.A) + (1 - τ) * g (rot θ * T.C) - μ * g (rot θ * T.B)
        - (1 - μ) * g (rot θ * T.D)) =
      τ * (g (foot (rot θ * T.A) q) - g (rot θ * T.A))
      + (1 - τ) * (g (foot (rot θ * T.C) q) - g (rot θ * T.C))
      - μ * (g (foot (rot θ * T.B) q) - g (rot θ * T.B))
      - (1 - μ) * (g (foot (rot θ * T.D) q) - g (rot θ * T.D)) := by ring
  rw [e]
  have h1 := abs_le.1 hA
  have h2 := abs_le.1 hB
  have h3 := abs_le.1 hC
  have h4 := abs_le.1 hD
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1.1 hτ0, mul_le_mul_of_nonneg_left h1.2 hτ0,
    mul_le_mul_of_nonneg_left h2.1 hμ0, mul_le_mul_of_nonneg_left h2.2 hμ0,
    mul_le_mul_of_nonneg_left h3.1 (sub_nonneg.2 hτ1), mul_le_mul_of_nonneg_left h3.2 (sub_nonneg.2 hτ1),
    mul_le_mul_of_nonneg_left h4.1 (sub_nonneg.2 hμ1), mul_le_mul_of_nonneg_left h4.2 (sub_nonneg.2 hμ1)]

/-- Continuity of the wobbling function. -/
theorem continuous_wob (hg : IsLip g L) (hs : SmallL T L) : Continuous (wob T g L) := by
  have ht := continuous_tilt hg hs
  have hgc := hg.continuous
  have hr : ∀ a : ℂ, Continuous fun θ : ℝ => rot θ * a :=
    fun a => continuous_rot.mul continuous_const
  have hfoot : ∀ a : ℂ, Continuous fun θ : ℝ => foot (rot θ * a) (tilt T g L θ) :=
    fun a => continuous_foot.comp ((hr a).prodMk ht)
  have hdot : ∀ a : ℂ, Continuous fun θ : ℝ => dot (rot θ * a) (tilt T g L θ) :=
    fun a => continuous_dot.comp ((hr a).prodMk ht)
  unfold wob resid cAC
  exact (((hgc.comp (hfoot T.A)).sub (hdot T.A)).add (hdot T.B)).sub (hgc.comp (hfoot T.B))

end Table

end Wobbly
