import Wobbly.Basic

/-!
# The equal hovering position (Proposition 4.4 of the paper)

A table is given by the positions `A, B, C, D` of its feet in the frame of the table.
The position `(θ, q, c)` of the table has rotation angle `θ`, tilt `q` and height `c`; the foot
which is at `a` in the frame of the table is then at the horizontal position
`foot (rot θ * a) q = rot θ * a - Φ (rot θ * a) q` and at the height `c + dot (rot θ * a) q`
(Lemma 4.1).

The tilt of the equal hovering position is the fixed point of the map `Q`; we show that it
exists, is unique, is bounded by `L K` and depends continuously on `θ`.
-/

noncomputable section

open Complex Metric

namespace Wobbly

/-- The unit vector in the direction of `z`. -/
def unit (z : ℂ) : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) * z

lemma norm_unit {z : ℂ} (hz : z ≠ 0) : ‖unit z‖ = 1 := by
  rw [unit, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

lemma norm_mul_unit (z : ℂ) (hz : z ≠ 0) : ((‖z‖ : ℝ) : ℂ) * unit z = z := by
  rw [unit, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz), ofReal_one,
    one_mul]

/-- A terrain `g` is `L`-Lipschitz. -/
def IsLip (g : ℂ → ℝ) (L : ℝ) : Prop := ∀ x y, |g x - g y| ≤ L * ‖x - y‖

lemma IsLip.nonneg {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) : 0 ≤ L := by
  have h := hg 0 1
  have h1 : ‖(0 : ℂ) - 1‖ = 1 := by simp
  rw [h1, mul_one] at h
  exact le_trans (abs_nonneg _) h

lemma IsLip.continuous {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) : Continuous g := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (|L| + 1), by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq, dist_eq_norm] at *
  calc |g y - g x| ≤ L * ‖y - x‖ := hg y x
    _ ≤ |L| * ‖y - x‖ := by gcongr; exact le_abs_self L
    _ ≤ (|L| + 1) * ‖y - x‖ := by gcongr; linarith
    _ < (|L| + 1) * (ε / (|L| + 1)) := by gcongr
    _ = ε := by field_simp

/-- Horizontal position of the foot which is at `u` (after rotation) when the tilt is `q`. -/
def foot (u q : ℂ) : ℂ := u - Φ u q

lemma continuous_foot : Continuous fun p : ℂ × ℂ => foot p.1 p.2 := by
  unfold foot
  exact continuous_fst.sub continuous_Φ

lemma foot_sub_foot (u v q : ℂ) : foot u q - foot v q = (u - v) - Φ (u - v) q := by
  rw [foot, foot, ← Φ_sub_left]; ring

lemma foot_sub_foot_same (v q q' : ℂ) : foot v q - foot v q' = -(Φ v q - Φ v q') := by
  unfold foot; ring

lemma norm_foot_sub_foot_le {u v q : ℂ} (hq : ‖q‖ ≤ 1) : ‖foot u q - foot v q‖ ≤ ‖u - v‖ := by
  rw [foot_sub_foot]; exact norm_sub_Φ_le hq

/-- A table: its four feet `A, B, C, D` (in cyclic order, in the frame of the table), at distance
at most `r` from the centre, with non-parallel diagonals. -/
structure Table where
  A : ℂ
  B : ℂ
  C : ℂ
  D : ℂ
  r : ℝ
  normA : ‖A‖ ≤ r
  normB : ‖B‖ ≤ r
  normC : ‖C‖ ≤ r
  normD : ‖D‖ ≤ r
  AC_ne : A ≠ C
  BD_ne : B ≠ D
  not_parallel : |dot (unit (A - C)) (unit (B - D))| < 1

namespace Table

variable (T : Table)

/-- Lengths of the diagonals. -/
def d₁ : ℝ := ‖T.A - T.C‖
def d₂ : ℝ := ‖T.B - T.D‖
def dmin : ℝ := min T.d₁ T.d₂
/-- Unit vectors of the diagonals. -/
def e₁ : ℂ := unit (T.A - T.C)
def e₂ : ℂ := unit (T.B - T.D)
/-- `γ = |cos φ|`, where `φ` is the angle between the diagonals. -/
def γ : ℝ := |dot T.e₁ T.e₂|
/-- `K = 1 / sin (φ/2)`, i.e. `K² = 2 / (1 - |cos φ|)`. -/
def K : ℝ := Real.sqrt (2 / (1 - T.γ))

lemma d₁_pos : 0 < T.d₁ := norm_pos_iff.2 (sub_ne_zero.2 T.AC_ne)
lemma d₂_pos : 0 < T.d₂ := norm_pos_iff.2 (sub_ne_zero.2 T.BD_ne)
lemma dmin_pos : 0 < T.dmin := lt_min T.d₁_pos T.d₂_pos
lemma dmin_le_d₁ : T.dmin ≤ T.d₁ := min_le_left _ _
lemma dmin_le_d₂ : T.dmin ≤ T.d₂ := min_le_right _ _
lemma γ_lt_one : T.γ < 1 := T.not_parallel
lemma K_nonneg : 0 ≤ T.K := Real.sqrt_nonneg _
lemma r_nonneg : 0 ≤ T.r := le_trans (norm_nonneg _) T.normA

lemma norm_e₁ : ‖T.e₁‖ = 1 := norm_unit (sub_ne_zero.2 T.AC_ne)
lemma norm_e₂ : ‖T.e₂‖ = 1 := norm_unit (sub_ne_zero.2 T.BD_ne)

lemma A_sub_C : T.A - T.C = (T.d₁ : ℂ) * T.e₁ := (norm_mul_unit _ (sub_ne_zero.2 T.AC_ne)).symm
lemma B_sub_D : T.B - T.D = (T.d₂ : ℂ) * T.e₂ := (norm_mul_unit _ (sub_ne_zero.2 T.BD_ne)).symm

/-! ### The rotated table -/

lemma norm_rot_e₁ (θ : ℝ) : ‖rot θ * T.e₁‖ = 1 := by rw [norm_rot_mul, T.norm_e₁]
lemma norm_rot_e₂ (θ : ℝ) : ‖rot θ * T.e₂‖ = 1 := by rw [norm_rot_mul, T.norm_e₂]
lemma γ_rot (θ : ℝ) : |dot (rot θ * T.e₁) (rot θ * T.e₂)| = T.γ := by rw [dot_rot]; rfl
lemma γ_rot_lt_one (θ : ℝ) : |dot (rot θ * T.e₁) (rot θ * T.e₂)| < 1 := by
  rw [T.γ_rot]; exact T.γ_lt_one
lemma det_rot_ne (θ : ℝ) : det2 (rot θ * T.e₁) (rot θ * T.e₂) ≠ 0 :=
  det2_ne_zero (T.norm_rot_e₁ θ) (T.norm_rot_e₂ θ) (T.γ_rot_lt_one θ)

lemma norm_rot_A_sub_C (θ : ℝ) : ‖rot θ * T.A - rot θ * T.C‖ = T.d₁ := by
  rw [← mul_sub, norm_rot_mul]; rfl
lemma norm_rot_B_sub_D (θ : ℝ) : ‖rot θ * T.B - rot θ * T.D‖ = T.d₂ := by
  rw [← mul_sub, norm_rot_mul]; rfl

/-- `u_A - u_C = d₁ (rot θ e₁)`. -/
lemma rot_A_sub_C (θ : ℝ) : rot θ * T.A - rot θ * T.C = (T.d₁ : ℂ) * (rot θ * T.e₁) := by
  rw [← mul_sub, T.A_sub_C]; ring
lemma rot_B_sub_D (θ : ℝ) : rot θ * T.B - rot θ * T.D = (T.d₂ : ℂ) * (rot θ * T.e₂) := by
  rw [← mul_sub, T.B_sub_D]; ring

/-! ### The map `Q` -/

/-- The map `Q_θ` of the proof of Proposition 4.4: the fixed points of `Q_θ` are the tilts for
which `A, C` are equally high above the ground and `B, D` are equally high above the ground. -/
def Q (g : ℂ → ℝ) (θ : ℝ) (q : ℂ) : ℂ :=
  solve2 (rot θ * T.e₁) (rot θ * T.e₂)
    ((g (foot (rot θ * T.A) q) - g (foot (rot θ * T.C) q)) / T.d₁)
    ((g (foot (rot θ * T.B) q) - g (foot (rot θ * T.D) q)) / T.d₂)

variable {T}
variable {g : ℂ → ℝ} {L : ℝ}

/-- `Q_θ` maps the unit disc into the disc of radius `L K`. -/
lemma norm_Q_le (hg : IsLip g L) (θ : ℝ) {q : ℂ} (hq : ‖q‖ ≤ 1) : ‖T.Q g θ q‖ ≤ T.K * L := by
  have hα : |(g (foot (rot θ * T.A) q) - g (foot (rot θ * T.C) q)) / T.d₁| ≤ L := by
    rw [abs_div, abs_of_pos T.d₁_pos, div_le_iff₀ T.d₁_pos]
    calc |g (foot (rot θ * T.A) q) - g (foot (rot θ * T.C) q)|
        ≤ L * ‖foot (rot θ * T.A) q - foot (rot θ * T.C) q‖ := hg _ _
      _ ≤ L * T.d₁ := by
          have hL : 0 ≤ L := by
            have := hg 0 1
            have h1 : ‖(0 : ℂ) - 1‖ = 1 := by simp
            rw [h1] at this; linarith [abs_nonneg (g 0 - g 1)]
          gcongr
          rw [← T.norm_rot_A_sub_C θ]; exact norm_foot_sub_foot_le hq
  have hβ : |(g (foot (rot θ * T.B) q) - g (foot (rot θ * T.D) q)) / T.d₂| ≤ L := by
    rw [abs_div, abs_of_pos T.d₂_pos, div_le_iff₀ T.d₂_pos]
    calc |g (foot (rot θ * T.B) q) - g (foot (rot θ * T.D) q)|
        ≤ L * ‖foot (rot θ * T.B) q - foot (rot θ * T.D) q‖ := hg _ _
      _ ≤ L * T.d₂ := by
          have hL : 0 ≤ L := by
            have := hg 0 1
            have h1 : ‖(0 : ℂ) - 1‖ = 1 := by simp
            rw [h1] at this; linarith [abs_nonneg (g 0 - g 1)]
          gcongr
          rw [← T.norm_rot_B_sub_D θ]; exact norm_foot_sub_foot_le hq
  have := norm_solve2_le (T.norm_rot_e₁ θ) (T.norm_rot_e₂ θ) (T.γ_rot_lt_one θ) hα hβ
  rwa [T.γ_rot] at this

/-- The Lipschitz constant of Lemma 4.2, `ψ(t) = 2t/(1+c) + t³/(c(1+c)²)` with `c = √(1-t²)`. -/
def ψ (t : ℝ) : ℝ :=
  2 * t / (1 + Real.sqrt (1 - t ^ 2)) +
    t ^ 3 / (Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) ^ 2)

lemma ψ_nonneg {t : ℝ} (ht0 : 0 ≤ t) : 0 ≤ ψ t := by unfold ψ; positivity

/-- `Q_θ` is Lipschitz on the disc of radius `t < 1`. -/
lemma norm_Q_sub_le (hg : IsLip g L) (hL : 0 ≤ L) (θ : ℝ) {q q' : ℂ} {t : ℝ} (hq : ‖q‖ ≤ t)
    (hq' : ‖q'‖ ≤ t) (ht : t < 1) :
    ‖T.Q g θ q - T.Q g θ q'‖ ≤ T.K * (2 * L * T.r * ψ t / T.dmin * ‖q - q'‖) := by
  have ht0 : 0 ≤ t := le_trans (norm_nonneg _) hq
  have hd := T.det_rot_ne θ
  -- the difference of the right-hand sides for the pair of feet `(a, b)` of a diagonal of length `d`
  have key : ∀ (a b : ℂ) (d : ℝ), ‖a‖ ≤ T.r → ‖b‖ ≤ T.r → 0 < d → T.dmin ≤ d →
      |(g (foot (rot θ * a) q) - g (foot (rot θ * b) q)) / d -
          (g (foot (rot θ * a) q') - g (foot (rot θ * b) q')) / d| ≤
        2 * L * T.r * ψ t / T.dmin * ‖q - q'‖ := by
    intro a b d ha hb hd0 hdmin
    have ha' : ‖rot θ * a‖ ≤ T.r := by rw [norm_rot_mul]; exact ha
    have hb' : ‖rot θ * b‖ ≤ T.r := by rw [norm_rot_mul]; exact hb
    have hΦa := norm_Φ_sub_le ha' hq hq' ht
    have hΦb := norm_Φ_sub_le hb' hq hq' ht
    have e : (g (foot (rot θ * a) q) - g (foot (rot θ * b) q)) / d -
        (g (foot (rot θ * a) q') - g (foot (rot θ * b) q')) / d =
        ((g (foot (rot θ * a) q) - g (foot (rot θ * a) q')) -
          (g (foot (rot θ * b) q) - g (foot (rot θ * b) q'))) / d := by ring
    have hfa : ‖foot (rot θ * a) q - foot (rot θ * a) q'‖ =
        ‖Φ (rot θ * a) q - Φ (rot θ * a) q'‖ := by rw [foot_sub_foot_same, norm_neg]
    have hfb : ‖foot (rot θ * b) q - foot (rot θ * b) q'‖ =
        ‖Φ (rot θ * b) q - Φ (rot θ * b) q'‖ := by rw [foot_sub_foot_same, norm_neg]
    rw [e, abs_div, abs_of_pos hd0]
    have hnum : |(g (foot (rot θ * a) q) - g (foot (rot θ * a) q')) -
        (g (foot (rot θ * b) q) - g (foot (rot θ * b) q'))| ≤ 2 * L * T.r * ψ t * ‖q - q'‖ := by
      calc _ ≤ |g (foot (rot θ * a) q) - g (foot (rot θ * a) q')| +
            |g (foot (rot θ * b) q) - g (foot (rot θ * b) q')| := abs_sub _ _
        _ ≤ L * ‖foot (rot θ * a) q - foot (rot θ * a) q'‖ +
            L * ‖foot (rot θ * b) q - foot (rot θ * b) q'‖ := add_le_add (hg _ _) (hg _ _)
        _ ≤ L * (T.r * ψ t * ‖q - q'‖) + L * (T.r * ψ t * ‖q - q'‖) := by
            rw [hfa, hfb]
            gcongr
            · exact hΦa
            · exact hΦb
        _ = 2 * L * T.r * ψ t * ‖q - q'‖ := by ring
    have hpos : 0 ≤ 2 * L * T.r * ψ t * ‖q - q'‖ := by
      have := ψ_nonneg ht0; have := T.r_nonneg; positivity
    calc _ ≤ 2 * L * T.r * ψ t * ‖q - q'‖ / d := by gcongr
      _ ≤ 2 * L * T.r * ψ t * ‖q - q'‖ / T.dmin :=
          div_le_div_of_nonneg_left hpos T.dmin_pos hdmin
      _ = 2 * L * T.r * ψ t / T.dmin * ‖q - q'‖ := by ring
  unfold Q
  rw [solve2_sub hd]
  have := norm_solve2_le (T.norm_rot_e₁ θ) (T.norm_rot_e₂ θ) (T.γ_rot_lt_one θ)
    (key T.A T.C T.d₁ T.normA T.normC T.d₁_pos T.dmin_le_d₁)
    (key T.B T.D T.d₂ T.normB T.normD T.d₂_pos T.dmin_le_d₂)
  rwa [T.γ_rot] at this

/-! ### Existence, uniqueness and continuity (Proposition 4.4) -/

/-- The smallness assumption (4.3) of the paper (stated in Proposition 4.4). -/
structure SmallL (T : Table) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  hK : L * T.K ≤ 1 / 2
  hlam : 4 / Real.sqrt 3 * (T.r / T.dmin) * (L * T.K) ^ 2 < 1

/-- The contraction constant of `Q_θ` on the disc of radius `L K`. -/
def lam (T : Table) (L : ℝ) : ℝ := T.K * (2 * L * T.r * ψ (L * T.K) / T.dmin)

lemma lam_nonneg (hs : SmallL T L) : 0 ≤ lam T L := by
  unfold lam
  have := ψ_nonneg (mul_nonneg hs.nonneg T.K_nonneg)
  have := T.r_nonneg; have := T.dmin_pos; have := T.K_nonneg; have := hs.nonneg
  positivity

lemma lam_lt_one (hs : SmallL T L) : lam T L < 1 := by
  have hρ0 : 0 ≤ L * T.K := mul_nonneg hs.nonneg T.K_nonneg
  have hψ := psi_le hρ0 hs.hK
  have hψ' : ψ (L * T.K) ≤ 2 / Real.sqrt 3 * (L * T.K) := hψ
  have h : lam T L ≤ 4 / Real.sqrt 3 * (T.r / T.dmin) * (L * T.K) ^ 2 := by
    unfold lam
    have := T.r_nonneg; have := T.dmin_pos; have := T.K_nonneg; have := hs.nonneg
    calc T.K * (2 * L * T.r * ψ (L * T.K) / T.dmin)
        ≤ T.K * (2 * L * T.r * (2 / Real.sqrt 3 * (L * T.K)) / T.dmin) := by gcongr
      _ = 4 / Real.sqrt 3 * (T.r / T.dmin) * (L * T.K) ^ 2 := by ring
  linarith [hs.hlam]

lemma LK_lt_one (hs : SmallL T L) : L * T.K < 1 := by linarith [hs.hK]

/-- `Q_θ` is a `lam`-contraction on the closed disc of radius `L K`. -/
lemma Q_contract (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) {q q' : ℂ}
    (hq : ‖q‖ ≤ L * T.K) (hq' : ‖q'‖ ≤ L * T.K) :
    ‖T.Q g θ q - T.Q g θ q'‖ ≤ lam T L * ‖q - q'‖ := by
  have := norm_Q_sub_le (T := T) hg hs.nonneg θ hq hq' (LK_lt_one hs)
  unfold lam
  calc ‖T.Q g θ q - T.Q g θ q'‖
      ≤ T.K * (2 * L * T.r * ψ (L * T.K) / T.dmin * ‖q - q'‖) := this
    _ = T.K * (2 * L * T.r * ψ (L * T.K) / T.dmin) * ‖q - q'‖ := by ring

/-- Proposition 4.4, existence: `Q_θ` has a fixed point in the disc of radius `L K`. -/
lemma exists_fixed (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    ∃ q : ℂ, ‖q‖ ≤ L * T.K ∧ T.Q g θ q = q := by
  set ρ := L * T.K with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg hs.nonneg T.K_nonneg
  have hmaps : Set.MapsTo (T.Q g θ) (closedBall (0 : ℂ) ρ) (closedBall (0 : ℂ) ρ) := by
    intro q hq
    rw [mem_closedBall, dist_zero_right] at hq ⊢
    have h1 : ‖q‖ ≤ 1 := le_trans hq (LK_lt_one hs).le
    have := norm_Q_le (T := T) hg θ h1
    linarith [mul_comm L T.K]
  have hcomplete : IsComplete (closedBall (0 : ℂ) ρ) := isClosed_closedBall.isComplete
  have hcontr : ContractingWith ⟨lam T L, lam_nonneg hs⟩ (hmaps.restrict (T.Q g θ) _ _) := by
    refine ⟨by exact_mod_cast lam_lt_one hs, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, Set.MapsTo.val_restrict_apply, dist_eq_norm]
    have hx := x.2; have hy := y.2
    rw [mem_closedBall, dist_zero_right] at hx hy
    exact Q_contract hg hs θ hx hy
  obtain ⟨q, hq, hfix, -⟩ := hcontr.exists_fixedPoint' hcomplete hmaps
    (mem_closedBall_self hρ0) (edist_ne_top _ _)
  rw [mem_closedBall, dist_zero_right] at hq
  exact ⟨q, hq, hfix⟩

/-- Proposition 4.4, uniqueness: a fixed point in the open unit disc is in the disc of radius
`L K`, and there is at most one such fixed point. -/
lemma fixed_unique (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) {q q' : ℂ}
    (hq : ‖q‖ < 1) (hfix : T.Q g θ q = q) (hq' : ‖q'‖ < 1) (hfix' : T.Q g θ q' = q') : q = q' := by
  have hq1 : ‖q‖ ≤ L * T.K := by
    rw [← hfix]; have := norm_Q_le (T := T) hg θ hq.le; linarith [mul_comm L T.K]
  have hq1' : ‖q'‖ ≤ L * T.K := by
    rw [← hfix']; have := norm_Q_le (T := T) hg θ hq'.le; linarith [mul_comm L T.K]
  have h := Q_contract hg hs θ hq1 hq1'
  rw [hfix, hfix'] at h
  have hl := lam_lt_one hs
  have : ‖q - q'‖ ≤ 0 := by nlinarith [norm_nonneg (q - q')]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

open Classical in
/-- The tilt of the equal hovering position (it is defined for all `θ`; its properties hold under
the assumptions of Proposition 4.4). -/
def tilt (T : Table) (g : ℂ → ℝ) (L : ℝ) (θ : ℝ) : ℂ :=
  if h : ∃ q : ℂ, ‖q‖ ≤ L * T.K ∧ T.Q g θ q = q then Classical.choose h else 0

lemma tilt_spec (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    ‖tilt T g L θ‖ ≤ L * T.K ∧ T.Q g θ (tilt T g L θ) = tilt T g L θ := by
  have h := exists_fixed (T := T) hg hs θ
  rw [tilt, dite_eq_left h]
  exact Classical.choose_spec h

lemma norm_tilt_le (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) : ‖tilt T g L θ‖ ≤ L * T.K :=
  (tilt_spec hg hs θ).1

lemma norm_tilt_lt_one (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) : ‖tilt T g L θ‖ < 1 :=
  lt_of_le_of_lt (norm_tilt_le hg hs θ) (LK_lt_one hs)

lemma Q_tilt (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) : T.Q g θ (tilt T g L θ) = tilt T g L θ :=
  (tilt_spec hg hs θ).2

/-- Proposition 4.4 (existence and uniqueness of the equal hovering tilt). -/
theorem existsUnique_tilt (hg : IsLip g L) (hs : SmallL T L) (θ : ℝ) :
    ∃! q : ℂ, ‖q‖ < 1 ∧ T.Q g θ q = q :=
  ⟨tilt T g L θ, ⟨norm_tilt_lt_one hg hs θ, Q_tilt hg hs θ⟩,
    fun _ hq => fixed_unique hg hs θ hq.1 hq.2 (norm_tilt_lt_one hg hs θ) (Q_tilt hg hs θ)⟩

/-- For a fixed tilt, `θ ↦ Q_θ(p)` is continuous. -/
lemma continuous_Q_apply (hg : IsLip g L) (p : ℂ) : Continuous fun θ => T.Q g θ p := by
  have hgc := hg.continuous
  have hfoot : ∀ a : ℂ, Continuous fun θ : ℝ => foot (rot θ * a) p := by
    intro a
    have hr : Continuous fun θ : ℝ => rot θ * a := continuous_rot.mul continuous_const
    exact continuous_foot.comp (hr.prodMk continuous_const)
  have hα : Continuous fun θ : ℝ =>
      (g (foot (rot θ * T.A) p) - g (foot (rot θ * T.C) p)) / T.d₁ :=
    ((hgc.comp (hfoot T.A)).sub (hgc.comp (hfoot T.C))).div_const _
  have hβ : Continuous fun θ : ℝ =>
      (g (foot (rot θ * T.B) p) - g (foot (rot θ * T.D) p)) / T.d₂ :=
    ((hgc.comp (hfoot T.B)).sub (hgc.comp (hfoot T.D))).div_const _
  have he₁ : Continuous fun θ : ℝ => rot θ * T.e₁ := continuous_rot.mul continuous_const
  have he₂ : Continuous fun θ : ℝ => rot θ * T.e₂ := continuous_rot.mul continuous_const
  exact continuous_solve2 he₁ he₂ hα hβ (fun θ => T.det_rot_ne θ)

/-- Proposition 4.4 (continuity of the equal hovering tilt in `θ`). -/
theorem continuous_tilt (hg : IsLip g L) (hs : SmallL T L) : Continuous (tilt T g L) := by
  rw [Metric.continuous_iff]
  intro θ₀ ε hε
  have hl := lam_lt_one hs
  have hl0 := lam_nonneg hs
  set p := tilt T g L θ₀ with hp
  have hcont := continuous_Q_apply (T := T) hg p
  rw [Metric.continuous_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont θ₀ (ε * (1 - lam T L)) (by nlinarith)
  refine ⟨δ, hδ, fun θ hθ => ?_⟩
  have h1 := hδ' θ hθ
  rw [dist_eq_norm] at h1 ⊢
  -- `tilt θ - p = (Q_θ(tilt θ) - Q_θ(p)) + (Q_θ(p) - Q_{θ₀}(p))`
  have hfixθ := Q_tilt hg hs θ
  have hfix₀ : T.Q g θ₀ p = p := Q_tilt hg hs θ₀
  have hc := Q_contract hg hs θ (norm_tilt_le hg hs θ) (norm_tilt_le hg hs θ₀)
  have e : tilt T g L θ - p = (T.Q g θ (tilt T g L θ) - T.Q g θ p) + (T.Q g θ p - T.Q g θ₀ p) := by
    rw [hfixθ, hfix₀]; ring
  have h2 : ‖tilt T g L θ - p‖ ≤ lam T L * ‖tilt T g L θ - p‖ + ‖T.Q g θ p - T.Q g θ₀ p‖ := by
    calc ‖tilt T g L θ - p‖ =
          ‖(T.Q g θ (tilt T g L θ) - T.Q g θ p) + (T.Q g θ p - T.Q g θ₀ p)‖ := by rw [← e]
      _ ≤ ‖T.Q g θ (tilt T g L θ) - T.Q g θ p‖ + ‖T.Q g θ p - T.Q g θ₀ p‖ := norm_add_le _ _
      _ ≤ lam T L * ‖tilt T g L θ - p‖ + ‖T.Q g θ p - T.Q g θ₀ p‖ := add_le_add hc le_rfl
  have h3 : (1 - lam T L) * ‖tilt T g L θ - p‖ < (1 - lam T L) * ε := by nlinarith
  exact lt_of_mul_lt_mul_left h3 (by linarith)

end Table

end Wobbly
