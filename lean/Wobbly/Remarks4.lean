import Wobbly.Degenerate
import Wobbly.AxisLocal
import Wobbly.Coordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The remarks of §4 of the paper

**Remark 4.5.**
* (a) For a square table, `K = √2`, `d_min = 2r` and (4.3) reads `L ≤ 1/(2√2)`
  (`square_K`, `square_dmin`, `square_smallL_iff`); the corresponding maximal slope is
  `arctan (1/(2√2)) = arcsin (1/3)`, between `19.4°` and `19.5°` (`square_slope`,
  `square_slope_deg`).
* (b) (4.3) is symmetric in the two diagonals (`Table.swap`, `smallL_swap_iff`), so Proposition 4.4
  also gives the equal hovering position with respect to `BD` (`existsUnique_hover_BD`).
* (c) is a comment on the hypotheses: `Table` and `SmallL` involve neither equal diagonals nor
  rationality.

**Remark 4.12.**
* The Fourier coefficients of `F₀`: `∫ e^{-ikθ} F₀(θ) dθ = -m(k) G_k` (`integral_F₀v`), so that
  `F₀ ≡ 0` iff `m(k) G_k = 0` for every `k` (`F₀v_eq_zero_iff`). (`m(0) = m(±1) = 0` and the odd
  modes of rectangles are `Feet.m_zero`, `Feet.m_one`, `Feet.m_odd_of_rectangle`.)
* The quadratic form `qᵀ M q` of the heuristic (`Feet.Mq`) is `-½ Re(conj(m(2)) q²)` (`Mq_eq`); it
  has trace `0` (`Mq_add_Mq_I`), so it is not definite (`Mq_not_pos`, `Mq_not_neg`).
* The inequality `|v₁² - v₂²| ≥ ||v₁|² - |v₂|²|` (`abs_normSq_sub_le`), and: a quadratic form of
  trace `0` vanishes somewhere on every ellipse `v₁ e^{iφ} + v₂ e^{-iφ}` centred at `0`
  (`exists_re_mul_sq_eq_zero`). If `g₁ = Re(z^k)` on the circle for a degenerate mode `k`, the
  idealised tilt, seen in the frame of the table, describes such an ellipse, so `qᵀ M q` vanishes
  for some angle (`exists_Mq_idealTilt_eq_zero`).
* The heuristic second order expansion `w_AC ≈ -(rβ/2) qᵀ M q` itself is not formalised (the
  paper presents it as a heuristic), nor is the remark on random terrains.
-/

noncomputable section

open Complex ComplexConjugate MeasureTheory

namespace Wobbly

/-! ### Remark 4.5 (a): the square -/

/-- The square table with feet `r, ir, -r, -ir`. -/
def sqTable (r : ℝ) (hr : 0 < r) : Table where
  A := r
  B := r * I
  C := -r
  D := -(r * I)
  r := r
  normA := by simp [abs_of_pos hr]
  normB := by simp [abs_of_pos hr]
  normC := by simp [abs_of_pos hr]
  normD := by simp [abs_of_pos hr]
  AC_ne := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  BD_ne := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  not_parallel := by
    simp [unit, dot]

section square

variable {r : ℝ} (hr : 0 < r)

lemma square_d₁ : (sqTable r hr).d₁ = 2 * r := by
  simp only [Table.d₁, sqTable, sub_neg_eq_add]
  rw [show (r : ℂ) + r = ((2 * r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

lemma square_d₂ : (sqTable r hr).d₂ = 2 * r := by
  simp only [Table.d₂, sqTable, sub_neg_eq_add]
  rw [show (r : ℂ) * I + r * I = ((2 * r : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg (by linarith)]

lemma square_dmin : (sqTable r hr).dmin = 2 * r := by
  rw [Table.dmin, square_d₁, square_d₂, min_self]

lemma square_γ : (sqTable r hr).γ = 0 := by
  simp [Table.γ, Table.e₁, Table.e₂, unit, sqTable, dot]

lemma square_K : (sqTable r hr).K = Real.sqrt 2 := by
  rw [Table.K, square_γ]; norm_num

/-- **Remark 4.5 (a)**: for a square table, (4.3) reads `L ≤ 1/(2√2)`. -/
theorem square_smallL_iff (L : ℝ) :
    Table.SmallL (sqTable r hr) L ↔ 0 ≤ L ∧ L ≤ 1 / (2 * Real.sqrt 2) := by
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hrr : (sqTable r hr).r = r := rfl
  constructor
  · rintro ⟨h0, hK, -⟩
    rw [square_K] at hK
    refine ⟨h0, ?_⟩
    rw [le_div_iff₀ (by positivity)]
    linarith
  · rintro ⟨h0, hL⟩
    have hLK : L * Real.sqrt 2 ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hL
      linarith
    refine ⟨h0, by rw [square_K]; exact hLK, ?_⟩
    rw [square_K, square_dmin, hrr, show r / (2 * r) = 1 / 2 by field_simp]
    have hL2 : (L * Real.sqrt 2) ^ 2 ≤ 1 / 4 := by
      have := mul_nonneg h0 h2.le
      nlinarith
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith

/-- The maximal slope of Remark 4.5 (a): `arctan (1/(2√2)) = arcsin (1/3)`. -/
theorem square_slope : Real.arctan (1 / (2 * Real.sqrt 2)) = Real.arcsin (1 / 3) := by
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Real.arctan_eq_arcsin]
  congr 1
  have : Real.sqrt (1 + (1 / (2 * Real.sqrt 2)) ^ 2) = 3 / (2 * Real.sqrt 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    field_simp
    rw [hs2]; norm_num
  rw [this]
  field_simp

end square

lemma sin_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x - x ^ 3 / 6 - x ^ 5 / 100 ≤ Real.sin x := by
  have := Real.sin_bound (show |x| ≤ 1 by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  linarith [neg_abs_le (Real.sin x - (x - x ^ 3 / 6))]

lemma sin_le' {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
  have := Real.sin_bound (show |x| ≤ 1 by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  linarith [le_abs_self (Real.sin x - (x - x ^ 3 / 6))]

/-- The maximal slope of Remark 4.5 (a) is between `19.4°` and `19.5°`. -/
theorem square_slope_deg :
    19.4 < Real.arctan (1 / (2 * Real.sqrt 2)) * (180 / Real.pi) ∧
      Real.arctan (1 / (2 * Real.sqrt 2)) * (180 / Real.pi) < 19.5 := by
  rw [square_slope]
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hpos : 0 < Real.pi := Real.pi_pos
  constructor
  · -- `sin 19.4° < 1/3`
    set x := 19.4 * Real.pi / 180 with hx
    have hx0 : 0 ≤ x := by positivity
    have hxl : 0.33859 < x := by rw [hx]; linarith
    have hxu : x < 0.33860 := by rw [hx]; linarith
    have h2 : 0.11464 < x ^ 2 := by nlinarith
    have h3 : 0.038816 < x ^ 3 := by nlinarith
    have h2u : x ^ 2 < 0.11466 := by nlinarith
    have h4u : x ^ 4 < 0.013147 := by nlinarith
    have h5 : x ^ 5 < 0.0045 := by nlinarith
    have hs : Real.sin x < 1 / 3 := by
      have := sin_le' hx0 (by linarith)
      linarith
    have : x < Real.arcsin (1 / 3) := by
      rw [Real.lt_arcsin_iff_sin_lt' ⟨by linarith, by linarith⟩]
      exact hs
    calc (19.4 : ℝ) = x * (180 / Real.pi) := by rw [hx]; field_simp
      _ < Real.arcsin (1 / 3) * (180 / Real.pi) := by gcongr
  · -- `1/3 < sin 19.5°`
    set x := 19.5 * Real.pi / 180 with hx
    have hx0 : 0 ≤ x := by positivity
    have hxl : 0.34033 < x := by rw [hx]; linarith
    have hxu : x < 0.34034 := by rw [hx]; linarith
    have h2 : x ^ 2 < 0.11584 := by nlinarith
    have h3 : x ^ 3 < 0.039425 := by nlinarith
    have h5 : x ^ 5 < 0.0046 := by nlinarith
    have hs : 1 / 3 < Real.sin x := by
      have := sin_ge hx0 (by linarith)
      linarith
    have : Real.arcsin (1 / 3) < x := by
      rw [Real.arcsin_lt_iff_lt_sin' ⟨by linarith, by linarith⟩]
      exact hs
    calc Real.arcsin (1 / 3) * (180 / Real.pi) < x * (180 / Real.pi) := by gcongr
      _ = 19.5 := by rw [hx]; field_simp

/-! ### Remark 4.5 (b): the two diagonals play the same role -/

/-- The table with the roles of the diagonals exchanged: `(A, B, C, D) ↦ (B, C, D, A)`. -/
def Table.swap (T : Table) : Table where
  A := T.B
  B := T.C
  C := T.D
  D := T.A
  r := T.r
  normA := T.normB
  normB := T.normC
  normC := T.normD
  normD := T.normA
  AC_ne := T.BD_ne
  BD_ne := T.AC_ne.symm
  not_parallel := by
    have hu : unit (T.C - T.A) = -unit (T.A - T.C) := by
      simp only [unit, ← neg_sub T.A T.C, norm_neg, mul_neg]
    have hd : ∀ u v : ℂ, dot u (-v) = -dot u v := fun u v => by simp [dot]; ring
    rw [hu, hd, abs_neg, dot_comm]
    exact T.not_parallel

lemma Table.swap_K (T : Table) : T.swap.K = T.K := by
  have hu : unit (T.C - T.A) = -unit (T.A - T.C) := by
    simp only [unit, ← neg_sub T.A T.C, norm_neg, mul_neg]
  have hd : ∀ u v : ℂ, dot u (-v) = -dot u v := fun u v => by simp [dot]; ring
  simp only [Table.K, Table.γ, Table.e₁, Table.e₂, Table.swap]
  rw [hu, hd, abs_neg, dot_comm]

lemma Table.swap_dmin (T : Table) : T.swap.dmin = T.dmin := by
  simp only [Table.dmin, Table.d₁, Table.d₂, Table.swap]
  rw [← neg_sub T.A T.C, norm_neg, min_comm]

/-- **Remark 4.5 (b)**: (4.3) is symmetric in the two diagonals. -/
theorem smallL_swap_iff (T : Table) (L : ℝ) : Table.SmallL T.swap L ↔ Table.SmallL T L := by
  have hr : T.swap.r = T.r := rfl
  constructor <;> rintro ⟨h0, h1, h2⟩ <;>
    exact ⟨h0, by simpa [Table.swap_K] using h1, by simpa [Table.swap_K, Table.swap_dmin, hr] using h2⟩

/-- **Remark 4.5 (b)**: under (4.3), there is a unique equal hovering position with respect to
`BD`: the feet `B`, `D` on the ground and `C`, `A` at the same height (Proposition 4.4 for the
table `T.swap`). -/
theorem existsUnique_hover_BD (T : Table) {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) (hs : Table.SmallL T L)
    (θ : ℝ) : ∃! q : ℂ, ‖q‖ < 1 ∧ T.swap.Q g θ q = q :=
  Table.existsUnique_tilt (T := T.swap) hg ((smallL_swap_iff T L).2 hs) θ

/-! ### Remark 4.12: the Fourier coefficients of `F₀` -/

section fourier

variable {r : ℝ}

open Axis in
/-- The `k`-th Fourier coefficient of `F₀` is `-m(k) G_k`. -/
lemma integral_F₀v (F : Feet) {g : ℂ → ℝ} (hg : Continuous g) (v : ℂ) (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * θ) * (F₀v F r g v θ : ℂ) =
      -(F.m k * γR r k g v) := by
  have ci : ∀ e : ℂ, IntervalIntegrable
      (fun θ : ℝ => rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * e)) : ℂ)) volume 0 (2 * Real.pi) :=
    fun e => ((continuous_rotk k).mul (Complex.continuous_ofReal.comp (hg.comp
      (continuous_const.add (continuous_const.mul (continuous_rot.mul continuous_const))))))
        |>.intervalIntegrable _ _
  have e : ∀ θ : ℝ, rot (-(k : ℝ) * θ) * (F₀v F r g v θ : ℂ) =
      (F.τ : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.A)) : ℂ))
      + ((1 - F.τ : ℝ) : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.C)) : ℂ))
      - (F.μ : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.B)) : ℂ))
      - ((1 - F.μ : ℝ) : ℂ) * (rot (-(k : ℝ) * θ) * (g (v + r * (rot θ * F.D)) : ℂ)) := by
    intro θ; simp only [F₀v]; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_shift k v _ F.nA, integral_shift k v _ F.nB, integral_shift k v _ F.nC,
    integral_shift k v _ F.nD]
  · simp only [Feet.m]; ring
  all_goals first
    | exact (ci _).const_mul _
    | exact ((ci _).const_mul _).add ((ci _).const_mul _)
    | exact (((ci _).const_mul _).add ((ci _).const_mul _)).sub ((ci _).const_mul _)

open Axis in
/-- **Remark 4.12**: `F₀ ≡ 0` if and only if `m(k) G_k = 0` for every `k ≥ 0`, i.e. if and only if
the terrain on the circle only has degenerate Fourier modes. -/
theorem F₀v_eq_zero_iff (F : Feet) {g : ℂ → ℝ} (hg : Continuous g) (v : ℂ) :
    (∀ θ, F₀v F r g v θ = 0) ↔ ∀ k : ℕ, F.m k * γR r k g v = 0 := by
  refine ⟨fun h k => m_mul_γR_eq_zero F hg h k, fun h θ => ?_⟩
  set ψ : ℝ → ℂ := fun θ => (F₀v F r g v θ : ℂ) with hψ
  have hc : Continuous ψ := by
    have hr : ∀ a : ℂ, Continuous fun θ : ℝ => g (v + r * (rot θ * a)) :=
      fun a => hg.comp (continuous_const.add (continuous_const.mul (continuous_rot.mul
        continuous_const)))
    refine Complex.continuous_ofReal.comp ?_
    unfold F₀v
    exact ((((hr _).const_smul F.τ).add ((hr _).const_smul (1 - F.τ))).sub
      ((hr _).const_smul F.μ)).sub ((hr _).const_smul (1 - F.μ))
  have hp : Function.Periodic ψ (2 * Real.pi) := fun θ => by
    simp only [hψ, F₀v, rot_add', rot_two_pi, mul_one]
  have hk : ∀ k : ℕ, ∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) * ψ φ = 0 := fun k => by
    rw [hψ, integral_F₀v F hg v k, h k, neg_zero]
  have hcoef : ∀ n : ℤ, ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = 0 := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · simp_rw [mul_comm (ψ _)]
      exact_mod_cast hk k
    · have e : ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-((-(k : ℤ) : ℤ) : ℝ) * φ) =
          conj (∫ φ in (0 : ℝ)..2 * Real.pi, rot (-(k : ℝ) * φ) * ψ φ) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        congr 1; ext φ
        rw [map_mul, Axis.conj_rot, hψ]
        simp only [Complex.conj_ofReal]
        push_cast; ring_nf
      rw [e, hk k, map_zero]
  have h0 : ((F₀v F r g v θ : ℝ) : ℂ) = 0 := eq_zero_of_fourier hc hp hcoef θ
  exact_mod_cast h0

end fourier

/-! ### Remark 4.12: the quadratic form of the heuristic -/

/-- The quadratic form `qᵀ M q` of the heuristic of Remark 4.12, in the frame of the table:
`M = τ e_A e_Aᵀ + (1-τ) e_C e_Cᵀ - μ e_B e_Bᵀ - (1-μ) e_D e_Dᵀ`. -/
def Feet.Mq (F : Feet) (q : ℂ) : ℝ :=
  F.τ * dot F.A q ^ 2 + (1 - F.τ) * dot F.C q ^ 2 - F.μ * dot F.B q ^ 2 - (1 - F.μ) * dot F.D q ^ 2

lemma dot_sq_of_norm_one {e : ℂ} (he : ‖e‖ = 1) (q : ℂ) :
    dot e q ^ 2 = (‖q‖ ^ 2 + (conj e ^ 2 * q ^ 2).re) / 2 := by
  have h1 := sq_norm_eq e
  rw [he, one_pow] at h1
  rw [sq_norm_eq]
  simp only [dot, sq, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  linear_combination -(q.re * q.re + q.im * q.im) / 2 * h1

/-- `qᵀ M q = -½ Re(conj(m(2)) q²)`. -/
theorem Mq_eq (F : Feet) (q : ℂ) : F.Mq q = -(1 / 2) * (conj (F.m 2) * q ^ 2).re := by
  have e1 : conj (F.m 2) * q ^ 2 = -((F.τ : ℂ) * (conj F.A ^ 2 * q ^ 2)
      - (F.μ : ℂ) * (conj F.B ^ 2 * q ^ 2) + ((1 - F.τ : ℝ) : ℂ) * (conj F.C ^ 2 * q ^ 2)
      - ((1 - F.μ : ℝ) : ℂ) * (conj F.D ^ 2 * q ^ 2)) := by
    simp only [Feet.m, map_neg, map_sub, map_add, map_mul, map_pow, Complex.conj_ofReal]
    ring
  rw [e1]
  simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul]
  simp only [Feet.Mq, dot_sq_of_norm_one F.nA, dot_sq_of_norm_one F.nB, dot_sq_of_norm_one F.nC,
    dot_sq_of_norm_one F.nD]
  ring

/-- `M` has trace `0`: `qᵀ M q + (iq)ᵀ M (iq) = 0`. -/
theorem Mq_add_Mq_I (F : Feet) (q : ℂ) : F.Mq q + F.Mq (I * q) = 0 := by
  rw [Mq_eq, Mq_eq, show (I * q) ^ 2 = -q ^ 2 by rw [mul_pow, I_sq]; ring, mul_neg, Complex.neg_re]
  ring

/-- `M` is not positive definite. -/
theorem Mq_not_pos (F : Feet) : ¬ ∀ q : ℂ, q ≠ 0 → 0 < F.Mq q := fun h => by
  have h1 := h 1 one_ne_zero
  have h2 := h (I * 1) (by simp)
  have := Mq_add_Mq_I F 1
  linarith

/-- `M` is not negative definite. -/
theorem Mq_not_neg (F : Feet) : ¬ ∀ q : ℂ, q ≠ 0 → F.Mq q < 0 := fun h => by
  have h1 := h 1 one_ne_zero
  have h2 := h (I * 1) (by simp)
  have := Mq_add_Mq_I F 1
  linarith

/-- The inequality `|v₁² - v₂²| ≥ ||v₁|² - |v₂|²|` of Remark 4.12. -/
lemma abs_normSq_sub_le (v₁ v₂ : ℂ) : |‖v₁‖ ^ 2 - ‖v₂‖ ^ 2| ≤ ‖v₁ ^ 2 - v₂ ^ 2‖ := by
  rw [← norm_pow, ← norm_pow]
  exact abs_norm_sub_norm_le _ _

open Axis in
/-- A quadratic form of trace `0`, `q ↦ Re(β q²)`, vanishes somewhere on every ellipse
`φ ↦ v₁ e^{iφ} + v₂ e^{-iφ}` centred at `0`. -/
theorem exists_re_mul_sq_eq_zero (β v₁ v₂ : ℂ) :
    ∃ φ : ℝ, (β * (v₁ * rot φ + v₂ * rot (-φ)) ^ 2).re = 0 := by
  set C₀ : ℝ := (2 * β * v₁ * v₂).re with hC₀
  set W : ℂ := β * v₁ ^ 2 + conj (β * v₂ ^ 2) with hW
  -- along the ellipse, the form is `C₀ + Re(W e^{2iφ})`
  have key : ∀ φ : ℝ, (β * (v₁ * rot φ + v₂ * rot (-φ)) ^ 2).re = C₀ + (W * rot (2 * φ)).re := by
    intro φ
    have h1 : rot φ * conj (rot φ) = 1 := by rw [Axis.conj_rot, rot_mul_rot_neg]
    have e2 : rot (2 * φ) = rot φ ^ 2 := by rw [two_mul, rot_add', sq]
    have e3 : β * (v₁ * rot φ + v₂ * rot (-φ)) ^ 2 =
        2 * β * v₁ * v₂ + β * v₁ ^ 2 * rot φ ^ 2 + β * v₂ ^ 2 * conj (rot φ) ^ 2 := by
      rw [← Axis.conj_rot]
      linear_combination (2 * β * v₁ * v₂) * h1
    have e4 : (β * v₂ ^ 2 * conj (rot φ) ^ 2).re = (conj (β * v₂ ^ 2) * rot φ ^ 2).re := by
      rw [← Complex.conj_re]
      simp only [map_mul, map_pow, Complex.conj_conj]
    rw [e3, Complex.add_re, Complex.add_re, e4, e2, hW, add_mul, Complex.add_re]
    ring
  -- the amplitude `|W|` is at least `|C₀|`
  have hamp : C₀ ^ 2 ≤ Complex.normSq W := by
    have hc : ((C₀ : ℝ) : ℂ) = (2 * β * v₁ * v₂ + conj (2 * β * v₁ * v₂)) / 2 :=
      Complex.re_eq_add_conj _
    have hid : ((Complex.normSq W - C₀ ^ 2 : ℝ) : ℂ) =
        ((Complex.normSq β * (Complex.normSq v₁ - Complex.normSq v₂) ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.mul_conj W, ← Complex.mul_conj β, ← Complex.mul_conj v₁, ← Complex.mul_conj v₂, hc,
        hW]
      simp only [map_add, map_mul, map_pow, map_ofNat, Complex.conj_conj]
      ring
    have := Complex.ofReal_injective hid
    nlinarith [Complex.normSq_nonneg β, sq_nonneg (Complex.normSq v₁ - Complex.normSq v₂)]
  by_cases hW0 : W = 0
  · have : C₀ = 0 := by
      rw [hW0, map_zero] at hamp
      nlinarith [sq_nonneg C₀]
    exact ⟨0, by rw [key, hW0, zero_mul, Complex.zero_re, add_zero, this]⟩
  · have hρ : 0 < ‖W‖ := norm_pos_iff.2 hW0
    have hρ2 : Complex.normSq W = ‖W‖ ^ 2 := Complex.normSq_eq_norm_sq W
    have hWpol : W = (‖W‖ : ℂ) * rot (Complex.arg W) := by
      rw [rot]; exact (Complex.norm_mul_exp_arg_mul_I W).symm
    set ρ := ‖W‖ with hρdef
    set a := Complex.arg W with hadef
    have hx : |-C₀ / ρ| ≤ 1 := by
      rw [abs_div, abs_neg, abs_of_pos hρ, div_le_one hρ, abs_le]
      constructor <;> nlinarith
    refine ⟨(Real.arccos (-C₀ / ρ) - a) / 2, ?_⟩
    rw [key]
    have e5 : W * rot (2 * ((Real.arccos (-C₀ / ρ) - a) / 2)) = (ρ : ℂ) * rot (Real.arccos (-C₀ / ρ)) := by
      rw [hWpol, mul_assoc, ← rot_add']
      congr 2; ring
    rw [e5, Complex.re_ofReal_mul, rot_re, Real.cos_arccos (by linarith [(abs_le.1 hx).1])
      (by linarith [(abs_le.1 hx).2])]
    field_simp
    ring

open Axis in
/-- **Remark 4.12**: if `g₁ = Re(z^k)` on the unit circle, for a degenerate mode `k ≥ 1`, the
idealised tilt `q₀(θ)`, seen in the frame of the table, describes an ellipse centred at `0`
(`Table.idealTilt_eq`), so the quadratic form `qᵀ M q` vanishes for some angle. -/
theorem exists_Mq_idealTilt_eq_zero (F : Feet) {T : Table} (hA : T.A = F.A) (hB : T.B = F.B)
    (hC : T.C = F.C) (hD : T.D = F.D) {g : ℂ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hg : ∀ z : ℂ, ‖z‖ = 1 → g z = (z ^ k).re) (hmk : F.m k = 0) :
    ∃ θ : ℝ, F.Mq (rot (-θ) * T.Q g θ 0) = 0 := by
  obtain ⟨a₀, a₁, a₂, iA, iB, iC, iD⟩ := (F.m_eq_zero_iff k).1 hmk
  obtain ⟨φ, hφ⟩ := exists_re_mul_sq_eq_zero (conj (F.m 2)) a₂ (conj a₁)
  refine ⟨φ / k, ?_⟩
  rw [Table.idealTilt_eq (T := T) (by rw [hA]; exact F.nA) (by rw [hB]; exact F.nB)
    (by rw [hC]; exact F.nC) (by rw [hD]; exact F.nD) hg (by rw [hA]; exact iA)
    (by rw [hB]; exact iB) (by rw [hC]; exact iC) (by rw [hD]; exact iD)]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hpow : rot (φ / k) ^ k = rot φ := by
    rw [rot, ← Complex.exp_nat_mul, rot]
    congr 1; push_cast; field_simp
  have h1 : rot (-(φ / k)) * rot (φ / k) = 1 := by rw [mul_comm, rot_mul_rot_neg]
  rw [hpow, Axis.conj_rot, ← mul_assoc, h1, one_mul, Mq_eq, hφ, mul_zero]

end Wobbly
