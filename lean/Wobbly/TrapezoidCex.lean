import Wobbly.Degenerate
import Wobbly.PolyCalc

/-!
# Theorem 5.7: an isosceles trapezoid which wobbles at every angle

The table is the isosceles trapezoid with feet `A = (3/5, 4/5)`, `B = (3/5, -4/5)`,
`C = (c_β, -s_β)`, `D = (c_β, s_β)`, where `c_β = (√23 - 3)/10` and `s_β = √(1 - c_β²)`.
All the quantities of Proposition 5.6 are computed exactly in `ℚ(√23)` (up to the common factor
`c₀ = 2 s_α s_β / (s_α + s_β)`), using `(x + iy)^n = P_n(x) + i y Q_n(x)` (`cheb`).

Main results: `trap_W3_bound` (`W₃ ≥ 1.4`), `trapezoid_wob_ge` (`w_AC ≥ ε³` for `0 < ε ≤ 10⁻³`),
`trapezoid_terrain_exists` and `trapezoid_wobbles` (the four feet are never on the ground).
Compared with the paper (`ε ≤ 4·10⁻³`, `w_AC ≥ 0.5 ε³`), the Lean version uses cruder constants
(`K ≤ 4.4`, `d_min ≥ 1.8`, `P₃ ≤ K L₃`, `f(s) ≤ ½ + s/2`) and hence a smaller `ε₀ = 10⁻³`.
-/

open Complex ComplexConjugate

namespace Wobbly

/-- `cheb x n = (P_n(x), Q_n(x))` with `(x + iy)^n = P_n(x) + i y Q_n(x)` when `x² + y² = 1`
(`P_n = T_n` and `Q_n = U_{n-1}` are Chebyshev polynomials). -/
noncomputable def cheb (x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => (x * (cheb x n).1 - (1 - x ^ 2) * (cheb x n).2, x * (cheb x n).2 + (cheb x n).1)

lemma cheb_succ (x : ℝ) (n : ℕ) :
    cheb x (n + 1) = (x * (cheb x n).1 - (1 - x ^ 2) * (cheb x n).2, x * (cheb x n).2 + (cheb x n).1) :=
  rfl

lemma pow_eq_cheb {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) (n : ℕ) :
    (⟨x, y⟩ : ℂ) ^ n = ⟨(cheb x n).1, y * (cheb x n).2⟩ := by
  induction n with
  | zero => apply Complex.ext <;> simp [cheb]
  | succ n ih =>
    rw [pow_succ, ih, cheb_succ]
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im]
    · linear_combination (-(cheb x n).2) * h
    · ring

section values

/-- `√23`. -/
noncomputable def s : ℝ := Real.sqrt 23

lemma hs : s ^ 2 = 23 := Real.sq_sqrt (by norm_num)

lemma s_pos : 0 < s := Real.sqrt_pos.2 (by norm_num)

lemma s_bounds : 4.79583 < s ∧ s < 4.79584 := by
  have h := hs
  have h0 := s_pos
  constructor <;> nlinarith

/-- `cos β = (√23 - 3)/10`. -/
noncomputable def cb : ℝ := (s - 3) / 10

lemma cb_0 : cheb cb 0 = ((1 : ℝ), (0 : ℝ)) := by simp [cheb]

lemma cb_1 : cheb cb 1 = ((-3 / 10 : ℝ) + (1 / 10 : ℝ) * s, (1 : ℝ)) := by
  rw [cheb_succ, cb_0]; simp only [cb]
  ext
  · linear_combination ((0 : ℝ)) * hs
  · linear_combination ((0 : ℝ)) * hs

lemma cb_2 : cheb cb 2 = ((-9 / 25 : ℝ) + (-3 / 25 : ℝ) * s, (-3 / 5 : ℝ) + (1 / 5 : ℝ) * s) := by
  rw [cheb_succ, cb_1]; simp only [cb]
  ext
  · linear_combination ((1 / 50 : ℝ)) * hs
  · linear_combination ((0 : ℝ)) * hs

lemma cb_3 : cheb cb 3 = ((-9 / 250 : ℝ) + (-1 / 10 : ℝ) * s, (7 / 25 : ℝ) + (-6 / 25 : ℝ) * s) := by
  rw [cheb_succ, cb_2]; simp only [cb]
  ext
  · linear_combination ((-3 / 100 : ℝ) + (1 / 500 : ℝ) * s) * hs
  · linear_combination ((1 / 50 : ℝ)) * hs

lemma cb_4 : cheb cb 4 = ((-49 / 625 : ℝ) + (108 / 625 : ℝ) * s, (-84 / 125 : ℝ)) := by
  rw [cheb_succ, cb_3]; simp only [cb]
  ext
  · linear_combination ((9 / 1250 : ℝ) + (-3 / 1250 : ℝ) * s) * hs
  · linear_combination ((-3 / 125 : ℝ)) * hs

lemma cb_5 : cheb cb 5 = ((5487 / 6250 : ℝ) + (-121 / 6250 : ℝ) * s, (77 / 625 : ℝ) + (66 / 625 : ℝ) * s) := by
  rw [cheb_succ, cb_4]; simp only [cb]
  ext
  · linear_combination ((33 / 3125 : ℝ)) * hs
  · linear_combination ((0 : ℝ)) * hs

lemma cb_6 : cheb cb 6 = ((-8397 / 15625 : ℝ) + (9 / 625 : ℝ) * s, (3387 / 3125 : ℝ) + (-121 / 3125 : ℝ) * s) := by
  rw [cheb_succ, cb_5]; simp only [cb]
  ext
  · linear_combination ((-22 / 3125 : ℝ) + (33 / 31250 : ℝ) * s) * hs
  · linear_combination ((33 / 3125 : ℝ)) * hs

lemma cb_7 : cheb cb 7 = ((-76443 / 156250 : ℝ) + (-15119 / 156250 : ℝ) * s, (-14869 / 15625 : ℝ) + (84 / 625 : ℝ) * s) := by
  rw [cheb_succ, cb_6]; simp only [cb]
  ext
  · linear_combination ((4563 / 312500 : ℝ) + (-121 / 312500 : ℝ) * s) * hs
  · linear_combination ((-121 / 31250 : ℝ)) * hs

lemma cb_8 : cheb cb 8 = ((150721 / 390625 : ℝ) + (-21168 / 390625 : ℝ) * s, (8232 / 78125 : ℝ) + (-18144 / 78125 : ℝ) * s) := by
  rw [cheb_succ, cb_7]; simp only [cb]
  ext
  · linear_combination ((-10647 / 390625 : ℝ) + (21 / 15625 : ℝ) * s) * hs
  · linear_combination ((42 / 3125 : ℝ)) * hs

lemma cb_9 : cheb cb 9 = ((33021 / 3906250 : ℝ) + (32257 / 156250 : ℝ) * s, (-70283 / 390625 : ℝ) + (10164 / 390625 : ℝ) * s) := by
  rw [cheb_succ, cb_8]; simp only [cb]
  ext
  · linear_combination ((3738 / 390625 : ℝ) + (-4536 / 1953125 : ℝ) * s) * hs
  · linear_combination ((-9072 / 390625 : ℝ)) * hs

lemma cb_10 : cheb cb 10 = ((5456331 / 9765625 : ℝ) + (-663927 / 9765625 : ℝ) * s, (238821 / 1953125 : ℝ) + (14113 / 78125 : ℝ) * s) := by
  rw [cheb_succ, cb_9]; simp only [cb]
  ext
  · linear_combination ((337579 / 19531250 : ℝ) + (2541 / 9765625 : ℝ) * s) * hs
  · linear_combination ((5082 / 1953125 : ℝ)) * hs

lemma cb_11 : cheb cb 11 = ((-64104153 / 97656250 : ℝ) + (-5264401 / 97656250 : ℝ) * s, (9155587 / 9765625 : ℝ) + (-1073754 / 9765625 : ℝ) * s) := by
  rw [cheb_succ, cb_10]; simp only [cb]
  ext
  · linear_combination ((-3205983 / 195312500 : ℝ) + (14113 / 7812500 : ℝ) * s) * hs
  · linear_combination ((14113 / 781250 : ℝ)) * hs

lemma cb_12 : cheb cb 12 = ((-100792657 / 244140625 : ℝ) + (-302292 / 9765625 : ℝ) * s, (-58133628 / 48828125 : ℝ) + (3556224 / 48828125 : ℝ) * s) := by
  rw [cheb_succ, cb_11]; simp only [cb]
  ext
  · linear_combination ((1033371 / 97656250 : ℝ) + (-536877 / 488281250 : ℝ) * s) * hs
  · linear_combination ((-536877 / 48828125 : ℝ)) * hs

lemma cb_13 : cheb cb 13 = ((1859723967 / 2441406250 : ℝ) + (-24631489 / 2441406250 : ℝ) * s, (27304361 / 244140625 : ℝ) + (-1678338 / 9765625 : ℝ) * s) := by
  rw [cheb_succ, cb_12]; simp only [cb]
  ext
  · linear_combination ((-23646393 / 1220703125 : ℝ) + (889056 / 1220703125 : ℝ) * s) * hs
  · linear_combination ((1778112 / 244140625 : ℝ)) * hs

lemma cb_14 : cheb cb 14 = ((-553031649 / 6103515625 : ℝ) + (1155741717 / 6103515625 : ℝ) * s, (406383267 / 1220703125 : ℝ) + (64274111 / 1220703125 : ℝ) * s) := by
  rw [cheb_succ, cb_13]; simp only [cb]
  ext
  · linear_combination ((63605893 / 6103515625 : ℝ) + (-839169 / 488281250 : ℝ) * s) * hs
  · linear_combination ((-839169 / 48828125 : ℝ)) * hs

lemma cb_15 : cheb cb 15 = ((9989209701 / 61035156250 : ℝ) + (-59397811 / 488281250 : ℝ) * s, (-423454273 / 6103515625 : ℝ) + (1262522184 / 6103515625 : ℝ) * s) := by
  rw [cheb_succ, cb_14]; simp only [cb]
  ext
  · linear_combination ((466444407 / 24414062500 : ℝ) + (64274111 / 122070312500 : ℝ) * s) * hs
  · linear_combination ((64274111 / 12207031250 : ℝ)) * hs

lemma cb_16 : cheb cb 16 = ((-86542376639 / 152587890625 : ℝ) + (-12761848512 / 152587890625 : ℝ) * s, (20148791376 / 30517578125 : ℝ) + (-232714944 / 1220703125 : ℝ) * s) := by
  rw [cheb_succ, cb_15]; simp only [cb]
  ext
  · linear_combination ((-3855828438 / 152587890625 : ℝ) + (315630546 / 152587890625 : ℝ) * s) * hs
  · linear_combination ((631261092 / 30517578125 : ℝ)) * hs

lemma ca_0 : cheb (3 / 5) 0 = (1, 0) := by simp [cheb]

lemma ca_1 : cheb (3 / 5) 1 = ((3 / 5 : ℝ), (1 / 1 : ℝ)) := by
  rw [cheb_succ, ca_0]; norm_num

lemma ca_2 : cheb (3 / 5) 2 = ((-7 / 25 : ℝ), (6 / 5 : ℝ)) := by
  rw [cheb_succ, ca_1]; norm_num

lemma ca_3 : cheb (3 / 5) 3 = ((-117 / 125 : ℝ), (11 / 25 : ℝ)) := by
  rw [cheb_succ, ca_2]; norm_num

lemma ca_4 : cheb (3 / 5) 4 = ((-527 / 625 : ℝ), (-84 / 125 : ℝ)) := by
  rw [cheb_succ, ca_3]; norm_num

lemma ca_5 : cheb (3 / 5) 5 = ((-237 / 3125 : ℝ), (-779 / 625 : ℝ)) := by
  rw [cheb_succ, ca_4]; norm_num

lemma ca_6 : cheb (3 / 5) 6 = ((11753 / 15625 : ℝ), (-2574 / 3125 : ℝ)) := by
  rw [cheb_succ, ca_5]; norm_num

lemma ca_7 : cheb (3 / 5) 7 = ((76443 / 78125 : ℝ), (4031 / 15625 : ℝ)) := by
  rw [cheb_succ, ca_6]; norm_num

lemma ca_8 : cheb (3 / 5) 8 = ((164833 / 390625 : ℝ), (88536 / 78125 : ℝ)) := by
  rw [cheb_succ, ca_7]; norm_num

lemma ca_9 : cheb (3 / 5) 9 = ((-922077 / 1953125 : ℝ), (430441 / 390625 : ℝ)) := by
  rw [cheb_succ, ca_8]; norm_num

lemma ca_10 : cheb (3 / 5) 10 = ((-9653287 / 9765625 : ℝ), (369246 / 1953125 : ℝ)) := by
  rw [cheb_succ, ca_9]; norm_num

lemma ca_11 : cheb (3 / 5) 11 = ((-34867797 / 48828125 : ℝ), (-8545549 / 9765625 : ℝ)) := by
  rw [cheb_succ, ca_10]; norm_num

lemma ca_12 : cheb (3 / 5) 12 = ((32125393 / 244140625 : ℝ), (-60504444 / 48828125 : ℝ)) := by
  rw [cheb_succ, ca_11]; norm_num

lemma ca_13 : cheb (3 / 5) 13 = ((1064447283 / 1220703125 : ℝ), (-149387939 / 244140625 : ℝ)) := by
  rw [cheb_succ, ca_12]; norm_num

lemma ca_14 : cheb (3 / 5) 14 = ((5583548873 / 6103515625 : ℝ), (616283466 / 1220703125 : ℝ)) := by
  rw [cheb_succ, ca_13]; norm_num

lemma ca_15 : cheb (3 / 5) 15 = ((6890111163 / 30517578125 : ℝ), (7432399271 / 6103515625 : ℝ)) := by
  rw [cheb_succ, ca_14]; norm_num

lemma ca_16 : cheb (3 / 5) 16 = ((-98248054847 / 152587890625 : ℝ), (29187308976 / 30517578125 : ℝ)) := by
  rw [cheb_succ, ca_15]; norm_num

lemma cb_bounds : 0.179583 < cb ∧ cb < 0.179584 := by
  obtain ⟨h1, h2⟩ := s_bounds
  constructor <;> simp only [cb] <;> linarith

/-- `sin β = √(1 - cos² β)`. -/
noncomputable def sb : ℝ := Real.sqrt (1 - cb ^ 2)

lemma sb_sq : sb ^ 2 = 1 - cb ^ 2 := Real.sq_sqrt (by nlinarith [cb_bounds])

lemma sb_sq' : sb ^ 2 = (68 + 6 * s) / 100 := by
  rw [sb_sq]; simp only [cb]; linear_combination (-1 / 100 : ℝ) * hs

lemma sb_pos : 0 < sb := Real.sqrt_pos.2 (by nlinarith [cb_bounds])

lemma sb_bounds : 0.9837 < sb ∧ sb < 0.9838 := by
  have h := sb_sq'
  have h0 := sb_pos
  obtain ⟨h1, h2⟩ := s_bounds
  constructor <;> nlinarith

end values

section table

/-- `τ = μ = sin β / (sin α + sin β)`. -/
noncomputable def tt : ℝ := sb / (4 / 5 + sb)

lemma tt_pos : 0 < tt := div_pos sb_pos (by linarith [sb_pos])

lemma tt_lt_one : tt < 1 := by
  rw [tt, div_lt_one (by linarith [sb_pos])]; linarith

lemma one_sub_tt : 1 - tt = (4 / 5) / (4 / 5 + sb) := by
  have h : (4 / 5 + sb) ≠ 0 := by linarith [sb_pos]
  rw [tt, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]; ring

/-- The feet `A = e^{iα}`, `B = e^{-iα}`, `C = e^{-iβ}`, `D = e^{iβ}`. -/
noncomputable def eA : ℂ := ⟨3 / 5, 4 / 5⟩
noncomputable def eB : ℂ := ⟨3 / 5, -(4 / 5)⟩
noncomputable def eC : ℂ := ⟨cb, -sb⟩
noncomputable def eD : ℂ := ⟨cb, sb⟩

lemma norm_mk_eq_one {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) : ‖(⟨x, y⟩ : ℂ)‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_mk, show x * x + y * y = 1 by linarith, Real.sqrt_one]

lemma hA2 : (3 / 5 : ℝ) ^ 2 + (4 / 5) ^ 2 = 1 := by norm_num
lemma hB2 : (3 / 5 : ℝ) ^ 2 + (-(4 / 5)) ^ 2 = 1 := by norm_num
lemma hC2 : cb ^ 2 + (-sb) ^ 2 = 1 := by rw [neg_sq, sb_sq]; ring
lemma hD2 : cb ^ 2 + sb ^ 2 = 1 := by rw [sb_sq]; ring

lemma ne_of_re {z w : ℂ} (h : z.re ≠ w.re) : z ≠ w := fun e => h (by rw [e])
lemma ne_of_im {z w : ℂ} (h : z.im ≠ w.im) : z ≠ w := fun e => h (by rw [e])

lemma cb_ne : (3 / 5 : ℝ) ≠ cb := by linarith [cb_bounds]

/-- The feet of the trapezoid of Theorem 5.7. -/
noncomputable def trapF : Feet where
  A := eA
  B := eB
  C := eC
  D := eD
  τ := tt
  μ := tt
  nA := norm_mk_eq_one hA2
  nB := norm_mk_eq_one hB2
  nC := norm_mk_eq_one hC2
  nD := norm_mk_eq_one hD2
  hX := by
    apply Complex.ext <;> simp only [eA, eB, eC, eD, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    · ring
    · rw [one_sub_tt, tt]
      field_simp [show (4 / 5 + sb) ≠ 0 by linarith [sb_pos]]
      ring
  τ0 := tt_pos
  τ1 := tt_lt_one
  μ0 := tt_pos
  μ1 := tt_lt_one
  AB := ne_of_im (by simp [eA, eB]; norm_num)
  AC := ne_of_re (by simpa [eA, eC] using cb_ne)
  AD := ne_of_re (by simpa [eA, eD] using cb_ne)
  BC := ne_of_re (by simpa [eB, eC] using cb_ne)
  BD := ne_of_re (by simpa [eB, eD] using cb_ne)
  CD := ne_of_im (by simp [eC, eD]; linarith [sb_pos])

/-- `c₀ = 2 sin α sin β / (sin α + sin β)`. -/
noncomputable def c₀ : ℝ := 2 * (4 / 5) * sb / (4 / 5 + sb)

/-- `μ_j = Q_j(cos β) - Q_j(cos α)`. -/
noncomputable def μ (j : ℕ) : ℝ := (cheb cb j).2 - (cheb (3 / 5) j).2

/-- `m(j) = i c₀ μ_j`. -/
lemma trapF_m (j : ℕ) : trapF.m j = I * ((c₀ * μ j : ℝ) : ℂ) := by
  have pA : eA ^ j = ⟨(cheb (3 / 5) j).1, 4 / 5 * (cheb (3 / 5) j).2⟩ := pow_eq_cheb hA2 j
  have pB : eB ^ j = ⟨(cheb (3 / 5) j).1, -(4 / 5) * (cheb (3 / 5) j).2⟩ := pow_eq_cheb hB2 j
  have pC : eC ^ j = ⟨(cheb cb j).1, -sb * (cheb cb j).2⟩ := pow_eq_cheb hC2 j
  have pD : eD ^ j = ⟨(cheb cb j).1, sb * (cheb cb j).2⟩ := pow_eq_cheb hD2 j
  simp only [Feet.m, trapF, pA, pB, pC, pD]
  rw [one_sub_tt]
  have h : (4 / 5 + sb) ≠ 0 := by linarith [sb_pos]
  apply Complex.ext <;> simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, c₀, μ, tt] <;> field_simp <;> ring

end table

section W3

/-- `ξ₊ = -(√23 + 3)/5`. -/
noncomputable def xX : ℝ := -(s + 3) / 5

/-- `ξ₋ = -(√23/5 + 159/125)`. -/
noncomputable def yY : ℝ := -(s / 5 + 159 / 125)

lemma μ_2 : μ 2 = (-9 / 5 : ℝ) + (1 / 5 : ℝ) * s := by
  simp only [μ, cb_2, ca_2]; ring

lemma μ_3 : μ 3 = (-4 / 25 : ℝ) + (-6 / 25 : ℝ) * s := by
  simp only [μ, cb_3, ca_3]; ring

lemma μ_4 : μ 4 = (0 : ℝ) := by
  simp only [μ, cb_4, ca_4]; ring

lemma μ_5 : μ 5 = (856 / 625 : ℝ) + (66 / 625 : ℝ) * s := by
  simp only [μ, cb_5, ca_5]; ring

lemma μ_6 : μ 6 = (5961 / 3125 : ℝ) + (-121 / 3125 : ℝ) * s := by
  simp only [μ, cb_6, ca_6]; ring

lemma μ_8 : μ 8 = (-80304 / 78125 : ℝ) + (-18144 / 78125 : ℝ) * s := by
  simp only [μ, cb_8, ca_8]; ring

lemma μ_10 : μ 10 = (-5217 / 78125 : ℝ) + (14113 / 78125 : ℝ) * s := by
  simp only [μ, cb_10, ca_10]; ring

lemma μ_12 : μ 12 = (2370816 / 48828125 : ℝ) + (3556224 / 48828125 : ℝ) * s := by
  simp only [μ, cb_12, ca_12]; ring

lemma μ_16 : μ 16 = (-361540704 / 1220703125 : ℝ) + (-232714944 / 1220703125 : ℝ) * s := by
  simp only [μ, cb_16, ca_16]; ring

lemma id_X : μ 3 + xX * μ 2 = (0 : ℝ) := by
  simp only [μ_2, μ_3, xX]
  linear_combination ((-1 / 25 : ℝ)) * hs

lemma id_Y : μ 5 - yY * μ 2 = (0 : ℝ) := by
  simp only [μ_2, μ_5, yY]
  linear_combination ((1 / 25 : ℝ)) * hs

lemma id_k0 : -(3 / 4) * (μ 10 * xX ^ 2 + 2 * μ 8 * xX * yY + μ 6 * yY ^ 2) = (79110612 / 48828125 : ℝ) + (16993368 / 48828125 : ℝ) * s := by
  simp only [μ_6, μ_8, μ_10, xX, yY]
  linear_combination ((5817294 / 48828125 : ℝ) + (756 / 78125 : ℝ) * s) * hs

lemma id_A : μ 2 * (2 * xX * yY - yY ^ 2) = (-30246 / 78125 : ℝ) + (-20806 / 78125 : ℝ) * s := by
  simp only [μ_2, xX, yY]
  linear_combination ((-3 / 125 : ℝ) + (1 / 125 : ℝ) * s) * hs

lemma id_r2 : -(3 / 2) * ((xX ^ 2 + yY ^ 2) * μ 8 + xX * yY * (μ 6 + μ 10)) + 497 / 100 * μ 8 = (362580036 / 1220703125 : ℝ) + (-75398904 / 1220703125 : ℝ) * s := by
  simp only [μ_6, μ_8, μ_10, xX, yY]
  linear_combination ((379008 / 1953125 : ℝ) + (1512 / 78125 : ℝ) * s) * hs

lemma id_r3 : μ 2 * xX ^ 2 + 2569 / 500 * μ 12 = (-5801562174 / 6103515625 : ℝ) + (1209766114 / 6103515625 : ℝ) * s := by
  simp only [μ_2, μ_12, xX]
  linear_combination ((-3 / 125 : ℝ) + (1 / 125 : ℝ) * s) * hs

lemma id_r4 : -(3 / 4) * (xX ^ 2 * μ 6 + 2 * xX * yY * μ 8 + yY ^ 2 * μ 10) + 4173 / 1000 * μ 16 = (187655425776 / 152587890625 : ℝ) + (-39133919664 / 152587890625 : ℝ) * s := by
  simp only [μ_6, μ_8, μ_10, μ_16, xX, yY]
  linear_combination ((3657906 / 48828125 : ℝ) + (756 / 78125 : ℝ) * s) * hs

lemma c₀_pos : 0 < c₀ := by
  have := sb_pos; unfold c₀; positivity

lemma c₀_bound : 0.8823 < c₀ := by
  have := sb_bounds.1
  rw [c₀, lt_div_iff₀ (by linarith)]; linarith

lemma μ2_ne : μ 2 ≠ 0 := by rw [μ_2]; nlinarith [s_bounds]

lemma conj_I_mul (r : ℝ) : conj (I * (r : ℂ)) = -(I * (r : ℂ)) := by
  simp [Complex.conj_ofReal]

lemma trapF_m2_ne : I * ((c₀ * μ 2 : ℝ) : ℂ) ≠ 0 :=
  mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 (mul_ne_zero c₀_pos.ne' μ2_ne))

lemma trap_X : trapF.m (4 - 1) / conj (trapF.m 2) = (xX : ℂ) := by
  rw [show 4 - 1 = 3 from rfl, trapF_m, trapF_m, conj_I_mul, div_eq_iff (neg_ne_zero.2 trapF_m2_ne),
    show μ 3 = -xX * μ 2 by linarith [id_X]]
  push_cast; ring

lemma trap_Y : conj (trapF.m (4 + 1)) / conj (trapF.m 2) = (yY : ℂ) := by
  rw [show 4 + 1 = 5 from rfl, trapF_m, trapF_m, conj_I_mul, conj_I_mul,
    div_eq_iff (neg_ne_zero.2 trapF_m2_ne), show μ 5 = yY * μ 2 by linarith [id_Y]]
  push_cast; ring

lemma norm_I_mul (r : ℝ) : ‖I * (r : ℂ)‖ = |r| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma trap_κ : trapF.κ 4 (6 * I) xX yY = c₀ * (-(3 / 4) * (μ 10 * xX ^ 2 + 2 * μ 8 * xX * yY + μ 6 * yY ^ 2)) := by
  simp only [Feet.κ, trapF_m, Complex.conj_ofReal, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  have : (6 * I) * (I * ((c₀ * μ 10 : ℝ) : ℂ) * (xX : ℂ) ^ 2 + 2 * (I * ((c₀ * μ 8 : ℝ) : ℂ)) * (xX : ℂ) * (yY : ℂ)
      + I * ((c₀ * μ 6 : ℝ) : ℂ) * (yY : ℂ) ^ 2) =
      ((-6 * c₀ * (μ 10 * xX ^ 2 + 2 * μ 8 * xX * yY + μ 6 * yY ^ 2) : ℝ) : ℂ) := by
    push_cast
    linear_combination (6 * c₀ * (μ 10 * xX ^ 2 + 2 * μ 8 * xX * yY + μ 6 * yY ^ 2) : ℂ) * Complex.I_sq
  rw [this, Complex.ofReal_re]; ring

lemma trap_A : ‖((4 : ℕ) : ℂ) / 4 * (2 * trapF.m (4 - 2) * (xX : ℂ) * (yY : ℂ) +
    conj (trapF.m (4 - 2)) * conj (yY : ℂ) ^ 2)‖ = c₀ * |μ 2 * (2 * xX * yY - yY ^ 2)| := by
  simp only [trapF_m, conj_I_mul, Complex.conj_ofReal, Nat.reduceSub]
  have : ((4 : ℕ) : ℂ) / 4 * (2 * (I * ((c₀ * μ 2 : ℝ) : ℂ)) * (xX : ℂ) * (yY : ℂ) +
      -(I * ((c₀ * μ 2 : ℝ) : ℂ)) * (yY : ℂ) ^ 2) = I * ((c₀ * (μ 2 * (2 * xX * yY - yY ^ 2)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_I_mul, abs_mul, abs_of_pos c₀_pos]

lemma norm_real' (r : ℝ) : ‖(r : ℂ)‖ = |r| := by rw [Complex.norm_real, Real.norm_eq_abs]

lemma trap_r2 : ‖trapF.W2 4 (6 * I) xX yY - trapF.m (2 * 4) * (497 / 100 * I)‖ =
    c₀ * |-(3 / 2) * ((xX ^ 2 + yY ^ 2) * μ 8 + xX * yY * (μ 6 + μ 10)) + 497 / 100 * μ 8| := by
  simp only [Feet.W2, trapF_m, Complex.conj_ofReal, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  have : 6 * I / 4 * (((xX : ℂ) * (xX : ℂ) + (yY : ℂ) * (yY : ℂ)) * (I * ((c₀ * μ 8 : ℝ) : ℂ)) +
      (xX : ℂ) * (yY : ℂ) * (I * ((c₀ * μ 6 : ℝ) : ℂ)) + (xX : ℂ) * (yY : ℂ) * (I * ((c₀ * μ 10 : ℝ) : ℂ)))
      - I * ((c₀ * μ 8 : ℝ) : ℂ) * (497 / 100 * I) =
      ((c₀ * (-(3 / 2) * ((xX ^ 2 + yY ^ 2) * μ 8 + xX * yY * (μ 6 + μ 10)) + 497 / 100 * μ 8) : ℝ) : ℂ) := by
    push_cast
    linear_combination (c₀ * ((3 / 2) * ((xX ^ 2 + yY ^ 2) * μ 8 + xX * yY * (μ 6 + μ 10)) - 497 / 100 * μ 8)
      : ℂ) * Complex.I_sq
  rw [this, norm_real', abs_mul, abs_of_pos c₀_pos]

lemma trap_r3 : ‖((4 : ℕ) : ℂ) / 4 * (trapF.m (4 - 2) * (xX : ℂ) ^ 2) - trapF.m (3 * 4) * (-(2569 / 500))‖ =
    c₀ * |μ 2 * xX ^ 2 + 2569 / 500 * μ 12| := by
  simp only [trapF_m, Nat.reduceMul, Nat.reduceSub]
  have : ((4 : ℕ) : ℂ) / 4 * (I * ((c₀ * μ 2 : ℝ) : ℂ) * (xX : ℂ) ^ 2) - I * ((c₀ * μ 12 : ℝ) : ℂ) * (-(2569 / 500)) =
      I * ((c₀ * (μ 2 * xX ^ 2 + 2569 / 500 * μ 12) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_I_mul, abs_mul, abs_of_pos c₀_pos]

lemma trap_r4 : ‖trapF.W4 4 (6 * I) xX yY - trapF.m (4 * 4) * (4173 / 1000 * I)‖ =
    c₀ * |-(3 / 4) * (xX ^ 2 * μ 6 + 2 * xX * yY * μ 8 + yY ^ 2 * μ 10) + 4173 / 1000 * μ 16| := by
  simp only [Feet.W4, trapF_m, Complex.conj_ofReal, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  have : 6 * I / 8 * ((xX : ℂ) ^ 2 * (I * ((c₀ * μ 6 : ℝ) : ℂ)) + 2 * (xX : ℂ) * (yY : ℂ) * (I * ((c₀ * μ 8 : ℝ) : ℂ))
      + (yY : ℂ) ^ 2 * (I * ((c₀ * μ 10 : ℝ) : ℂ))) - I * ((c₀ * μ 16 : ℝ) : ℂ) * (4173 / 1000 * I) =
      ((c₀ * (-(3 / 4) * (xX ^ 2 * μ 6 + 2 * xX * yY * μ 8 + yY ^ 2 * μ 10) + 4173 / 1000 * μ 16) : ℝ) : ℂ) := by
    push_cast
    linear_combination (c₀ * ((3 / 4) * (xX ^ 2 * μ 6 + 2 * xX * yY * μ 8 + yY ^ 2 * μ 10) - 4173 / 1000 * μ 16)
      : ℂ) * Complex.I_sq
  rw [this, norm_real', abs_mul, abs_of_pos c₀_pos]

/-- The lower bound `W₃ ≥ 1.4` (Theorem 5.7). -/
lemma trap_W3_bound : 1.4 ≤ trapF.κ 4 (6 * I) xX yY
    - ‖((4 : ℕ) : ℂ) / 4 * (2 * trapF.m (4 - 2) * (xX : ℂ) * (yY : ℂ) + conj (trapF.m (4 - 2)) * conj (yY : ℂ) ^ 2)‖
    - ‖trapF.W2 4 (6 * I) xX yY - trapF.m (2 * 4) * (497 / 100 * I)‖
    - ‖((4 : ℕ) : ℂ) / 4 * (trapF.m (4 - 2) * (xX : ℂ) ^ 2) - trapF.m (3 * 4) * (-(2569 / 500))‖
    - ‖trapF.W4 4 (6 * I) xX yY - trapF.m (4 * 4) * (4173 / 1000 * I)‖ := by
  rw [trap_κ, trap_A, trap_r2, trap_r3, trap_r4, id_k0, id_A, id_r2, id_r3, id_r4]
  obtain ⟨h1, h2⟩ := s_bounds
  have hc := c₀_bound
  rw [abs_of_neg (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_neg (by linarith)]
  nlinarith

end W3

section tableT

/-- `a = cos α - cos β` and `b = sin α + sin β`: the diagonals are `(a, ±b)`. -/
noncomputable def ta : ℝ := 3 / 5 - cb
noncomputable def tb : ℝ := 4 / 5 + sb

lemma ta_bounds : 0.4204 < ta ∧ ta < 0.4205 := by
  obtain ⟨h1, h2⟩ := cb_bounds; constructor <;> simp only [ta] <;> linarith

lemma tb_bounds : 1.7837 < tb ∧ tb < 1.7838 := by
  obtain ⟨h1, h2⟩ := sb_bounds; constructor <;> simp only [tb] <;> linarith

lemma eAC : eA - eC = ⟨ta, tb⟩ := by
  apply Complex.ext <;> simp [eA, eC, ta, tb]

lemma eBD : eB - eD = ⟨ta, -tb⟩ := by
  apply Complex.ext <;> simp [eB, eD, ta, tb]; ring

lemma norm_mk (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_mk, sq, sq]

/-- The trapezoid of Theorem 5.7, as a table with `r = 1`. -/
noncomputable def trapT : Table where
  A := eA
  B := eB
  C := eC
  D := eD
  r := 1
  normA := (norm_mk_eq_one hA2).le
  normB := (norm_mk_eq_one hB2).le
  normC := (norm_mk_eq_one hC2).le
  normD := (norm_mk_eq_one hD2).le
  AC_ne := trapF.AC
  BD_ne := trapF.BD
  not_parallel := by
    have ha := ta_bounds; have hb := tb_bounds
    have hd : 0 < ta ^ 2 + tb ^ 2 := by nlinarith [ha.1, hb.1]
    have hs := Real.sq_sqrt hd.le
    have hs0 := Real.sqrt_pos.2 hd
    rw [eAC, eBD]
    simp only [unit, dot, norm_mk, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, neg_sq]
    set d := Real.sqrt (ta ^ 2 + tb ^ 2)
    have e : d⁻¹ * ta * (d⁻¹ * ta) + d⁻¹ * tb * (d⁻¹ * -tb) = (ta ^ 2 - tb ^ 2) / (ta ^ 2 + tb ^ 2) := by
      rw [← hs]; field_simp; ring
    rw [e, abs_div, abs_of_pos hd, div_lt_one hd, abs_lt]
    constructor <;> nlinarith

lemma trapT_d₁ : trapT.d₁ = Real.sqrt (ta ^ 2 + tb ^ 2) := by
  simp only [Table.d₁, trapT, eAC, norm_mk]

lemma trapT_d₂ : trapT.d₂ = Real.sqrt (ta ^ 2 + tb ^ 2) := by
  simp only [Table.d₂, trapT, eBD, norm_mk, neg_sq]

lemma trapT_dmin : 1.8 ≤ trapT.dmin := by
  rw [Table.dmin, trapT_d₁, trapT_d₂, min_self, Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [ta_bounds, tb_bounds]

lemma trapT_γ : trapT.γ = (tb ^ 2 - ta ^ 2) / (ta ^ 2 + tb ^ 2) := by
  have ha := ta_bounds; have hb := tb_bounds
  have hd : 0 < ta ^ 2 + tb ^ 2 := by nlinarith [ha.1, hb.1]
  have hs := Real.sq_sqrt hd.le
  have hs0 := Real.sqrt_pos.2 hd
  simp only [Table.γ, Table.e₁, Table.e₂, trapT, eAC, eBD]
  simp only [unit, dot, norm_mk, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero, neg_sq]
  set d := Real.sqrt (ta ^ 2 + tb ^ 2)
  have e : d⁻¹ * ta * (d⁻¹ * ta) + d⁻¹ * tb * (d⁻¹ * -tb) = -((tb ^ 2 - ta ^ 2) / (ta ^ 2 + tb ^ 2)) := by
    rw [← hs]; field_simp; ring
  rw [e, abs_neg, abs_of_pos (div_pos (by nlinarith) hd)]

lemma trapT_K : trapT.K ≤ 4.4 := by
  have ha := ta_bounds; have hb := tb_bounds
  have hd : 0 < ta ^ 2 + tb ^ 2 := by nlinarith [ha.1, hb.1]
  rw [Table.K, trapT_γ, Real.sqrt_le_left (by norm_num)]
  have e : 1 - (tb ^ 2 - ta ^ 2) / (ta ^ 2 + tb ^ 2) = 2 * ta ^ 2 / (ta ^ 2 + tb ^ 2) := by
    field_simp; ring
  rw [e, div_div_eq_mul_div, div_le_iff₀ (by nlinarith [ha.1])]
  nlinarith

end tableT

section remainder

lemma f_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : f s ≤ 1 / 2 + s / 2 := by
  have e := f_sub_half h1
  have hq : 1 / (2 * (1 + Real.sqrt (1 - s)) ^ 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have := Real.sqrt_nonneg (1 - s)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hq h0]

/-- An explicit upper bound for the remainder `R(ε)` of Proposition 5.2, from upper bounds `K'` on
`K` and `t'` on `t₁`, and a lower bound `d'` on `d_min` (using `f(s) ≤ ½ + s/2`). -/
lemma Rem_le_of {K dmin L₁ M₁ L₃ P P₃ ε K' d' t' : ℝ} (hK : 0 ≤ K) (hL₁ : 0 ≤ L₁) (hM₁ : 0 ≤ M₁)
    (hL₃ : 0 ≤ L₃) (hP : 0 ≤ P) (hP₃ : 0 ≤ P₃) (hε : 0 ≤ ε) (hKK : K ≤ K') (hd' : 0 < d')
    (hdd : d' ≤ dmin) (h0 : (ε * L₁ + ε ^ 3 * L₃) * K' ≤ 1)
    (ht : ε * P + ε ^ 3 * P₃ + 2 * K' * (ε * L₁ + ε ^ 3 * L₃) / d' *
      ((1 / 2 + ((ε * L₁ + ε ^ 3 * L₃) * K') ^ 2 / 2) * ((ε * L₁ + ε ^ 3 * L₃) * K') ^ 2) ≤ t')
    (ht1 : t' ≤ 1) :
    Rem K dmin L₁ M₁ L₃ P P₃ ε ≤
      ε * M₁ * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2) ^ 2 + 2 * ε * L₁ * (t' ^ 4 / 2 + 1 / 2 * (t' + ε * P) *
        (ε ^ 3 * P₃ + 2 * K' * (ε * L₁ + ε ^ 3 * L₃) / d' * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2))) +
      2 * ε ^ 3 * L₃ * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2) := by
  unfold Rem
  set L := ε * L₁ + ε ^ 3 * L₃ with hL
  have hL0 : 0 ≤ L := by positivity
  have hdm : 0 < dmin := lt_of_lt_of_le hd' hdd
  set t₀ := L * K
  have ht₀ : 0 ≤ t₀ := mul_nonneg hL0 hK
  have ht₀' : t₀ ≤ L * K' := mul_le_mul_of_nonneg_left hKK hL0
  have ht₀1 : t₀ ≤ 1 := ht₀'.trans h0
  have hK' : 0 ≤ K' := hK.trans hKK
  have ft₀ : f (t₀ ^ 2) ≤ 1 / 2 + (L * K') ^ 2 / 2 := by
    have := f_le (sq_nonneg t₀) (by nlinarith)
    have : t₀ ^ 2 ≤ (L * K') ^ 2 := pow_le_pow_left₀ ht₀ ht₀' 2
    linarith
  have hf₀ := f_pos (t₀ ^ 2)
  set t₁ := min t₀ (ε * P + ε ^ 3 * P₃ + 2 * K * L / dmin * (f (t₀ ^ 2) * t₀ ^ 2))
  have ht₁0 : 0 ≤ t₁ := le_min ht₀ (by positivity)
  have hcoef : 2 * K * L / dmin ≤ 2 * K' * L / d' := by
    rw [div_le_div_iff₀ hdm hd']
    have : 2 * K * L * d' ≤ 2 * K' * L * d' := by gcongr
    have : 2 * K' * L * d' ≤ 2 * K' * L * dmin := by gcongr
    linarith
  have ht₁ : t₁ ≤ t' := by
    refine (min_le_right _ _).trans (le_trans ?_ ht)
    have hsq : t₀ ^ 2 ≤ (L * K') ^ 2 := pow_le_pow_left₀ ht₀ ht₀' 2
    have : f (t₀ ^ 2) * t₀ ^ 2 ≤ (1 / 2 + (L * K') ^ 2 / 2) * (L * K') ^ 2 :=
      mul_le_mul ft₀ hsq (sq_nonneg _) (by positivity)
    have : 2 * K * L / dmin * (f (t₀ ^ 2) * t₀ ^ 2) ≤
        2 * K' * L / d' * ((1 / 2 + (L * K') ^ 2 / 2) * (L * K') ^ 2) :=
      mul_le_mul hcoef this (by positivity) (by positivity)
    linarith
  have ht₁1 : t₁ ≤ 1 := ht₁.trans ht1
  have hsq1 : t₁ ^ 2 ≤ t' ^ 2 := pow_le_pow_left₀ ht₁0 ht₁ 2
  have ft₁ : f (t₁ ^ 2) ≤ 1 / 2 + t' ^ 2 / 2 := by
    have := f_le (sq_nonneg t₁) (by nlinarith); linarith
  have hf₁ := half_le_f (sq_nonneg t₁)
  set Φ₁ := f (t₁ ^ 2) * t₁ ^ 2
  have hΦ0 : 0 ≤ Φ₁ := by positivity
  have hΦ : Φ₁ ≤ (1 / 2 + t' ^ 2 / 2) * t' ^ 2 := mul_le_mul ft₁ hsq1 (sq_nonneg _) (by positivity)
  have hδ : ε ^ 3 * P₃ + 2 * K * L / dmin * Φ₁ ≤
      ε ^ 3 * P₃ + 2 * K' * L / d' * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2) := by
    have := mul_le_mul hcoef hΦ hΦ0 (by positivity); linarith
  have hδ0 : 0 ≤ ε ^ 3 * P₃ + 2 * K * L / dmin * Φ₁ := by positivity
  have h1 : (f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 ≤ t' ^ 4 / 2 := by
    have : f (t₁ ^ 2) - 1 / 2 ≤ t' ^ 2 / 2 := by linarith
    have := mul_le_mul this hsq1 (sq_nonneg _) (by positivity)
    nlinarith
  have h2 : (t₁ + ε * P) * (ε ^ 3 * P₃ + 2 * K * L / dmin * Φ₁) ≤
      (t' + ε * P) * (ε ^ 3 * P₃ + 2 * K' * L / d' * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2)) :=
    mul_le_mul (by linarith) hδ hδ0 (by have := mul_nonneg hε hP; linarith)
  have h3 : Φ₁ ^ 2 ≤ ((1 / 2 + t' ^ 2 / 2) * t' ^ 2) ^ 2 := pow_le_pow_left₀ hΦ0 hΦ 2
  have a1 : ε * M₁ * Φ₁ ^ 2 ≤ ε * M₁ * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have a2 : 2 * ε * L₁ * ((f (t₁ ^ 2) - 1 / 2) * t₁ ^ 2 + 1 / 2 * (t₁ + ε * P) *
      (ε ^ 3 * P₃ + 2 * K * L / dmin * Φ₁)) ≤ 2 * ε * L₁ * (t' ^ 4 / 2 + 1 / 2 * (t' + ε * P) *
      (ε ^ 3 * P₃ + 2 * K' * L / d' * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [h1, h2]
  have a3 : 2 * ε ^ 3 * L₃ * Φ₁ ≤ 2 * ε ^ 3 * L₃ * ((1 / 2 + t' ^ 2 / 2) * t' ^ 2) :=
    mul_le_mul_of_nonneg_left hΦ (by positivity)
  linarith

end remainder

section theorem57

open Table

/-- `g₃ = Re(4.970 i z⁸ - 5.138 z¹² + 4.173 i z¹⁶)`. -/
noncomputable def g3 : ℂ → ℝ := fun z =>
  (497 / 100 * I * z ^ (2 * 4) + -(2569 / 500) * z ^ (3 * 4) + 4173 / 1000 * I * z ^ (4 * 4)).re

lemma norm_b6 : ‖(6 : ℂ) * I‖ = 6 := by simp

lemma norm_pow_sub_pow_le' {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + (x ^ n - y ^ n) * y := by ring
    rw [e]
    have h1 : ‖x ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    calc _ ≤ ‖x ^ n * (x - y)‖ + ‖(x ^ n - y ^ n) * y‖ := norm_add_le _ _
      _ = ‖x ^ n‖ * ‖x - y‖ + ‖x ^ n - y ^ n‖ * ‖y‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖x - y‖ + (n * ‖x - y‖) * 1 := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ‖x - y‖ := by push_cast; ring

lemma g3_lip (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : |g3 x - g3 y| ≤ 169 * ‖x - y‖ := by
  have e : g3 x - g3 y = (497 / 100 * I * (x ^ 8 - y ^ 8) + -(2569 / 500) * (x ^ 12 - y ^ 12)
      + 4173 / 1000 * I * (x ^ 16 - y ^ 16)).re := by
    simp only [g3, ← Complex.sub_re, Nat.reduceMul]; congr 1; ring
  rw [e]
  have h8 := norm_pow_sub_pow_le' hx hy 8
  have h12 := norm_pow_sub_pow_le' hx hy 12
  have h16 := norm_pow_sub_pow_le' hx hy 16
  have n1 : ‖(497 / 100 : ℂ) * I‖ = 497 / 100 := by simp
  have n2 : ‖-(2569 / 500 : ℂ)‖ = 2569 / 500 := by simp
  have n3 : ‖(4173 / 1000 : ℂ) * I‖ = 4173 / 1000 := by simp
  push_cast at h8 h12 h16
  calc _ ≤ ‖497 / 100 * I * (x ^ 8 - y ^ 8) + -(2569 / 500) * (x ^ 12 - y ^ 12)
        + 4173 / 1000 * I * (x ^ 16 - y ^ 16)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖497 / 100 * I * (x ^ 8 - y ^ 8)‖ + ‖-(2569 / 500) * (x ^ 12 - y ^ 12)‖
        + ‖4173 / 1000 * I * (x ^ 16 - y ^ 16)‖ := norm_add₃_le
    _ = 497 / 100 * ‖x ^ 8 - y ^ 8‖ + 2569 / 500 * ‖x ^ 12 - y ^ 12‖ + 4173 / 1000 * ‖x ^ 16 - y ^ 16‖ := by
        rw [norm_mul (497 / 100 * I), norm_mul (-(2569 / 500) : ℂ), norm_mul (4173 / 1000 * I), n1, n2, n3]
    _ ≤ 169 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

lemma normSq_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) : Complex.normSq u = 1 := by
  rw [Complex.normSq_eq_norm_sq, hu, one_pow]

lemma gk_circle (k : ℕ) (b u : ℂ) (hu : ‖u‖ = 1) : gk k b u = (u ^ k).re := by
  simp [gk, normSq_of_norm_one hu]

lemma Gk_circle (k : ℕ) (b u : ℂ) (hu : ‖u‖ = 1) : Gk k b u = Feet.grad₁ k b u := by
  simp [Gk, Feet.grad₁, normSq_of_norm_one hu]

lemma trapF_m4 : trapF.m 4 = 0 := by rw [trapF_m, μ_4]; simp

lemma trapT_F₀_g₁ (θ : ℝ) : F₀ trapT (gk 4 (6 * I)) tt tt θ = 0 := by
  have n : ∀ a : ℂ, ‖a‖ = 1 → ‖rot θ * a‖ = 1 := fun a ha => by rw [norm_rot_mul, ha]
  have e : F₀ trapT (gk 4 (6 * I)) tt tt θ = F₀ trapT (fun z => (1 * z ^ 4).re) trapF.τ trapF.μ θ := by
    unfold F₀
    rw [gk_circle _ _ _ (n trapT.A trapF.nA), gk_circle _ _ _ (n trapT.B trapF.nB),
      gk_circle _ _ _ (n trapT.C trapF.nC), gk_circle _ _ _ (n trapT.D trapF.nD)]
    simp only [one_mul]; rfl
  rw [e, Table.F₀_monomial trapF rfl rfl rfl rfl, trapF_m4]; simp

/-- The idealised tilt `q₀ = e^{iθ}(ξ₊ ζ + ξ₋ ζ̄)` has `|q₀| ≤ |ξ₊| + |ξ₋| ≤ 3.8`. -/
lemma trapT_P (θ : ℝ) : ‖trapT.Q (gk 4 (6 * I)) θ 0‖ ≤ 19 / 5 := by
  obtain ⟨a₀, a₁, a₂, iA, iB, iC, iD⟩ := (trapF.m_eq_zero_iff 4).1 trapF_m4
  obtain ⟨e1, e2, -⟩ := trapF.interp_coeffs (by norm_num) trapF_m4 ⟨iA, iB, iC, iD⟩
  have hm2 := trapF.m_two_ne_zero
  have hm2c : conj (trapF.m 2) ≠ 0 := (map_ne_zero _).2 hm2
  have hX : a₂ = trapF.m (4 - 1) / conj (trapF.m 2) := by rw [e2]; field_simp
  have hY : conj a₁ = conj (trapF.m (4 + 1)) / conj (trapF.m 2) := by
    rw [e1, map_mul]; field_simp
  rw [trap_X] at hX
  rw [trap_Y] at hY
  have hg : ∀ z : ℂ, ‖z‖ = 1 → gk 4 (6 * I) z = (z ^ 4).re := fun z hz => gk_circle _ _ _ hz
  rw [Table.idealTilt_eq (T := trapT) trapF.nA trapF.nB trapF.nC trapF.nD hg iA iB iC iD θ, hX, hY]
  have hr : ‖rot θ ^ 4‖ = 1 := by rw [norm_pow, norm_rot, one_pow]
  rw [norm_mul, norm_rot, one_mul]
  calc _ ≤ ‖(xX : ℂ) * rot θ ^ 4‖ + ‖(yY : ℂ) * conj (rot θ ^ 4)‖ := norm_add_le _ _
    _ = |xX| + |yY| := by
        rw [norm_mul, norm_mul, Complex.norm_conj, hr, norm_real', norm_real', mul_one, mul_one]
    _ ≤ 19 / 5 := by
        obtain ⟨h1, h2⟩ := s_bounds
        rw [abs_of_neg (by simp only [xX]; linarith), abs_of_neg (by simp only [yY]; linarith)]
        simp only [xX, yY]; linarith

/-- The idealised tilt of `g₃`: `|q₃| ≤ K L₃ ≤ 4.4 · 169`. -/
lemma trapT_P₃ (θ : ℝ) : ‖trapT.Q g3 θ 0‖ ≤ 4.4 * 169 := by
  have key : ∀ (u v : ℂ) (d : ℝ), ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → d = ‖u - v‖ → 0 < d →
      |(g3 (foot (rot θ * u) 0) - g3 (foot (rot θ * v) 0)) / d| ≤ 169 := by
    intro u v d hu hv hd hd0
    rw [foot_zero_tilt, foot_zero_tilt, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    have hu' : ‖rot θ * u‖ ≤ 1 := by rw [norm_rot_mul]; exact hu
    have hv' : ‖rot θ * v‖ ≤ 1 := by rw [norm_rot_mul]; exact hv
    have := g3_lip _ _ hu' hv'
    rwa [← mul_sub, norm_rot_mul, ← hd] at this
  have h := norm_solve2_le (trapT.norm_rot_e₁ θ) (trapT.norm_rot_e₂ θ) (trapT.γ_rot_lt_one θ)
    (key trapT.A trapT.C trapT.d₁ trapT.normA trapT.normC rfl trapT.d₁_pos)
    (key trapT.B trapT.D trapT.d₂ trapT.normB trapT.normD rfl trapT.d₂_pos)
  rw [trapT.γ_rot] at h
  unfold Table.Q
  calc _ ≤ trapT.K * 169 := h
    _ ≤ 4.4 * 169 := by nlinarith [trapT_K]

lemma sqrt3_bound : 1.7 ≤ Real.sqrt 3 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma trapT_small {ε : ℝ} (hε : 0 ≤ ε) (hε₀ : ε ≤ 1 / 1000) : SmallL trapT (ε * 10 + ε ^ 3 * 169) := by
  have hK := trapT_K
  have hK0 := trapT.K_nonneg
  have hd := trapT_dmin
  have hL : ε * 10 + ε ^ 3 * 169 ≤ 0.0101 := by
    have : ε ^ 3 ≤ (1 / 1000) ^ 3 := pow_le_pow_left₀ hε hε₀ 3
    nlinarith
  have hL0 : 0 ≤ ε * 10 + ε ^ 3 * 169 := by positivity
  have hLK : (ε * 10 + ε ^ 3 * 169) * trapT.K ≤ 0.0101 * 4.4 := mul_le_mul hL hK hK0 (by norm_num)
  refine ⟨hL0, by linarith, ?_⟩
  have hr : trapT.r = 1 := rfl
  rw [hr]
  have h3 := sqrt3_bound
  have hLK0 : 0 ≤ (ε * 10 + ε ^ 3 * 169) * trapT.K := mul_nonneg hL0 hK0
  have hsq : ((ε * 10 + ε ^ 3 * 169) * trapT.K) ^ 2 ≤ (0.0101 * 4.4) ^ 2 := pow_le_pow_left₀ hLK0 hLK 2
  have e1 : 4 / Real.sqrt 3 ≤ 4 / 1.7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
  have e2 : 1 / trapT.dmin ≤ 1 / 1.8 := one_div_le_one_div_of_le (by norm_num) hd
  have : 4 / Real.sqrt 3 * (1 / trapT.dmin) * ((ε * 10 + ε ^ 3 * 169) * trapT.K) ^ 2 ≤
      4 / 1.7 * (1 / 1.8) * (0.0101 * 4.4) ^ 2 := by
    apply mul_le_mul (mul_le_mul e1 e2 (by positivity) (by norm_num)) hsq (sq_nonneg _) (by norm_num)
  norm_num at this ⊢
  linarith

lemma trapT_Rem₀ : Rem trapT.K trapT.dmin 10 114 169 (19 / 5) (4.4 * 169) (1 / 1000) ≤ 0.1 * (1 / 1000) ^ 3 := by
  refine (Rem_le_of (K' := 4.4) (d' := 1.8) (t' := 0.00385) trapT.K_nonneg (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) trapT_K (by norm_num) trapT_dmin
    (by norm_num) (by norm_num) (by norm_num)).trans ?_
  norm_num

lemma trapT_Rem {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000) :
    Rem trapT.K trapT.dmin 10 114 169 (19 / 5) (4.4 * 169) ε ≤ 0.1 * ε ^ 3 := by
  have h := Rem_le_scale trapT.K_nonneg trapT.dmin_pos (L₁ := 10) (M₁ := 114) (L₃ := 169) (P := 19 / 5)
    (P₃ := 4.4 * 169) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hε₀
    (by nlinarith [trapT_K, trapT.K_nonneg])
  have hq : 0 ≤ (ε / (1 / 1000)) ^ 5 := by positivity
  refine h.trans ((mul_le_mul_of_nonneg_left trapT_Rem₀ hq).trans ?_)
  have e : (ε / (1 / 1000)) ^ 5 * (0.1 * (1 / 1000) ^ 3) = 0.1 * ε ^ 3 * (ε / (1 / 1000)) ^ 2 := by ring
  rw [e]
  have : (ε / (1 / 1000)) ^ 2 ≤ 1 := by
    apply pow_le_one₀ (by positivity); rw [div_le_one (by norm_num)]; exact hε₀
  have : 0 ≤ 0.1 * ε ^ 3 := by positivity
  nlinarith

/-- **Theorem 5.7** (with `ε₀ = 10⁻³` and the bound `w_AC ≥ ε³`): let the table be the isosceles
trapezoid `trapT` and let `g` be a terrain equal to `ε g₁ + ε³ g₃` on the closed unit disc, with
`g₁ = Re(z⁴) - 3(|z|² - 1) Im(z⁸)` and `g₃ = -(4.970 Im z⁸ + 5.138 Re z¹² + 4.173 Im z¹⁶)`, and
`(10 ε + 169 ε³)`-Lipschitz on `ℂ` (see `trapezoid_terrain_exists`). If `0 < ε ≤ 10⁻³`, then
`w_AC(θ) ≥ ε³ > 0` for every `θ`. -/
theorem trapezoid_wob_ge {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000) {g : ℂ → ℝ}
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x) (θ : ℝ) :
    ε ^ 3 ≤ wob trapT g (ε * 10 + ε ^ 3 * 169) θ := by
  have hs := trapT_small hε.le hε₀
  have hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 →
      |gk 4 (6 * I) x - gk 4 (6 * I) u - dot (Gk 4 (6 * I) u) (x - u)| ≤ 114 / 2 * ‖x - u‖ ^ 2 := by
    intro u x hu hx
    refine taylor_of_lipschitz_grad' (fun u w t _ => hasDerivAt_gk 4 (by norm_num) _ u w t) ?_ u x hu hx
    intro x y hx hy
    have := lipschitz_Gk 2 (6 * I) poly_four x y hx hy
    rw [norm_b6] at this
    push_cast at this
    linarith
  have hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖Gk 4 (6 * I) u‖ ≤ 10 := by
    intro u hu
    have := norm_Gk_le 4 (by norm_num) (6 * I) u hu (polyG_four _ (norm_nonneg u) hu)
    rw [norm_b6] at this; push_cast at this; linarith
  have hmain := Table.abs_wob_sub_third_order_le (T := trapT) (g₁ := gk 4 (6 * I)) (g₃ := g3)
    (G₁ := Gk 4 (6 * I)) (M₁ := 114) (P := 19 / 5) (P₃ := 4.4 * 169) (τ := tt) (μ := tt)
    rfl hε.le hg hs hgd hT (by norm_num) hG g3_lip trapT_P trapT_P₃ trapF.hX tt_pos.le tt_lt_one.le
    tt_pos.le tt_lt_one.le θ
  have hW := Table.W3_ge (T := trapT) trapF rfl rfl rfl rfl (k := 4) (by norm_num) trapF_m4 (6 * I)
    (497 / 100 * I) (-(2569 / 500)) (4173 / 1000 * I) (g₁ := gk 4 (6 * I)) (G₁ := Gk 4 (6 * I))
    (fun z hz => gk_circle _ _ _ hz) (fun u hu => Gk_circle _ _ _ hu) θ
  rw [trap_X, trap_Y] at hW
  have hW' := trap_W3_bound
  have hR := trapT_Rem hε hε₀
  rw [trapT_F₀_g₁] at hmain
  have hw3 : 1.4 ≤ Table.w3 trapT (Gk 4 (6 * I)) tt tt θ (trapT.Q (gk 4 (6 * I)) θ 0) + F₀ trapT g3 tt tt θ :=
    hW'.trans hW
  have hε3 : 0 < ε ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left hw3 hε3.le
  rw [abs_le] at hmain
  nlinarith [hmain.1]

/-- `g₁` is `10`-Lipschitz on the closed unit disc. -/
lemma gk_lip (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |gk 4 (6 * I) x - gk 4 (6 * I) y| ≤ 10 * ‖x - y‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => gk 4 (6 * I) (y + t • (x - y)))
    (f' := fun t => dot (Gk 4 (6 * I) (y + t • (x - y))) (x - y))
    (C := 10 * ‖x - y‖) (a := 0) (b := 1)
    (fun t _ => (hasDerivAt_gk 4 (by norm_num) (6 * I) y (x - y) t).hasDerivWithinAt)
    (fun t ht => by
      have hz := norm_line_le hx hy (Set.Ico_subset_Icc_self ht)
      have hG := norm_Gk_le 4 (by norm_num) (6 * I) _ hz (polyG_four _ (norm_nonneg _) hz)
      rw [norm_b6] at hG; push_cast at hG
      rw [Real.norm_eq_abs]
      exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
    1 ⟨zero_le_one, le_rfl⟩
  simpa [Real.norm_eq_abs] using key

/-- A terrain as in Theorem 5.7 exists (McShane extension from the closed unit disc). -/
theorem trapezoid_terrain_exists {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ g : ℂ → ℝ, IsLip g (ε * 10 + ε ^ 3 * 169) ∧
      ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x := by
  set L := ε * 10 + ε ^ 3 * 169
  have hL : 0 ≤ L := by positivity
  have hlip : LipschitzOnWith (Real.toNNReal L) (fun x => ε * gk 4 (6 * I) x + ε ^ 3 * g3 x)
      (Metric.closedBall 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hx hy
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
    have h1 := gk_lip x y hx hy
    have h3 := g3_lip x y hx hy
    have e : ε * gk 4 (6 * I) x + ε ^ 3 * g3 x - (ε * gk 4 (6 * I) y + ε ^ 3 * g3 y) =
        ε * (gk 4 (6 * I) x - gk 4 (6 * I) y) + ε ^ 3 * (g3 x - g3 y) := by ring
    rw [e]
    calc _ ≤ |ε * (gk 4 (6 * I) x - gk 4 (6 * I) y)| + |ε ^ 3 * (g3 x - g3 y)| := abs_add_le _ _
      _ = ε * |gk 4 (6 * I) x - gk 4 (6 * I) y| + ε ^ 3 * |g3 x - g3 y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg (pow_nonneg hε 3)]
      _ ≤ ε * (10 * ‖x - y‖) + ε ^ 3 * (169 * ‖x - y‖) := by gcongr
      _ = L * ‖x - y‖ := by ring
  obtain ⟨g, hg, hEq⟩ := hlip.extend_real
  refine ⟨g, fun x y => ?_, fun x hx => (hEq (by rwa [Metric.mem_closedBall, dist_zero_right])).symm⟩
  have := hg.dist_le_mul x y
  rwa [Real.dist_eq, Real.coe_toNNReal _ hL, dist_eq_norm] at this

/-- **Theorem 5.7**, conclusion: whatever the angle of rotation `θ`, there is no position of the
table (with a tilt `‖q‖ < 1`) in which its four feet are on the ground. -/
theorem trapezoid_wobbles {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 1 / 1000) {g : ℂ → ℝ}
    (hg : IsLip g (ε * 10 + ε ^ 3 * 169))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 4 (6 * I) x + ε ^ 3 * g3 x) (θ : ℝ) :
    ¬ ∃ q c, ‖q‖ < 1 ∧ resid g θ q c trapT.A = 0 ∧ resid g θ q c trapT.B = 0 ∧
      resid g θ q c trapT.C = 0 ∧ resid g θ q c trapT.D = 0 := by
  rw [four_feet_iff hg (trapT_small hε.le hε₀) θ]
  have := trapezoid_wob_ge hε hε₀ hg hgd θ
  have : 0 < ε ^ 3 := by positivity
  intro h; linarith

end theorem57

end Wobbly
