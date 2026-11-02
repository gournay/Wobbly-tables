import Wobbly.TrapezoidCex
import Wobbly.Rational

/-!
# Proposition 5.8: a table with diagonals of different lengths which wobbles at every angle

The feet are the four zeros of `G(θ) = 2 cos 2θ - 2 cos(θ + π/6) + 1/2`, i.e. the roots of
`Q(z) = z⁴ - ω z³ + ½ z² - ω̄ z + 1` with `ω = e^{iπ/6}`. Writing a foot as `x + iy`,
`y = -4x² + √3 x + 3/2` and `x` is a root of `P(x) = 16x⁴ - 8√3 x³ - 8x² + 3√3 x + 5/4`; the four
roots are located by the intermediate value theorem.

All the quantities of Proposition 5.6 are then exact multiples of `t = Im m(2)` (`m(2)` is purely
imaginary and `m(3) = ω m(2)`, by the algebra of `z ↦ z^j mod Q`); only a lower bound for `t` needs
the location of the roots.
-/

open Complex ComplexConjugate

set_option linter.unusedSimpArgs false

namespace Wobbly

namespace Uneq

section roots

/-- `√3`. -/
noncomputable def r3 : ℝ := Real.sqrt 3

lemma hr3 : r3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma r3_pos : 0 < r3 := Real.sqrt_pos.2 (by norm_num)

lemma r3_bounds : 1.7320508 < r3 ∧ r3 < 1.7320509 := by
  have h := hr3; have h0 := r3_pos
  constructor <;> nlinarith

/-- `P(x) = 16x⁴ - 8√3 x³ - 8x² + 3√3 x + 5/4 = x² + y(x)² - 1`. -/
noncomputable def Pq (x : ℝ) : ℝ := 16 * x ^ 4 - 8 * r3 * x ^ 3 - 8 * x ^ 2 + 3 * r3 * x + 5 / 4

/-- `y(x) = -4x² + √3 x + 3/2`. -/
noncomputable def yf (x : ℝ) : ℝ := -4 * x ^ 2 + r3 * x + 3 / 2

lemma Pq_eq (x : ℝ) : Pq x = x ^ 2 + yf x ^ 2 - 1 := by
  unfold Pq yf; linear_combination (-(x ^ 2)) * hr3

lemma continuous_Pq : Continuous Pq := by unfold Pq; fun_prop

lemma exists_root {lo hi : ℝ} (h : lo ≤ hi) (hs : (Pq lo ≤ 0 ∧ 0 ≤ Pq hi) ∨ (0 ≤ Pq lo ∧ Pq hi ≤ 0)) :
    ∃ x, lo ≤ x ∧ x ≤ hi ∧ Pq x = 0 := by
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨x, hx, e⟩ := intermediate_value_Icc h continuous_Pq.continuousOn ⟨h1, h2⟩
    exact ⟨x, hx.1, hx.2, e⟩
  · obtain ⟨x, hx, e⟩ := intermediate_value_Icc' h continuous_Pq.continuousOn ⟨h2, h1⟩
    exact ⟨x, hx.1, hx.2, e⟩

lemma exA : ∃ x, 46613 / 50000 ≤ x ∧ x ≤ 93227 / 100000 ∧ Pq x = 0 :=
  exists_root (by norm_num) (Or.inl ⟨by have := r3_bounds; unfold Pq; norm_num; linarith,
    by have := r3_bounds; unfold Pq; norm_num; linarith⟩)
lemma exB : ∃ x, 7131 / 10000 ≤ x ∧ x ≤ 71311 / 100000 ∧ Pq x = 0 :=
  exists_root (by norm_num) (Or.inr ⟨by have := r3_bounds; unfold Pq; norm_num; linarith,
    by have := r3_bounds; unfold Pq; norm_num; linarith⟩)
lemma exC : ∃ x, -20439 / 100000 ≤ x ∧ x ≤ -10219 / 50000 ∧ Pq x = 0 :=
  exists_root (by norm_num) (Or.inl ⟨by have := r3_bounds; unfold Pq; norm_num; linarith,
    by have := r3_bounds; unfold Pq; norm_num; linarith⟩)
lemma exD : ∃ x, -57497 / 100000 ≤ x ∧ x ≤ -7187 / 12500 ∧ Pq x = 0 :=
  exists_root (by norm_num) (Or.inr ⟨by have := r3_bounds; unfold Pq; norm_num; linarith,
    by have := r3_bounds; unfold Pq; norm_num; linarith⟩)

/-- The abscissae of the feet. -/
noncomputable def xA : ℝ := exA.choose
noncomputable def xB : ℝ := exB.choose
noncomputable def xC : ℝ := exC.choose
noncomputable def xD : ℝ := exD.choose

lemma xA_spec : 46613 / 50000 ≤ xA ∧ xA ≤ 93227 / 100000 ∧ Pq xA = 0 := exA.choose_spec
lemma xB_spec : 7131 / 10000 ≤ xB ∧ xB ≤ 71311 / 100000 ∧ Pq xB = 0 := exB.choose_spec
lemma xC_spec : -20439 / 100000 ≤ xC ∧ xC ≤ -10219 / 50000 ∧ Pq xC = 0 := exC.choose_spec
lemma xD_spec : -57497 / 100000 ≤ xD ∧ xD ≤ -7187 / 12500 ∧ Pq xD = 0 := exD.choose_spec

end roots

section algebra

/-- `ω = e^{iπ/6}` and `ω̄`. -/
noncomputable def ω₀ : ℂ := ((r3 : ℂ) + I) / 2
noncomputable def ω₁ : ℂ := ((r3 : ℂ) - I) / 2

lemma hr3c : (r3 : ℂ) ^ 2 = 3 := by exact_mod_cast hr3

/-- `Q(z) = z⁴ - ω z³ + ½ z² - ω̄ z + 1`. -/
noncomputable def Qc (z : ℂ) : ℂ := z ^ 4 - ω₀ * z ^ 3 + 1 / 2 * z ^ 2 - ω₁ * z + 1

/-- The foot with abscissa `x`. -/
noncomputable def foot' (x : ℝ) : ℂ := ⟨x, yf x⟩

lemma norm_foot' {x : ℝ} (h : Pq x = 0) : ‖foot' x‖ = 1 := by
  rw [Pq_eq] at h
  rw [Complex.norm_def, foot', Complex.normSq_mk, show x * x + yf x * yf x = 1 by linarith, Real.sqrt_one]

lemma foot'_eq (x : ℝ) : foot' x = (x : ℂ) + (yf x : ℂ) * I := Complex.mk_eq_add_mul_I x (yf x)

lemma conj_foot' (x : ℝ) : conj (foot' x) = (x : ℂ) - (yf x : ℂ) * I := by
  rw [foot'_eq]; simp [map_add, map_mul, Complex.conj_ofReal]; ring

lemma foot'_mul_conj {x : ℝ} (h : Pq x = 0) : foot' x * conj (foot' x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_foot' h]; simp

/-- The feet are roots of `Q`. -/
lemma Qc_foot' {x : ℝ} (h : Pq x = 0) : Qc (foot' x) = 0 := by
  have hn := foot'_mul_conj h
  set e := foot' x
  set eb := conj (foot' x)
  have hG : e ^ 2 + eb ^ 2 - ω₀ * e - ω₁ * eb + 1 / 2 = 0 := by
    have hy : ((yf x : ℝ) : ℂ) = -4 * (x : ℂ) ^ 2 + (r3 : ℂ) * x + 3 / 2 := by simp [yf]
    have hP : (x : ℂ) ^ 2 + (yf x : ℂ) ^ 2 = 1 := by
      have := Pq_eq x; rw [h] at this; exact_mod_cast (by linarith : x ^ 2 + yf x ^ 2 = 1)
    simp only [e, eb, foot'_eq, conj_foot', ω₀, ω₁]
    linear_combination (2 * (yf x : ℂ) ^ 2 - (yf x : ℂ)) * Complex.I_sq + (-2 : ℂ) * hP + hy
  unfold Qc
  linear_combination e ^ 2 * hG - (1 + e * eb - ω₁ * e) * hn

lemma red_4 (z : ℂ) (h : Qc z = 0) :
    z ^ 4 = ((-1 : ℂ)) + ((1 / 2 : ℂ) * (r3 : ℂ) + (-1 / 2 : ℂ) * I) * z + ((-1 / 2 : ℂ)) * z ^ 2 + ((1 / 2 : ℂ) * (r3 : ℂ) + (1 / 2 : ℂ) * I) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ)) * h + ((0 : ℂ)) * hr3c + ((0 : ℂ)) * Complex.I_sq

lemma red_5 (z : ℂ) (h : Qc z = 0) :
    z ^ 5 = ((-1 / 2 : ℂ) * (r3 : ℂ) + (-1 / 2 : ℂ) * I) + ((0 : ℂ)) * z + ((1 / 4 : ℂ) * (r3 : ℂ) + (-3 / 4 : ℂ) * I) * z ^ 2 + ((1 / 2 : ℂ) * (r3 : ℂ) * I) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z + (1 / 2 : ℂ) * (r3 : ℂ) + (1 / 2 : ℂ) * I) * h + ((1 / 4 : ℂ) * z ^ 3 + (1 / 4 : ℂ) * z) * hr3c + ((1 / 4 : ℂ) * z ^ 3 + (-1 / 4 : ℂ) * z) * Complex.I_sq

lemma red_6 (z : ℂ) (h : Qc z = 0) :
    z ^ 6 = ((-1 / 2 : ℂ) * (r3 : ℂ) * I) + ((-1 / 4 : ℂ) * (r3 : ℂ) + (1 / 4 : ℂ) * I) * z + ((-1 / 4 : ℂ) * (r3 : ℂ) * I) * z ^ 2 + ((0 : ℂ)) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z ^ 2 + (1 / 2 : ℂ) * z * (r3 : ℂ) + (1 / 2 : ℂ) * z * I + (1 / 2 : ℂ) * (r3 : ℂ) * I) * h + ((1 / 4 : ℂ) * z ^ 4 + (1 / 4 : ℂ) * z ^ 3 * I + (1 / 4 : ℂ) * z ^ 2 + (1 / 4 : ℂ) * z * I) * hr3c + ((1 / 4 : ℂ) * z ^ 4 + (1 / 4 : ℂ) * z ^ 3 * (r3 : ℂ) + (-1 / 4 : ℂ) * z ^ 2 + (-1 / 4 : ℂ) * z * (r3 : ℂ)) * Complex.I_sq

lemma red_8 (z : ℂ) (h : Qc z = 0) :
    z ^ 8 = ((1 / 4 : ℂ) * (r3 : ℂ) * I) + ((-1 / 8 : ℂ) * (r3 : ℂ) + (-3 / 8 : ℂ) * I) * z + ((-3 / 8 : ℂ) * (r3 : ℂ) * I) * z ^ 2 + ((-1 / 8 : ℂ) * (r3 : ℂ) + (-1 / 8 : ℂ) * I) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z ^ 4 + (1 / 2 : ℂ) * z ^ 3 * (r3 : ℂ) + (1 / 2 : ℂ) * z ^ 3 * I + (1 / 2 : ℂ) * z ^ 2 * (r3 : ℂ) * I + (-1 / 4 : ℂ) * (r3 : ℂ) * I) * h + ((1 / 4 : ℂ) * z ^ 6 + (1 / 4 : ℂ) * z ^ 5 * I + (1 / 4 : ℂ) * z ^ 4 + (1 / 8 : ℂ) * z ^ 3 * I + (-1 / 8 : ℂ) * z * I) * hr3c + ((1 / 4 : ℂ) * z ^ 6 + (1 / 4 : ℂ) * z ^ 5 * (r3 : ℂ) + (-1 / 4 : ℂ) * z ^ 4 + (-3 / 8 : ℂ) * z ^ 3 * (r3 : ℂ) + (1 / 8 : ℂ) * z * (r3 : ℂ)) * Complex.I_sq

lemma red_10 (z : ℂ) (h : Qc z = 0) :
    z ^ 10 = ((1 / 2 : ℂ) * (r3 : ℂ) * I + (1 / 8 : ℂ)) + ((-3 / 16 : ℂ) * (r3 : ℂ) + (-9 / 16 : ℂ) * I) * z + ((1 / 2 : ℂ) * (r3 : ℂ) * I + (-3 / 16 : ℂ)) * z ^ 2 + ((1 / 8 : ℂ) * (r3 : ℂ) + (-9 / 8 : ℂ) * I) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z ^ 6 + (1 / 2 : ℂ) * z ^ 5 * (r3 : ℂ) + (1 / 2 : ℂ) * z ^ 5 * I + (1 / 2 : ℂ) * z ^ 4 * (r3 : ℂ) * I + (-1 / 4 : ℂ) * z ^ 2 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z * (r3 : ℂ) + (-1 / 8 : ℂ) * z * I + (-1 / 2 : ℂ) * (r3 : ℂ) * I + (-1 / 8 : ℂ)) * h + ((1 / 4 : ℂ) * z ^ 8 + (1 / 4 : ℂ) * z ^ 7 * I + (1 / 4 : ℂ) * z ^ 6 + (1 / 8 : ℂ) * z ^ 5 * I + (-1 / 16 : ℂ) * z ^ 4 + (-3 / 8 : ℂ) * z ^ 3 * I + (-1 / 16 : ℂ) * z ^ 2 + (-1 / 4 : ℂ) * z * I) * hr3c + ((1 / 4 : ℂ) * z ^ 8 + (1 / 4 : ℂ) * z ^ 7 * (r3 : ℂ) + (-1 / 4 : ℂ) * z ^ 6 + (-3 / 8 : ℂ) * z ^ 5 * (r3 : ℂ) + (-1 / 16 : ℂ) * z ^ 4 + (-1 / 8 : ℂ) * z ^ 3 * (r3 : ℂ) + (1 / 16 : ℂ) * z ^ 2 + (1 / 4 : ℂ) * z * (r3 : ℂ)) * Complex.I_sq

lemma red_12 (z : ℂ) (h : Qc z = 0) :
    z ^ 12 = ((-9 / 16 : ℂ)) + ((5 / 32 : ℂ) * (r3 : ℂ) + (27 / 32 : ℂ) * I) * z + ((-1 / 8 : ℂ) * (r3 : ℂ) * I + (-17 / 32 : ℂ)) * z ^ 2 + ((1 / 32 : ℂ) * (r3 : ℂ) + (9 / 32 : ℂ) * I) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z ^ 8 + (1 / 2 : ℂ) * z ^ 7 * (r3 : ℂ) + (1 / 2 : ℂ) * z ^ 7 * I + (1 / 2 : ℂ) * z ^ 6 * (r3 : ℂ) * I + (-1 / 4 : ℂ) * z ^ 4 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z ^ 3 * (r3 : ℂ) + (-1 / 8 : ℂ) * z ^ 3 * I + (-1 / 2 : ℂ) * z ^ 2 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z ^ 2 + (1 / 8 : ℂ) * z * (r3 : ℂ) + (-9 / 8 : ℂ) * z * I + (9 / 16 : ℂ)) * h + ((1 / 4 : ℂ) * z ^ 10 + (1 / 4 : ℂ) * z ^ 9 * I + (1 / 4 : ℂ) * z ^ 8 + (1 / 8 : ℂ) * z ^ 7 * I + (-1 / 16 : ℂ) * z ^ 6 + (-3 / 8 : ℂ) * z ^ 5 * I + (-1 / 4 : ℂ) * z ^ 3 * I + (1 / 16 : ℂ) * z ^ 2) * hr3c + ((1 / 4 : ℂ) * z ^ 10 + (1 / 4 : ℂ) * z ^ 9 * (r3 : ℂ) + (-1 / 4 : ℂ) * z ^ 8 + (-3 / 8 : ℂ) * z ^ 7 * (r3 : ℂ) + (-1 / 16 : ℂ) * z ^ 6 + (-1 / 8 : ℂ) * z ^ 5 * (r3 : ℂ) + (-1 / 2 : ℂ) * z ^ 4 + (1 / 4 : ℂ) * z ^ 3 * (r3 : ℂ) + (9 / 16 : ℂ) * z ^ 2) * Complex.I_sq

lemma red_15 (z : ℂ) (h : Qc z = 0) :
    z ^ 15 = ((3 / 16 : ℂ) * (r3 : ℂ) + (-7 / 16 : ℂ) * I) + ((9 / 32 : ℂ) * (r3 : ℂ) * I + (9 / 16 : ℂ)) * z + ((-15 / 64 : ℂ) * (r3 : ℂ) + (-9 / 64 : ℂ) * I) * z ^ 2 + ((15 / 64 : ℂ) * (r3 : ℂ) * I + (-9 / 16 : ℂ)) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z ^ 11 + (1 / 2 : ℂ) * z ^ 10 * (r3 : ℂ) + (1 / 2 : ℂ) * z ^ 10 * I + (1 / 2 : ℂ) * z ^ 9 * (r3 : ℂ) * I + (-1 / 4 : ℂ) * z ^ 7 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z ^ 6 * (r3 : ℂ) + (-1 / 8 : ℂ) * z ^ 6 * I + (-1 / 2 : ℂ) * z ^ 5 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z ^ 5 + (1 / 8 : ℂ) * z ^ 4 * (r3 : ℂ) + (-9 / 8 : ℂ) * z ^ 4 * I + (9 / 16 : ℂ) * z ^ 3 + (1 / 32 : ℂ) * z ^ 2 * (r3 : ℂ) + (9 / 32 : ℂ) * z ^ 2 * I + (1 / 32 : ℂ) * z * (r3 : ℂ) * I + (-5 / 8 : ℂ) * z + (-3 / 16 : ℂ) * (r3 : ℂ) + (7 / 16 : ℂ) * I) * h + ((1 / 4 : ℂ) * z ^ 13 + (1 / 4 : ℂ) * z ^ 12 * I + (1 / 4 : ℂ) * z ^ 11 + (1 / 8 : ℂ) * z ^ 10 * I + (-1 / 16 : ℂ) * z ^ 9 + (-3 / 8 : ℂ) * z ^ 8 * I + (-1 / 4 : ℂ) * z ^ 6 * I + (5 / 64 : ℂ) * z ^ 5 + (1 / 64 : ℂ) * z ^ 4 * I + (-5 / 64 : ℂ) * z ^ 3 + (1 / 64 : ℂ) * z ^ 2 * I + (-3 / 32 : ℂ) * z) * hr3c + ((1 / 4 : ℂ) * z ^ 13 + (1 / 4 : ℂ) * z ^ 12 * (r3 : ℂ) + (-1 / 4 : ℂ) * z ^ 11 + (-3 / 8 : ℂ) * z ^ 10 * (r3 : ℂ) + (-1 / 16 : ℂ) * z ^ 9 + (-1 / 8 : ℂ) * z ^ 8 * (r3 : ℂ) + (-1 / 2 : ℂ) * z ^ 7 + (1 / 4 : ℂ) * z ^ 6 * (r3 : ℂ) + (45 / 64 : ℂ) * z ^ 5 + (1 / 64 : ℂ) * z ^ 4 * (r3 : ℂ) + (5 / 64 : ℂ) * z ^ 3 + (-1 / 64 : ℂ) * z ^ 2 * (r3 : ℂ) + (-7 / 32 : ℂ) * z) * Complex.I_sq

lemma red_20 (z : ℂ) (h : Qc z = 0) :
    z ^ 20 = ((-19 / 64 : ℂ) * (r3 : ℂ) * I + (-65 / 256 : ℂ)) + ((-63 / 512 : ℂ) * (r3 : ℂ) + (207 / 512 : ℂ) * I) * z + ((-13 / 64 : ℂ) * (r3 : ℂ) * I + (255 / 512 : ℂ)) * z ^ 2 + ((145 / 512 : ℂ) * (r3 : ℂ) + (225 / 512 : ℂ) * I) * z ^ 3 := by
  unfold Qc ω₀ ω₁ at h
  linear_combination ((1 : ℂ) * z ^ 16 + (1 / 2 : ℂ) * z ^ 15 * (r3 : ℂ) + (1 / 2 : ℂ) * z ^ 15 * I + (1 / 2 : ℂ) * z ^ 14 * (r3 : ℂ) * I + (-1 / 4 : ℂ) * z ^ 12 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z ^ 11 * (r3 : ℂ) + (-1 / 8 : ℂ) * z ^ 11 * I + (-1 / 2 : ℂ) * z ^ 10 * (r3 : ℂ) * I + (-1 / 8 : ℂ) * z ^ 10 + (1 / 8 : ℂ) * z ^ 9 * (r3 : ℂ) + (-9 / 8 : ℂ) * z ^ 9 * I + (9 / 16 : ℂ) * z ^ 8 + (1 / 32 : ℂ) * z ^ 7 * (r3 : ℂ) + (9 / 32 : ℂ) * z ^ 7 * I + (1 / 32 : ℂ) * z ^ 6 * (r3 : ℂ) * I + (-5 / 8 : ℂ) * z ^ 6 + (-3 / 16 : ℂ) * z ^ 5 * (r3 : ℂ) + (7 / 16 : ℂ) * z ^ 5 * I + (15 / 64 : ℂ) * z ^ 4 * (r3 : ℂ) * I + (-9 / 16 : ℂ) * z ^ 4 + (-81 / 128 : ℂ) * z ^ 3 * (r3 : ℂ) + (-9 / 128 : ℂ) * z ^ 3 * I + (-3 / 16 : ℂ) * z ^ 2 * (r3 : ℂ) * I + (-9 / 128 : ℂ) * z ^ 2 + (51 / 128 : ℂ) * z * (r3 : ℂ) + (-11 / 128 : ℂ) * z * I + (19 / 64 : ℂ) * (r3 : ℂ) * I + (65 / 256 : ℂ)) * h + ((1 / 4 : ℂ) * z ^ 18 + (1 / 4 : ℂ) * z ^ 17 * I + (1 / 4 : ℂ) * z ^ 16 + (1 / 8 : ℂ) * z ^ 15 * I + (-1 / 16 : ℂ) * z ^ 14 + (-3 / 8 : ℂ) * z ^ 13 * I + (-1 / 4 : ℂ) * z ^ 11 * I + (5 / 64 : ℂ) * z ^ 10 + (1 / 64 : ℂ) * z ^ 9 * I + (-5 / 64 : ℂ) * z ^ 8 + (17 / 128 : ℂ) * z ^ 7 * I + (-105 / 256 : ℂ) * z ^ 6 + (3 / 128 : ℂ) * z ^ 5 * I + (-15 / 128 : ℂ) * z ^ 4 + (7 / 128 : ℂ) * z ^ 3 * I + (51 / 256 : ℂ) * z ^ 2 + (19 / 128 : ℂ) * z * I) * hr3c + ((1 / 4 : ℂ) * z ^ 18 + (1 / 4 : ℂ) * z ^ 17 * (r3 : ℂ) + (-1 / 4 : ℂ) * z ^ 16 + (-3 / 8 : ℂ) * z ^ 15 * (r3 : ℂ) + (-1 / 16 : ℂ) * z ^ 14 + (-1 / 8 : ℂ) * z ^ 13 * (r3 : ℂ) + (-1 / 2 : ℂ) * z ^ 12 + (1 / 4 : ℂ) * z ^ 11 * (r3 : ℂ) + (45 / 64 : ℂ) * z ^ 10 + (1 / 64 : ℂ) * z ^ 9 * (r3 : ℂ) + (5 / 64 : ℂ) * z ^ 8 + (13 / 128 : ℂ) * z ^ 7 * (r3 : ℂ) + (-65 / 256 : ℂ) * z ^ 6 + (-27 / 128 : ℂ) * z ^ 5 * (r3 : ℂ) + (-1 / 128 : ℂ) * z ^ 4 + (31 / 128 : ℂ) * z ^ 3 * (r3 : ℂ) + (11 / 256 : ℂ) * z ^ 2 + (-19 / 128 : ℂ) * z * (r3 : ℂ)) * Complex.I_sq

end algebra

section bounds

noncomputable def yA : ℝ := yf xA
noncomputable def yB : ℝ := yf xB
noncomputable def yC : ℝ := yf xC
noncomputable def yD : ℝ := yf xD

lemma yA_bounds : (-180983 / 500000 : ℝ) < yA ∧ yA < (-72313 / 200000 : ℝ) := by
  obtain ⟨h1, h2, -⟩ := xA_spec
  obtain ⟨s1, s2⟩ := r3_bounds
  have e : yA = -4 * xA ^ 2 + r3 * xA + 3 / 2 := by simp only [yA, yf]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s1.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s2.le),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s2.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s1.le)]

lemma yB_bounds : (87607 / 125000 : ℝ) < yB ∧ yB < (701257 / 1000000 : ℝ) := by
  obtain ⟨h1, h2, -⟩ := xB_spec
  obtain ⟨s1, s2⟩ := r3_bounds
  have e : yB = -4 * xB ^ 2 + r3 * xB + 3 / 2 := by simp only [yB, yf]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s1.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s2.le),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s2.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s1.le)]

lemma yC_bounds : (978689 / 1000000 : ℝ) < yC ∧ yC < (97909 / 100000 : ℝ) := by
  obtain ⟨h1, h2, -⟩ := xC_spec
  obtain ⟨s1, s2⟩ := r3_bounds
  have e : yC = -4 * xC ^ 2 + r3 * xC + 3 / 2 := by simp only [yC, yf]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s1.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s2.le),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s2.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s1.le)]

lemma yD_bounds : (-818381 / 1000000 : ℝ) < yD ∧ yD < (-40899 / 50000 : ℝ) := by
  obtain ⟨h1, h2, -⟩ := xD_spec
  obtain ⟨s1, s2⟩ := r3_bounds
  have e : yD = -4 * xD ^ 2 + r3 * xD + 3 / 2 := by simp only [yD, yf]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s1.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s2.le),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s2.le), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 s1.le)]

/-- McCormick inequalities for a product. -/
lemma mcc {u v ulo uhi vlo vhi : ℝ} (hu1 : ulo ≤ u) (hu2 : u ≤ uhi) (hv1 : vlo ≤ v) (hv2 : v ≤ vhi) :
    ulo * v + u * vlo - ulo * vlo ≤ u * v ∧ uhi * v + u * vhi - uhi * vhi ≤ u * v ∧
      u * v ≤ uhi * v + u * vlo - uhi * vlo ∧ u * v ≤ ulo * v + u * vhi - ulo * vhi := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hv1),
    mul_nonneg (sub_nonneg.2 hu2) (sub_nonneg.2 hv2), mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hv2),
    mul_nonneg (sub_nonneg.2 hu2) (sub_nonneg.2 hv1)]

/-- The determinant of the diagonals and the numerators of Cramer's rule for `τ` and `μ`. -/
noncomputable def dt : ℝ := (xA - xC) * (yD - yB) - (yA - yC) * (xD - xB)
noncomputable def nt : ℝ := (xD - xC) * (yD - yB) - (yD - yC) * (xD - xB)
noncomputable def nm : ℝ := (xA - xC) * (yD - yC) - (yA - yC) * (xD - xC)

lemma dt_bounds : -3.457 < dt ∧ dt < -3.450 := by
  obtain ⟨a1, a2, -⟩ := xA_spec; obtain ⟨b1, b2, -⟩ := xB_spec
  obtain ⟨c1, c2, -⟩ := xC_spec; obtain ⟨d1, d2, -⟩ := xD_spec
  obtain ⟨e1, e2⟩ := yA_bounds; obtain ⟨f1, f2⟩ := yB_bounds
  obtain ⟨g1, g2⟩ := yC_bounds; obtain ⟨h1, h2⟩ := yD_bounds
  have m1 := mcc (u := xA - xC) (v := yD - yB) (ulo := (3552 / 3125 : ℝ)) (uhi := (56833 / 50000 : ℝ)) (vlo := (-759819 / 500000 : ℝ)) (vhi := (-379709 / 250000 : ℝ)) (by linarith) (by linarith) (by linarith) (by linarith)
  have m2 := mcc (u := yA - yC) (v := xD - xB) (ulo := (-20954 / 15625 : ℝ)) (uhi := (-670127 / 500000 : ℝ)) (vlo := (-16101 / 12500 : ℝ)) (vhi := (-64403 / 50000 : ℝ)) (by linarith) (by linarith) (by linarith) (by linarith)
  unfold dt; constructor <;> nlinarith [m1, m2]

lemma nt_bounds : -1.755 < nt ∧ nt < -1.748 := by
  obtain ⟨b1, b2, -⟩ := xB_spec
  obtain ⟨c1, c2, -⟩ := xC_spec; obtain ⟨d1, d2, -⟩ := xD_spec
  obtain ⟨f1, f2⟩ := yB_bounds
  obtain ⟨g1, g2⟩ := yC_bounds; obtain ⟨h1, h2⟩ := yD_bounds
  have m1 := mcc (u := xD - xC) (v := yD - yB) (ulo := (-37059 / 100000 : ℝ)) (uhi := (-37057 / 100000 : ℝ)) (vlo := (-759819 / 500000 : ℝ)) (vhi := (-379709 / 250000 : ℝ)) (by linarith) (by linarith) (by linarith) (by linarith)
  have m2 := mcc (u := yD - yC) (v := xD - xB) (ulo := (-1797471 / 1000000 : ℝ)) (uhi := (-1796669 / 1000000 : ℝ)) (vlo := (-16101 / 12500 : ℝ)) (vhi := (-64403 / 50000 : ℝ)) (by linarith) (by linarith) (by linarith) (by linarith)
  unfold nt; constructor <;> nlinarith [m1, m2]

lemma nm_bounds : -2.543 < nm ∧ nm < -2.536 := by
  obtain ⟨a1, a2, -⟩ := xA_spec
  obtain ⟨c1, c2, -⟩ := xC_spec; obtain ⟨d1, d2, -⟩ := xD_spec
  obtain ⟨e1, e2⟩ := yA_bounds
  obtain ⟨g1, g2⟩ := yC_bounds; obtain ⟨h1, h2⟩ := yD_bounds
  have m1 := mcc (u := xA - xC) (v := yD - yC) (ulo := (3552 / 3125 : ℝ)) (uhi := (56833 / 50000 : ℝ)) (vlo := (-1797471 / 1000000 : ℝ)) (vhi := (-1796669 / 1000000 : ℝ)) (by linarith) (by linarith) (by linarith) (by linarith)
  have m2 := mcc (u := yA - yC) (v := xD - xC) (ulo := (-20954 / 15625 : ℝ)) (uhi := (-670127 / 500000 : ℝ)) (vlo := (-37059 / 100000 : ℝ)) (vhi := (-37057 / 100000 : ℝ)) (by linarith) (by linarith) (by linarith) (by linarith)
  unfold nm; constructor <;> nlinarith [m1, m2]

noncomputable def τu : ℝ := nt / dt
noncomputable def μu : ℝ := nm / dt

lemma τu_bounds : 0.505 < τu ∧ τu < 0.509 := by
  obtain ⟨a1, a2⟩ := dt_bounds; obtain ⟨b1, b2⟩ := nt_bounds
  unfold τu
  constructor
  · rw [lt_div_iff_of_neg (by linarith)]; nlinarith
  · rw [div_lt_iff_of_neg (by linarith)]; nlinarith

lemma μu_bounds : 0.733 < μu ∧ μu < 0.738 := by
  obtain ⟨a1, a2⟩ := dt_bounds; obtain ⟨b1, b2⟩ := nm_bounds
  unfold μu
  constructor
  · rw [lt_div_iff_of_neg (by linarith)]; nlinarith
  · rw [div_lt_iff_of_neg (by linarith)]; nlinarith

/-- `t = Im m(2)`, computed from the coordinates. -/
noncomputable def tt' : ℝ := -2 * (τu * (xA * yA) - μu * (xB * yB) + (1 - τu) * (xC * yC) - (1 - μu) * (xD * yD))

lemma tt'_bound : 1.4 < tt' := by
  obtain ⟨a1, a2, -⟩ := xA_spec; obtain ⟨b1, b2, -⟩ := xB_spec
  obtain ⟨c1, c2, -⟩ := xC_spec; obtain ⟨d1, d2, -⟩ := xD_spec
  obtain ⟨e1, e2⟩ := yA_bounds; obtain ⟨f1, f2⟩ := yB_bounds
  obtain ⟨g1, g2⟩ := yC_bounds; obtain ⟨h1, h2⟩ := yD_bounds
  obtain ⟨t1, t2⟩ := τu_bounds; obtain ⟨u1, u2⟩ := μu_bounds
  have pA := mcc (u := xA) (v := yA) a1 a2 e1.le e2.le
  have pB := mcc (u := xB) (v := yB) b1 b2 f1.le f2.le
  have pC := mcc (u := xC) (v := yC) c1 c2 g1.le g2.le
  have pD := mcc (u := xD) (v := yD) d1 d2 h1.le h2.le
  have qA := mcc (u := τu) (v := xA * yA) (vlo := (-33747 / 100000 : ℝ)) (vhi := (-16853 / 50000 : ℝ)) t1.le t2.le (by linarith [pA.1, pA.2.1]) (by linarith [pA.2.2.1, pA.2.2.2])
  have qB := mcc (u := μu) (v := xB * yB) (vlo := (49977 / 100000 : ℝ)) (vhi := (50009 / 100000 : ℝ)) u1.le u2.le (by linarith [pB.1, pB.2.1]) (by linarith [pB.2.2.1, pB.2.2.2])
  have qC := mcc (u := τu) (v := xC * yC) (vlo := (-20013 / 100000 : ℝ)) (vhi := (-20001 / 100000 : ℝ)) t1.le t2.le (by linarith [pC.1, pC.2.1]) (by linarith [pC.2.2.1, pC.2.2.2])
  have qD := mcc (u := μu) (v := xD * yD) (vlo := (47029 / 100000 : ℝ)) (vhi := (2941 / 6250 : ℝ)) u1.le u2.le (by linarith [pD.1, pD.2.1]) (by linarith [pD.2.2.1, pD.2.2.2])
  unfold tt'
  linarith [qA.1, qA.2.1, qA.2.2.1, qA.2.2.2, qB.1, qB.2.1, qB.2.2.1, qB.2.2.2, qC.1, qC.2.1, qC.2.2.1,
    qC.2.2.2, qD.1, qD.2.1, qD.2.2.1, qD.2.2.2]

end bounds

section feet

lemma fA_re : (foot' xA).re = xA := rfl
lemma fA_im : (foot' xA).im = yA := rfl
lemma fB_re : (foot' xB).re = xB := rfl
lemma fB_im : (foot' xB).im = yB := rfl
lemma fC_re : (foot' xC).re = xC := rfl
lemma fC_im : (foot' xC).im = yC := rfl
lemma fD_re : (foot' xD).re = xD := rfl
lemma fD_im : (foot' xD).im = yD := rfl

lemma dt_ne : dt ≠ 0 := by linarith [dt_bounds.2]

/-- The feet of the table of Proposition 5.8. -/
noncomputable def uF : Feet where
  A := foot' xA
  B := foot' xB
  C := foot' xC
  D := foot' xD
  τ := τu
  μ := μu
  nA := norm_foot' xA_spec.2.2
  nB := norm_foot' xB_spec.2.2
  nC := norm_foot' xC_spec.2.2
  nD := norm_foot' xD_spec.2.2
  hX := by
    have h := dt_ne
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, fA_re, fA_im, fB_re, fB_im, fC_re, fC_im, fD_re, fD_im,
      zero_mul, sub_zero, add_zero, τu, μu] <;> field_simp <;> unfold dt nt nm <;> ring
  τ0 := by linarith [τu_bounds.1]
  τ1 := by linarith [τu_bounds.2]
  μ0 := by linarith [μu_bounds.1]
  μ1 := by linarith [μu_bounds.2]
  AB := ne_of_re (by rw [fA_re, fB_re]; linarith [xA_spec.1, xB_spec.2.1])
  AC := ne_of_re (by rw [fA_re, fC_re]; linarith [xA_spec.1, xC_spec.2.1])
  AD := ne_of_re (by rw [fA_re, fD_re]; linarith [xA_spec.1, xD_spec.2.1])
  BC := ne_of_re (by rw [fB_re, fC_re]; linarith [xB_spec.1, xC_spec.2.1])
  BD := ne_of_re (by rw [fB_re, fD_re]; linarith [xB_spec.1, xD_spec.2.1])
  CD := ne_of_re (by rw [fC_re, fD_re]; linarith [xC_spec.1, xD_spec.2.1])

lemma QA : Qc uF.A = 0 := Qc_foot' xA_spec.2.2
lemma QB : Qc uF.B = 0 := Qc_foot' xB_spec.2.2
lemma QC : Qc uF.C = 0 := Qc_foot' xC_spec.2.2
lemma QD : Qc uF.D = 0 := Qc_foot' xD_spec.2.2

/-- `m(j) = c₂ m(2) + c₃ m(3)` when `z^j ≡ c₀ + c₁ z + c₂ z² + c₃ z³ mod Q`. -/
lemma m_red {j : ℕ} {c0 c1 c2 c3 : ℂ}
    (hred : ∀ z : ℂ, Qc z = 0 → z ^ j = c0 + c1 * z + c2 * z ^ 2 + c3 * z ^ 3) :
    uF.m j = c2 * uF.m 2 + c3 * uF.m 3 := by
  have hX := uF.hX
  simp only [Feet.m]
  rw [hred _ QA, hred _ QB, hred _ QC, hred _ QD]
  push_cast at hX ⊢
  linear_combination (-c1) * hX

lemma interp5 {z : ℂ} (hQ : Qc z = 0) (hn : z * conj z = 1) :
    z ^ 5 = ((-1 / 4 : ℂ) * (r3 : ℂ) + (1 / 4 : ℂ) * I) + ((-1 / 4 : ℂ) * (r3 : ℂ) * I) * z
      + ((-1 / 2 : ℂ) * (r3 : ℂ) * I) * conj z := by
  have h6 := red_6 z hQ
  linear_combination conj z * h6 - (z ^ 5 - ((-1 / 4 : ℂ) * (r3 : ℂ) + (1 / 4 : ℂ) * I)
    - ((-1 / 4 : ℂ) * (r3 : ℂ) * I) * z) * hn

lemma uF_interp : uF.Interp 5 ((-1 / 4 : ℂ) * (r3 : ℂ) + (1 / 4 : ℂ) * I) ((-1 / 4 : ℂ) * (r3 : ℂ) * I)
    ((-1 / 2 : ℂ) * (r3 : ℂ) * I) :=
  ⟨interp5 QA (foot'_mul_conj xA_spec.2.2), interp5 QB (foot'_mul_conj xB_spec.2.2),
    interp5 QC (foot'_mul_conj xC_spec.2.2), interp5 QD (foot'_mul_conj xD_spec.2.2)⟩

/-- `5` is a degenerate mode. -/
lemma uF_m5 : uF.m 5 = 0 := (uF.m_eq_zero_iff 5).2 ⟨_, _, _, uF_interp⟩

lemma r3I_ne : (r3 : ℂ) * I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 r3_pos.ne') Complex.I_ne_zero

/-- `m(3) = ω m(2)`. -/
lemma uF_m3 : uF.m 3 = ω₀ * uF.m 2 := by
  have h5 := m_red (red_5)
  rw [uF_m5] at h5
  have : (1 / 2 : ℂ) * (r3 : ℂ) * I * (uF.m 3 - ω₀ * uF.m 2) = 0 := by
    unfold ω₀
    linear_combination -h5 + ((-1 / 4 : ℂ) * I * uF.m 2) * hr3c + ((-1 / 4 : ℂ) * (r3 : ℂ) * uF.m 2) * Complex.I_sq
  have hne : (1 / 2 : ℂ) * (r3 : ℂ) * I ≠ 0 := by
    rw [mul_assoc]; exact mul_ne_zero (by norm_num) r3I_ne
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)

lemma uF_m4 : uF.m 4 = ((1 / 2 : ℂ) * (r3 : ℂ) * I) * uF.m 2 := by
  rw [m_red red_4, uF_m3]
  unfold ω₀
  linear_combination ((1 / 4 : ℂ) * uF.m 2) * hr3c + ((1 / 4 : ℂ) * uF.m 2) * Complex.I_sq

lemma uF_m2_im : (uF.m 2).im = tt' := by
  simp only [Feet.m, uF, pow_two, Complex.neg_im, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, fA_re, fA_im, fB_re, fB_im, fC_re, fC_im,
    fD_re, fD_im, zero_mul, add_zero]
  unfold tt'; ring

/-- `m(2) = i t` is purely imaginary. -/
lemma uF_m2 : uF.m 2 = I * (tt' : ℂ) := by
  obtain ⟨-, e4, -⟩ := uF.interp_coeffs (by norm_num) uF_m5 uF_interp
  rw [show 5 - 1 = 4 from rfl, uF_m4] at e4
  have h : (1 / 2 : ℂ) * (r3 : ℂ) * I * (uF.m 2 + conj (uF.m 2)) = 0 := by linear_combination e4
  have hne : (1 / 2 : ℂ) * (r3 : ℂ) * I ≠ 0 := by
    rw [mul_assoc]; exact mul_ne_zero (by norm_num) r3I_ne
  have h2 := (mul_eq_zero.1 h).resolve_left hne
  have hre : (uF.m 2).re = 0 := by
    have := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this; linarith
  apply Complex.ext <;> simp [hre, uF_m2_im]

end feet

section W3

/-- `b = -80 e^{iπ/6}`, `ξ₊ = -(√3/2) i`, `ξ₋ = (√3/4) i` and the coefficients of `g₃`. -/
noncomputable def bU : ℂ := -40 * ((r3 : ℂ) + I)
noncomputable def Xc : ℂ := -((r3 : ℂ) * I) / 2
noncomputable def Yc : ℂ := (r3 : ℂ) * I / 4
noncomputable def a10 : ℂ := -1299 / 100 + 5 * I
noncomputable def a15 : ℂ := 153 / 200 + 379 / 1000 * I
noncomputable def a20 : ℂ := 2023 / 500 - 994 / 125 * I

lemma uX : uF.m (5 - 1) / conj (uF.m 2) = Xc := by
  rw [show 5 - 1 = 4 from rfl, uF_m4, uF_m2]
  have ht : (tt' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith [tt'_bound])
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [div_eq_iff (by simp [ht])]
  unfold Xc; ring

lemma uY : conj (uF.m (5 + 1)) / conj (uF.m 2) = Yc := by
  obtain ⟨e6, -, -⟩ := uF.interp_coeffs (by norm_num) uF_m5 uF_interp
  rw [e6, uF_m2]
  have ht : (tt' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith [tt'_bound])
  simp only [map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_one]
  rw [div_eq_iff (by simp [ht])]
  unfold Yc; ring

lemma u_m3 : uF.m 3 = ω₀ * (I * (tt' : ℂ)) := by rw [uF_m3, uF_m2]

lemma u_m8 : uF.m 8 = ((-1 / 2 : ℂ) * (r3 : ℂ) * I + (-1 / 8 : ℂ)) * (I * (tt' : ℂ)) := by
  rw [m_red red_8, uF_m3, uF_m2]
  unfold ω₀
  linear_combination ((-1 / 16 : ℂ) * I * (tt' : ℂ)) * hr3c + ((-1 / 16 : ℂ) * I * (tt' : ℂ)) * Complex.I_sq

lemma u_m10 : uF.m 10 = ((9 / 16 : ℂ)) * (I * (tt' : ℂ)) := by
  rw [m_red red_10, uF_m3, uF_m2]
  unfold ω₀
  linear_combination ((1 / 16 : ℂ) * I * (tt' : ℂ)) * hr3c + ((-9 / 16 : ℂ) * I * (tt' : ℂ)) * Complex.I_sq

lemma u_m12 : uF.m 12 = ((1 / 32 : ℂ) * (r3 : ℂ) * I + (-5 / 8 : ℂ)) * (I * (tt' : ℂ)) := by
  rw [m_red red_12, uF_m3, uF_m2]
  unfold ω₀
  linear_combination ((1 / 64 : ℂ) * I * (tt' : ℂ)) * hr3c + ((9 / 64 : ℂ) * I * (tt' : ℂ)) * Complex.I_sq

lemma u_m15 : uF.m 15 = ((-81 / 128 : ℂ) * (r3 : ℂ) + (-9 / 128 : ℂ) * I) * (I * (tt' : ℂ)) := by
  rw [m_red red_15, uF_m3, uF_m2]
  unfold ω₀
  linear_combination ((15 / 128 : ℂ) * I ^ 2 * (tt' : ℂ)) * hr3c + ((15 / 128 : ℂ) * (r3 : ℂ) * I * (tt' : ℂ)) * Complex.I_sq

lemma u_m20 : uF.m 20 = ((81 / 512 : ℂ) * (r3 : ℂ) * I + (45 / 64 : ℂ)) * (I * (tt' : ℂ)) := by
  rw [m_red red_20, uF_m3, uF_m2]
  unfold ω₀
  linear_combination ((145 / 1024 : ℂ) * I * (tt' : ℂ)) * hr3c + ((225 / 1024 : ℂ) * I * (tt' : ℂ)) * Complex.I_sq

lemma norm_re_im_le {a b B : ℝ} (hB : 0 ≤ B) (h : a ^ 2 + b ^ 2 ≤ B ^ 2) : ‖(a : ℂ) + (b : ℂ) * I‖ ≤ B := by
  rw [← Complex.mk_eq_add_mul_I, Complex.norm_def, Complex.normSq_mk]
  rw [Real.sqrt_le_left hB]; nlinarith

lemma u_κ : uF.κ 5 bU Xc Yc = 45 / 32 * tt' := by
  unfold Feet.κ
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, u_m12, u_m10, u_m8]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, re_eq_complex]
  simp only [bU, Xc, Yc]
  simp only [map_mul, map_add, map_neg, map_sub, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_one]
  push_cast
  linear_combination ((15 / 128 : ℂ) * (r3 : ℂ) ^ 2 * I ^ 4 * (tt' : ℂ) + (15 / 32 : ℂ) * I ^ 4 * (tt' : ℂ)) * hr3c + ((45 / 32 : ℂ) * I ^ 2 * (tt' : ℂ) + (-45 / 32 : ℂ) * (tt' : ℂ)) * Complex.I_sq

lemma u_A : ‖((5 : ℕ) : ℂ) / 4 * (2 * uF.m (5 - 2) * Xc * Yc + conj (uF.m (5 - 2)) * conj Yc ^ 2)‖ ≤ 1.0741 * tt' := by
  have e : ((5 : ℕ) : ℂ) / 4 * (2 * uF.m (5 - 2) * Xc * Yc + conj (uF.m (5 - 2)) * conj Yc ^ 2) = (((((-45 / 128 : ℝ) + (0 / 1 : ℝ) * r3)) * tt' : ℝ) : ℂ) + (((((0 / 1 : ℝ) + (75 / 128 : ℝ) * r3)) * tt' : ℝ) : ℂ) * I := by
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, u_m3, u_m8, u_m10, u_m12, u_m15, u_m20]
    simp only [bU, Xc, Yc, a10, a15, a20, ω₀]
    try simp only [map_mul, map_add, map_neg, map_sub, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_one, map_natCast]
    push_cast
    linear_combination ((-25 / 128 : ℂ) * (r3 : ℂ) * I ^ 3 * (tt' : ℂ) + (-15 / 128 : ℂ) * I ^ 4 * (tt' : ℂ)) * hr3c + ((-75 / 128 : ℂ) * (r3 : ℂ) * I * (tt' : ℂ) + (-45 / 128 : ℂ) * I ^ 2 * (tt' : ℂ) + (45 / 128 : ℂ) * (tt' : ℂ)) * Complex.I_sq
  rw [e]
  apply norm_re_im_le (le_of_lt (by linarith [tt'_bound]))
  have ht := tt'_bound
  obtain ⟨s1, s2⟩ := r3_bounds
  have h3 := hr3
  have hc : (((-45 / 128 : ℝ) + (0 / 1 : ℝ) * r3)) ^ 2 + (((0 / 1 : ℝ) + (75 / 128 : ℝ) * r3)) ^ 2 ≤ 1.0741 ^ 2 := by nlinarith
  have : 0 ≤ tt' ^ 2 := sq_nonneg _
  nlinarith

lemma u_r10 : ‖uF.W2 5 bU Xc Yc - uF.m (2 * 5) * a10‖ ≤ 0.0003 * tt' := by
  have e : uF.W2 5 bU Xc Yc - uF.m (2 * 5) * a10 = (((((0 / 1 : ℝ) + (0 / 1 : ℝ) * r3)) * tt' : ℝ) : ℂ) + (((((11691 / 1600 : ℝ) + (-135 / 32 : ℝ) * r3)) * tt' : ℝ) : ℂ) * I := by
    simp only [Feet.W2, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, u_m3, u_m8, u_m10, u_m12, u_m15, u_m20]
    simp only [bU, Xc, Yc, a10, a15, a20, ω₀]
    try simp only [map_mul, map_add, map_neg, map_sub, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_one, map_natCast]
    push_cast
    linear_combination ((-75 / 128 : ℂ) * (r3 : ℂ) ^ 2 * I ^ 4 * (tt' : ℂ) + (-75 / 128 : ℂ) * (r3 : ℂ) * I ^ 5 * (tt' : ℂ) + (105 / 128 : ℂ) * (r3 : ℂ) * I ^ 3 * (tt' : ℂ) + (-15 / 16 : ℂ) * I ^ 4 * (tt' : ℂ)) * hr3c + ((-225 / 128 : ℂ) * (r3 : ℂ) * I ^ 3 * (tt' : ℂ) + (135 / 32 : ℂ) * (r3 : ℂ) * I * (tt' : ℂ) + (-45 / 16 : ℂ) * I ^ 2 * (tt' : ℂ)) * Complex.I_sq
  rw [e]
  apply norm_re_im_le (le_of_lt (by linarith [tt'_bound]))
  have ht := tt'_bound
  obtain ⟨s1, s2⟩ := r3_bounds
  have h3 := hr3
  have hc : (((0 / 1 : ℝ) + (0 / 1 : ℝ) * r3)) ^ 2 + (((11691 / 1600 : ℝ) + (-135 / 32 : ℝ) * r3)) ^ 2 ≤ 0.0003 ^ 2 := by nlinarith
  have : 0 ≤ tt' ^ 2 := sq_nonneg _
  nlinarith

lemma u_r15 : ‖((5 : ℕ) : ℂ) / 4 * (uF.m (5 - 2) * Xc ^ 2) - uF.m (3 * 5) * a15‖ ≤ 0.0005 * tt' := by
  have e : ((5 : ℕ) : ℂ) / 4 * (uF.m (5 - 2) * Xc ^ 2) - uF.m (3 * 5) * a15 = (((((10623 / 25600 : ℝ) + (-30699 / 128000 : ℝ) * r3)) * tt' : ℝ) : ℂ) + (((((-3411 / 128000 : ℝ) + (393 / 25600 : ℝ) * r3)) * tt' : ℝ) : ℂ) * I := by
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, u_m3, u_m8, u_m10, u_m12, u_m15, u_m20]
    simp only [bU, Xc, Yc, a10, a15, a20, ω₀]
    try simp only [map_mul, map_add, map_neg, map_sub, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_one, map_natCast]
    push_cast
    linear_combination ((5 / 32 : ℂ) * (r3 : ℂ) * I ^ 3 * (tt' : ℂ) + (5 / 32 : ℂ) * I ^ 4 * (tt' : ℂ)) * hr3c + ((15 / 32 : ℂ) * (r3 : ℂ) * I * (tt' : ℂ) + (30699 / 128000 : ℂ) * (r3 : ℂ) * (tt' : ℂ) + (15 / 32 : ℂ) * I ^ 2 * (tt' : ℂ) + (3411 / 128000 : ℂ) * I * (tt' : ℂ) + (-10623 / 25600 : ℂ) * (tt' : ℂ)) * Complex.I_sq
  rw [e]
  apply norm_re_im_le (le_of_lt (by linarith [tt'_bound]))
  have ht := tt'_bound
  obtain ⟨s1, s2⟩ := r3_bounds
  have h3 := hr3
  have hc : (((10623 / 25600 : ℝ) + (-30699 / 128000 : ℝ) * r3)) ^ 2 + (((-3411 / 128000 : ℝ) + (393 / 25600 : ℝ) * r3)) ^ 2 ≤ 0.0005 ^ 2 := by nlinarith
  have : 0 ≤ tt' ^ 2 := sq_nonneg _
  nlinarith

lemma u_r20 : ‖uF.W4 5 bU Xc Yc - uF.m (4 * 5) * a20‖ ≤ 0.0003 * tt' := by
  have e : uF.W4 5 bU Xc Yc - uF.m (4 * 5) * a20 = (((((-14193 / 12800 : ℝ) + (163863 / 256000 : ℝ) * r3)) * tt' : ℝ) : ℂ) + (((((-18207 / 6400 : ℝ) + (105111 / 64000 : ℝ) * r3)) * tt' : ℝ) : ℂ) * I := by
    simp only [Feet.W4, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, u_m3, u_m8, u_m10, u_m12, u_m15, u_m20]
    simp only [bU, Xc, Yc, a10, a15, a20, ω₀]
    try simp only [map_mul, map_add, map_neg, map_sub, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_one, map_natCast]
    push_cast
    linear_combination ((315 / 512 : ℂ) * (r3 : ℂ) ^ 2 * I ^ 4 * (tt' : ℂ) + (315 / 512 : ℂ) * (r3 : ℂ) * I ^ 5 * (tt' : ℂ) + (-45 / 128 : ℂ) * (r3 : ℂ) * I ^ 3 * (tt' : ℂ) + (765 / 512 : ℂ) * I ^ 4 * (tt' : ℂ)) * hr3c + ((945 / 512 : ℂ) * (r3 : ℂ) * I ^ 3 * (tt' : ℂ) + (-105111 / 64000 : ℂ) * (r3 : ℂ) * I * (tt' : ℂ) + (-163863 / 256000 : ℂ) * (r3 : ℂ) * (tt' : ℂ) + (2295 / 512 : ℂ) * I ^ 2 * (tt' : ℂ) + (14193 / 12800 : ℂ) * (tt' : ℂ)) * Complex.I_sq
  rw [e]
  apply norm_re_im_le (le_of_lt (by linarith [tt'_bound]))
  have ht := tt'_bound
  obtain ⟨s1, s2⟩ := r3_bounds
  have h3 := hr3
  have hc : (((-14193 / 12800 : ℝ) + (163863 / 256000 : ℝ) * r3)) ^ 2 + (((-18207 / 6400 : ℝ) + (105111 / 64000 : ℝ) * r3)) ^ 2 ≤ 0.0003 ^ 2 := by nlinarith
  have : 0 ≤ tt' ^ 2 := sq_nonneg _
  nlinarith

/-- The lower bound `W₃ ≥ 0.45` (Proposition 5.8). -/
lemma u_W3_bound : 0.45 ≤ uF.κ 5 bU Xc Yc
    - ‖((5 : ℕ) : ℂ) / 4 * (2 * uF.m (5 - 2) * Xc * Yc + conj (uF.m (5 - 2)) * conj Yc ^ 2)‖
    - ‖uF.W2 5 bU Xc Yc - uF.m (2 * 5) * a10‖
    - ‖((5 : ℕ) : ℂ) / 4 * (uF.m (5 - 2) * Xc ^ 2) - uF.m (3 * 5) * a15‖
    - ‖uF.W4 5 bU Xc Yc - uF.m (4 * 5) * a20‖ := by
  rw [u_κ]
  linarith [u_A, u_r10, u_r15, u_r20, tt'_bound]

end W3

section tableU

lemma uAC : foot' xA - foot' xC = ⟨xA - xC, yA - yC⟩ := by
  apply Complex.ext <;> simp [foot', yA, yC]
lemma uBD : foot' xB - foot' xD = ⟨xB - xD, yB - yD⟩ := by
  apply Complex.ext <;> simp [foot', yB, yD]

lemma diag_bounds : 3 ≤ (xA - xC) ^ 2 + (yA - yC) ^ 2 ∧ 3.9 ≤ (xB - xD) ^ 2 + (yB - yD) ^ 2 ∧
    |(xA - xC) * (xB - xD) + (yA - yC) * (yB - yD)| ≤ 0.6 := by
  obtain ⟨a1, a2, -⟩ := xA_spec; obtain ⟨b1, b2, -⟩ := xB_spec
  obtain ⟨c1, c2, -⟩ := xC_spec; obtain ⟨d1, d2, -⟩ := xD_spec
  obtain ⟨e1, e2⟩ := yA_bounds; obtain ⟨f1, f2⟩ := yB_bounds
  obtain ⟨g1, g2⟩ := yC_bounds; obtain ⟨h1, h2⟩ := yD_bounds
  refine ⟨by nlinarith, by nlinarith, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

lemma abs_dot_unit_le {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (h : dot u v ^ 2 ≤ c ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2)) : |dot (unit u) (unit v)| ≤ c := by
  have hu0 := norm_pos_iff.2 hu
  have hv0 := norm_pos_iff.2 hv
  unfold unit
  rw [dot_real_mul_left, dot_real_mul_right, abs_mul, abs_mul, abs_inv, abs_inv, abs_norm, abs_norm]
  rw [show ‖u‖⁻¹ * (‖v‖⁻¹ * |dot u v|) = |dot u v| / (‖u‖ * ‖v‖) by field_simp, div_le_iff₀ (by positivity)]
  have : |dot u v| ^ 2 ≤ (c * (‖u‖ * ‖v‖)) ^ 2 := by rw [sq_abs]; nlinarith
  exact abs_le_of_sq_le_sq' this (by positivity) |>.2 |>.trans (le_abs_self _) |>.trans (by
    rw [abs_of_nonneg (by positivity)])

lemma u_γ : |dot (unit (foot' xA - foot' xC)) (unit (foot' xB - foot' xD))| ≤ 1 / 2 := by
  obtain ⟨h1, h2, h3⟩ := diag_bounds
  apply abs_dot_unit_le (u := foot' xA - foot' xC) (v := foot' xB - foot' xD) (sub_ne_zero.2 uF.AC)
    (sub_ne_zero.2 uF.BD) (by norm_num)
  rw [uAC, uBD, sq_norm_eq, sq_norm_eq]
  simp only [dot]
  have : ((xA - xC) * (xB - xD) + (yA - yC) * (yB - yD)) ^ 2 ≤ 0.36 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ((xA - xC) * (xB - xD) + (yA - yC) * (yB - yD))]
  nlinarith

/-- The table of Proposition 5.8, with `r = 1`. -/
noncomputable def uT : Table where
  A := foot' xA
  B := foot' xB
  C := foot' xC
  D := foot' xD
  r := 1
  normA := (norm_foot' xA_spec.2.2).le
  normB := (norm_foot' xB_spec.2.2).le
  normC := (norm_foot' xC_spec.2.2).le
  normD := (norm_foot' xD_spec.2.2).le
  AC_ne := uF.AC
  BD_ne := uF.BD
  not_parallel := lt_of_le_of_lt u_γ (by norm_num)

lemma uT_K : uT.K ≤ 2 := by
  have h := u_γ
  have h0 : 0 ≤ uT.γ := abs_nonneg _
  have hγ : uT.γ ≤ 1 / 2 := h
  rw [Table.K, Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]
  linarith

lemma uT_dmin : 1.7 ≤ uT.dmin := by
  obtain ⟨h1, h2, -⟩ := diag_bounds
  have e1 : uT.d₁ = Real.sqrt ((xA - xC) ^ 2 + (yA - yC) ^ 2) := by
    show ‖foot' xA - foot' xC‖ = _; rw [uAC, Complex.norm_def, Complex.normSq_mk, sq, sq]
  have e2 : uT.d₂ = Real.sqrt ((xB - xD) ^ 2 + (yB - yD) ^ 2) := by
    show ‖foot' xB - foot' xD‖ = _; rw [uBD, Complex.norm_def, Complex.normSq_mk, sq, sq]
  rw [Table.dmin, e1, e2]
  apply le_min <;> rw [Real.le_sqrt (by norm_num) (by positivity)] <;> linarith

end tableU

section theorem58

open Table

/-- `g₃ = Re(a₁₀ z¹⁰ + a₁₅ z¹⁵ + a₂₀ z²⁰)`. -/
noncomputable def g3u : ℂ → ℝ := fun z => (a10 * z ^ (2 * 5) + a15 * z ^ (3 * 5) + a20 * z ^ (4 * 5)).re

lemma norm_bU : ‖bU‖ = 80 := by
  have : (r3 : ℂ) + I = ⟨r3, 1⟩ := by rw [Complex.mk_eq_add_mul_I]; simp
  have h1 : ‖(-40 : ℂ)‖ = 40 := by rw [norm_neg]; norm_num
  have h2 : ‖(⟨r3, 1⟩ : ℂ)‖ = 2 := by
    rw [Complex.norm_def, Complex.normSq_mk, show r3 * r3 + 1 * 1 = 2 ^ 2 by nlinarith [hr3],
      Real.sqrt_sq (by norm_num)]
  rw [bU, norm_mul, this, h1, h2]; norm_num

lemma norm_a10 : ‖a10‖ ≤ 13.92 := by
  have : a10 = ((-1299 / 100 : ℝ) : ℂ) + ((5 : ℝ) : ℂ) * I := by rw [a10]; push_cast; ring
  rw [this]; exact norm_re_im_le (by norm_num) (by norm_num)
lemma norm_a15 : ‖a15‖ ≤ 0.854 := by
  have : a15 = ((153 / 200 : ℝ) : ℂ) + ((379 / 1000 : ℝ) : ℂ) * I := by rw [a15]; push_cast; ring
  rw [this]; exact norm_re_im_le (by norm_num) (by norm_num)
lemma norm_a20 : ‖a20‖ ≤ 8.923 := by
  have : a20 = ((2023 / 500 : ℝ) : ℂ) + ((-994 / 125 : ℝ) : ℂ) * I := by rw [a20]; push_cast; ring
  rw [this]; exact norm_re_im_le (by norm_num) (by norm_num)

lemma g3u_lip (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : |g3u x - g3u y| ≤ 331 * ‖x - y‖ := by
  have e : g3u x - g3u y = (a10 * (x ^ 10 - y ^ 10) + a15 * (x ^ 15 - y ^ 15) + a20 * (x ^ 20 - y ^ 20)).re := by
    simp only [g3u, ← Complex.sub_re, Nat.reduceMul]; congr 1; ring
  rw [e]
  have h10 := norm_pow_sub_pow_le' hx hy 10
  have h15 := norm_pow_sub_pow_le' hx hy 15
  have h20 := norm_pow_sub_pow_le' hx hy 20
  push_cast at h10 h15 h20
  have n1 := norm_a10; have n2 := norm_a15; have n3 := norm_a20
  have hn := norm_nonneg (x - y)
  calc _ ≤ ‖a10 * (x ^ 10 - y ^ 10) + a15 * (x ^ 15 - y ^ 15) + a20 * (x ^ 20 - y ^ 20)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖a10 * (x ^ 10 - y ^ 10)‖ + ‖a15 * (x ^ 15 - y ^ 15)‖ + ‖a20 * (x ^ 20 - y ^ 20)‖ := norm_add₃_le
    _ = ‖a10‖ * ‖x ^ 10 - y ^ 10‖ + ‖a15‖ * ‖x ^ 15 - y ^ 15‖ + ‖a20‖ * ‖x ^ 20 - y ^ 20‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ 13.92 * (10 * ‖x - y‖) + 0.854 * (15 * ‖x - y‖) + 8.923 * (20 * ‖x - y‖) := by
        gcongr
    _ ≤ 331 * ‖x - y‖ := by nlinarith

lemma gk5_lip (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |gk 5 bU x - gk 5 bU y| ≤ 85 * ‖x - y‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => gk 5 bU (y + t • (x - y)))
    (f' := fun t => dot (Gk 5 bU (y + t • (x - y))) (x - y))
    (C := 85 * ‖x - y‖) (a := 0) (b := 1)
    (fun t _ => (hasDerivAt_gk 5 (by norm_num) bU y (x - y) t).hasDerivWithinAt)
    (fun t ht => by
      have hz := norm_line_le hx hy (Set.Ico_subset_Icc_self ht)
      have hG := norm_Gk_le 5 (by norm_num) bU _ hz (polyG_five _ (norm_nonneg _) hz)
      rw [norm_bU] at hG; push_cast at hG
      rw [Real.norm_eq_abs]
      exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
    1 ⟨zero_le_one, le_rfl⟩
  simpa [Real.norm_eq_abs] using key

lemma uF_m5' : uF.m 5 = 0 := uF_m5

lemma uT_F₀_g₁ (θ : ℝ) : F₀ uT (gk 5 bU) τu μu θ = 0 := by
  have n : ∀ a : ℂ, ‖a‖ = 1 → ‖rot θ * a‖ = 1 := fun a ha => by rw [norm_rot_mul, ha]
  have e : F₀ uT (gk 5 bU) τu μu θ = F₀ uT (fun z => (1 * z ^ 5).re) uF.τ uF.μ θ := by
    unfold F₀
    rw [gk_circle _ _ _ (n uT.A uF.nA), gk_circle _ _ _ (n uT.B uF.nB),
      gk_circle _ _ _ (n uT.C uF.nC), gk_circle _ _ _ (n uT.D uF.nD)]
    simp only [one_mul]; rfl
  rw [e, Table.F₀_monomial uF rfl rfl rfl rfl, uF_m5]; simp

lemma norm_r3I (c : ℝ) (hc : 0 ≤ c) : ‖(c : ℂ) * (r3 : ℂ) * I‖ = c * r3 := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hc, abs_of_pos r3_pos, mul_one]

/-- The idealised tilt: `|q₀| ≤ |ξ₊| + |ξ₋| = 3√3/4 ≤ 1.3`. -/
lemma uT_P (θ : ℝ) : ‖uT.Q (gk 5 bU) θ 0‖ ≤ 1.3 := by
  obtain ⟨iA, iB, iC, iD⟩ := uF_interp
  have hg : ∀ z : ℂ, ‖z‖ = 1 → gk 5 bU z = (z ^ 5).re := fun z hz => gk_circle _ _ _ hz
  rw [Table.idealTilt_eq (T := uT) uF.nA uF.nB uF.nC uF.nD hg iA iB iC iD θ]
  have hr : ‖rot θ ^ 5‖ = 1 := by rw [norm_pow, norm_rot, one_pow]
  rw [norm_mul, norm_rot, one_mul]
  have e1 : ‖(-1 / 2 : ℂ) * (r3 : ℂ) * I‖ = 1 / 2 * r3 := by
    rw [show (-1 / 2 : ℂ) * (r3 : ℂ) * I = -(((1 / 2 : ℝ) : ℂ) * (r3 : ℂ) * I) by push_cast; ring,
      norm_neg, norm_r3I _ (by norm_num)]
  have e2 : ‖conj ((-1 / 4 : ℂ) * (r3 : ℂ) * I)‖ = 1 / 4 * r3 := by
    rw [Complex.norm_conj, show (-1 / 4 : ℂ) * (r3 : ℂ) * I = -(((1 / 4 : ℝ) : ℂ) * (r3 : ℂ) * I) by
      push_cast; ring, norm_neg, norm_r3I _ (by norm_num)]
  calc _ ≤ ‖(-1 / 2 : ℂ) * (r3 : ℂ) * I * rot θ ^ 5‖ + ‖conj ((-1 / 4 : ℂ) * (r3 : ℂ) * I) * conj (rot θ ^ 5)‖ :=
        norm_add_le _ _
    _ = 1 / 2 * r3 + 1 / 4 * r3 := by
        rw [norm_mul ((-1 / 2 : ℂ) * (r3 : ℂ) * I), norm_mul (conj ((-1 / 4 : ℂ) * (r3 : ℂ) * I)),
          Complex.norm_conj (rot θ ^ 5), hr, e1, e2, mul_one, mul_one]
    _ ≤ 1.3 := by linarith [r3_bounds.2]

lemma uT_P₃ (θ : ℝ) : ‖uT.Q g3u θ 0‖ ≤ 662 := by
  have h := norm_Q_zero_le (T := uT) (g := g3u) (L := 331) (fun x y hx hy => g3u_lip x y hx hy) θ
  nlinarith [uT_K, uT.K_nonneg]

lemma uT_small {ε : ℝ} (hε : 0 ≤ ε) (hε₀ : ε ≤ 5 / 10000) : SmallL uT (ε * 85 + ε ^ 3 * 331) := by
  have hK := uT_K
  have hK0 := uT.K_nonneg
  have hd := uT_dmin
  have hL : ε * 85 + ε ^ 3 * 331 ≤ 0.0426 := by
    have : ε ^ 3 ≤ (5 / 10000) ^ 3 := pow_le_pow_left₀ hε hε₀ 3
    nlinarith
  have hL0 : 0 ≤ ε * 85 + ε ^ 3 * 331 := by positivity
  have hLK : (ε * 85 + ε ^ 3 * 331) * uT.K ≤ 0.0426 * 2 := mul_le_mul hL hK hK0 (by norm_num)
  refine ⟨hL0, by linarith, ?_⟩
  have hr : uT.r = 1 := rfl
  rw [hr]
  have h3 := sqrt3_bound
  have hLK0 : 0 ≤ (ε * 85 + ε ^ 3 * 331) * uT.K := mul_nonneg hL0 hK0
  have hsq : ((ε * 85 + ε ^ 3 * 331) * uT.K) ^ 2 ≤ (0.0426 * 2) ^ 2 := pow_le_pow_left₀ hLK0 hLK 2
  have e1 : 4 / Real.sqrt 3 ≤ 4 / 1.7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
  have e2 : 1 / uT.dmin ≤ 1 / 1.7 := one_div_le_one_div_of_le (by norm_num) hd
  have : 4 / Real.sqrt 3 * (1 / uT.dmin) * ((ε * 85 + ε ^ 3 * 331) * uT.K) ^ 2 ≤
      4 / 1.7 * (1 / 1.7) * (0.0426 * 2) ^ 2 := by
    apply mul_le_mul (mul_le_mul e1 e2 (by positivity) (by norm_num)) hsq (sq_nonneg _) (by norm_num)
  norm_num at this ⊢
  linarith

lemma uT_Rem₀ : Rem uT.K uT.dmin 85 1700 331 1.3 662 (5 / 10000) ≤ 0.1 * (5 / 10000) ^ 3 := by
  refine (Rem_le_of (K' := 2) (d' := 1.7) (t' := 0.00103) uT.K_nonneg (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) uT_K (by norm_num) uT_dmin
    (by norm_num) (by norm_num) (by norm_num)).trans ?_
  norm_num

lemma uT_Rem {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 5 / 10000) :
    Rem uT.K uT.dmin 85 1700 331 1.3 662 ε ≤ 0.1 * ε ^ 3 := by
  have h := Rem_le_scale uT.K_nonneg uT.dmin_pos (L₁ := 85) (M₁ := 1700) (L₃ := 331) (P := 1.3)
    (P₃ := 662) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hε₀
    (by nlinarith [uT_K, uT.K_nonneg])
  have hq : 0 ≤ (ε / (5 / 10000)) ^ 5 := by positivity
  refine h.trans ((mul_le_mul_of_nonneg_left uT_Rem₀ hq).trans ?_)
  have e : (ε / (5 / 10000)) ^ 5 * (0.1 * (5 / 10000) ^ 3) = 0.1 * ε ^ 3 * (ε / (5 / 10000)) ^ 2 := by ring
  rw [e]
  have : (ε / (5 / 10000)) ^ 2 ≤ 1 := by
    apply pow_le_one₀ (by positivity); rw [div_le_one (by norm_num)]; exact hε₀
  have : 0 ≤ 0.1 * ε ^ 3 := by positivity
  nlinarith

/-- **Proposition 5.8** (with `ε₀ = 5·10⁻⁴`): for the table `uT` (diagonals of different lengths)
and a terrain `g` equal to `ε g₁ + ε³ g₃` on the closed unit disc, with
`g₁ = Re(z⁵) - 40(|z|² - 1) Re(e^{iπ/6} z¹⁰)` and `g₃ = Re(a₁₀ z¹⁰ + a₁₅ z¹⁵ + a₂₀ z²⁰)`, and
`(85 ε + 331 ε³)`-Lipschitz on `ℂ`: if `0 < ε ≤ 5·10⁻⁴`, then `w_AC(θ) ≥ 0.3 ε³` for every `θ`. -/
theorem uneq_wob_ge {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 5 / 10000) {g : ℂ → ℝ}
    (hg : IsLip g (ε * 85 + ε ^ 3 * 331))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 5 bU x + ε ^ 3 * g3u x) (θ : ℝ) :
    0.3 * ε ^ 3 ≤ wob uT g (ε * 85 + ε ^ 3 * 331) θ := by
  have hs := uT_small hε.le hε₀
  have hT : ∀ u x : ℂ, ‖u‖ ≤ 1 → ‖x‖ ≤ 1 →
      |gk 5 bU x - gk 5 bU u - dot (Gk 5 bU u) (x - u)| ≤ 1700 / 2 * ‖x - u‖ ^ 2 := by
    intro u x hu hx
    refine taylor_of_lipschitz_grad' (fun u w t _ => hasDerivAt_gk 5 (by norm_num) _ u w t) ?_ u x hu hx
    intro x y hx hy
    have := lipschitz_Gk 3 bU poly_five x y hx hy
    rw [norm_bU] at this
    push_cast at this
    linarith
  have hG : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖Gk 5 bU u‖ ≤ 85 := by
    intro u hu
    have := norm_Gk_le 5 (by norm_num) bU u hu (polyG_five _ (norm_nonneg u) hu)
    rw [norm_bU] at this; push_cast at this; linarith
  have hmain := Table.abs_wob_sub_third_order_le (T := uT) (g₁ := gk 5 bU) (g₃ := g3u)
    (G₁ := Gk 5 bU) (M₁ := 1700) (P := 1.3) (P₃ := 662) (τ := τu) (μ := μu)
    rfl hε.le hg hs hgd hT (by norm_num) hG g3u_lip uT_P uT_P₃ uF.hX uF.τ0.le uF.τ1.le
    uF.μ0.le uF.μ1.le θ
  have hW := Table.W3_ge (T := uT) uF rfl rfl rfl rfl (k := 5) (by norm_num) uF_m5 bU
    a10 a15 a20 (g₁ := gk 5 bU) (G₁ := Gk 5 bU)
    (fun z hz => gk_circle _ _ _ hz) (fun u hu => Gk_circle _ _ _ hu) θ
  rw [uX, uY] at hW
  have hW' := u_W3_bound
  have hR := uT_Rem hε hε₀
  rw [uT_F₀_g₁] at hmain
  have hw3 : 0.45 ≤ Table.w3 uT (Gk 5 bU) τu μu θ (uT.Q (gk 5 bU) θ 0) + F₀ uT g3u τu μu θ :=
    hW'.trans hW
  have hε3 : 0 < ε ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left hw3 hε3.le
  rw [abs_le] at hmain
  nlinarith [hmain.1]

/-- A terrain as in Proposition 5.8 exists (McShane extension from the closed unit disc). -/
theorem uneq_terrain_exists {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ g : ℂ → ℝ, IsLip g (ε * 85 + ε ^ 3 * 331) ∧
      ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 5 bU x + ε ^ 3 * g3u x := by
  set L := ε * 85 + ε ^ 3 * 331
  have hL : 0 ≤ L := by positivity
  have hlip : LipschitzOnWith (Real.toNNReal L) (fun x => ε * gk 5 bU x + ε ^ 3 * g3u x)
      (Metric.closedBall 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hx hy
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
    have h1 := gk5_lip x y hx hy
    have h3 := g3u_lip x y hx hy
    have e : ε * gk 5 bU x + ε ^ 3 * g3u x - (ε * gk 5 bU y + ε ^ 3 * g3u y) =
        ε * (gk 5 bU x - gk 5 bU y) + ε ^ 3 * (g3u x - g3u y) := by ring
    rw [e]
    calc _ ≤ |ε * (gk 5 bU x - gk 5 bU y)| + |ε ^ 3 * (g3u x - g3u y)| := abs_add_le _ _
      _ = ε * |gk 5 bU x - gk 5 bU y| + ε ^ 3 * |g3u x - g3u y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg (pow_nonneg hε 3)]
      _ ≤ ε * (85 * ‖x - y‖) + ε ^ 3 * (331 * ‖x - y‖) := by gcongr
      _ = L * ‖x - y‖ := by ring
  obtain ⟨g, hg, hEq⟩ := hlip.extend_real
  refine ⟨g, fun x y => ?_, fun x hx => (hEq (by rwa [Metric.mem_closedBall, dist_zero_right])).symm⟩
  have := hg.dist_le_mul x y
  rwa [Real.dist_eq, Real.coe_toNNReal _ hL, dist_eq_norm] at this

/-- **Proposition 5.8**, conclusion: the table with diagonals of different lengths wobbles at every
angle. -/
theorem uneq_wobbles {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ 5 / 10000) {g : ℂ → ℝ}
    (hg : IsLip g (ε * 85 + ε ^ 3 * 331))
    (hgd : ∀ x : ℂ, ‖x‖ ≤ 1 → g x = ε * gk 5 bU x + ε ^ 3 * g3u x) (θ : ℝ) :
    ¬ ∃ q c, ‖q‖ < 1 ∧ resid g θ q c uT.A = 0 ∧ resid g θ q c uT.B = 0 ∧
      resid g θ q c uT.C = 0 ∧ resid g θ q c uT.D = 0 := by
  rw [four_feet_iff hg (uT_small hε.le hε₀) θ]
  have := uneq_wob_ge hε hε₀ hg hgd θ
  have : 0 < ε ^ 3 := by positivity
  intro h; linarith

/-- The diagonals of the table have different lengths. -/
lemma uT_diagonals : uT.d₁ < uT.d₂ := by
  obtain ⟨a1, a2, -⟩ := xA_spec; obtain ⟨b1, b2, -⟩ := xB_spec
  obtain ⟨c1, c2, -⟩ := xC_spec; obtain ⟨d1, d2, -⟩ := xD_spec
  obtain ⟨e1, e2⟩ := yA_bounds; obtain ⟨f1, f2⟩ := yB_bounds
  obtain ⟨g1, g2⟩ := yC_bounds; obtain ⟨h1, h2⟩ := yD_bounds
  have e1' : uT.d₁ = Real.sqrt ((xA - xC) ^ 2 + (yA - yC) ^ 2) := by
    show ‖foot' xA - foot' xC‖ = _; rw [uAC, Complex.norm_def, Complex.normSq_mk, sq, sq]
  have e2' : uT.d₂ = Real.sqrt ((xB - xD) ^ 2 + (yB - yD) ^ 2) := by
    show ‖foot' xB - foot' xD‖ = _; rw [uBD, Complex.norm_def, Complex.normSq_mk, sq, sq]
  rw [e1', e2']
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith

end theorem58

end Uneq

end Wobbly
