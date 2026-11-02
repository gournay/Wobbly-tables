import Wobbly.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Degenerate Fourier modes (Lemma 5.3 of the paper)

The feet of the table are unit complex numbers `A, B, C, D` (in cyclic order) and
`X = τ A + (1 - τ) C = μ B + (1 - μ) D` is the intersection of the diagonals. For `k : ℕ`,
`m(k) = -(τ A^k - μ B^k + (1 - τ) C^k - (1 - μ) D^k)`; `m(-k)` is the complex conjugate of `m(k)`.
The mode `k` is *degenerate* if `m(k) = 0`.
-/

open Complex ComplexConjugate

namespace Wobbly

lemma inv_eq_conj_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z⁻¹ = conj z := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]; simp

lemma ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  rintro rfl; simp at hz


lemma exp_sub_exp_neg (z : ℂ) : Complex.exp (z * I) - Complex.exp (-(z * I)) = 2 * I * Complex.sin z := by
  rw [Complex.sin, neg_mul]
  linear_combination (Complex.exp (z * I) - Complex.exp (-(z * I))) * Complex.I_sq

lemma exp_ofReal_mul_I_pow (x : ℝ) (n : ℕ) :
    Complex.exp (x * I) ^ n = Complex.exp (((n * x : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma exp_neg_ofReal_mul_I_pow (x : ℝ) (n : ℕ) :
    Complex.exp (-(x * I)) ^ n = Complex.exp (-(((n * x : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma ofReal_cos_eq (x : ℝ) :
    ((Real.cos x : ℝ) : ℂ) = (Complex.exp (x * I) + (Complex.exp (x * I))⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, neg_mul, Complex.exp_neg]

/-- Four feet on the unit circle with the intersection point of the diagonals. -/
structure Feet where
  A : ℂ
  B : ℂ
  C : ℂ
  D : ℂ
  τ : ℝ
  μ : ℝ
  nA : ‖A‖ = 1
  nB : ‖B‖ = 1
  nC : ‖C‖ = 1
  nD : ‖D‖ = 1
  hX : (τ : ℂ) * A + ((1 - τ : ℝ) : ℂ) * C = (μ : ℂ) * B + ((1 - μ : ℝ) : ℂ) * D
  τ0 : 0 < τ
  τ1 : τ < 1
  μ0 : 0 < μ
  μ1 : μ < 1
  AB : A ≠ B
  AC : A ≠ C
  AD : A ≠ D
  BC : B ≠ C
  BD : B ≠ D
  CD : C ≠ D

namespace Feet

variable (F : Feet)

/-- `m(k) = -Σ_E c_E e_E^k`. -/
def m (k : ℕ) : ℂ :=
  -((F.τ : ℂ) * F.A ^ k - (F.μ : ℂ) * F.B ^ k + ((1 - F.τ : ℝ) : ℂ) * F.C ^ k
    - ((1 - F.μ : ℝ) : ℂ) * F.D ^ k)

/-- `m(-k) = -Σ_E c_E e_E^{-k}`. -/
noncomputable def mbar (k : ℕ) : ℂ :=
  -((F.τ : ℂ) * F.A⁻¹ ^ k - (F.μ : ℂ) * F.B⁻¹ ^ k + ((1 - F.τ : ℝ) : ℂ) * F.C⁻¹ ^ k
    - ((1 - F.μ : ℝ) : ℂ) * F.D⁻¹ ^ k)

lemma A_ne : F.A ≠ 0 := ne_zero_of_norm_eq_one F.nA
lemma B_ne : F.B ≠ 0 := ne_zero_of_norm_eq_one F.nB
lemma C_ne : F.C ≠ 0 := ne_zero_of_norm_eq_one F.nC
lemma D_ne : F.D ≠ 0 := ne_zero_of_norm_eq_one F.nD

lemma mbar_eq_conj (k : ℕ) : F.mbar k = conj (F.m k) := by
  simp only [mbar, m, map_neg, map_sub, map_add, map_mul, map_pow, Complex.conj_ofReal,
    inv_eq_conj_of_norm_eq_one F.nA, inv_eq_conj_of_norm_eq_one F.nB,
    inv_eq_conj_of_norm_eq_one F.nC, inv_eq_conj_of_norm_eq_one F.nD]

/-- Lemma 5.3 (a): `m(0) = 0`. -/
lemma m_zero : F.m 0 = 0 := by
  simp only [m, pow_zero]; push_cast; ring

/-- Lemma 5.3 (a): `m(1) = 0` (the diagonals meet at `X`). -/
lemma m_one : F.m 1 = 0 := by
  have := F.hX
  simp only [m, pow_one]
  linear_combination -this

lemma mbar_one : F.mbar 1 = 0 := by rw [mbar_eq_conj, m_one, map_zero]

lemma mbar_zero : F.mbar 0 = 0 := by rw [mbar_eq_conj, m_zero, map_zero]

/-- Lemma 5.3 (b): for a rectangle, the odd modes are degenerate. -/
lemma m_odd_of_rectangle (hC : F.C = -F.A) (hD : F.D = -F.B) (hτ : F.τ = 1 / 2)
    (hμ : F.μ = 1 / 2) {k : ℕ} (hk : Odd k) : F.m k = 0 := by
  simp only [m, hC, hD, hτ, hμ, hk.neg_pow]
  push_cast; ring

/-- Lemma 5.3 (d): for a rational table (feet at `n`-th roots of unity), `m(k)` only depends on
`k mod n`. -/
lemma m_add_of_rational {n : ℕ} (hA : F.A ^ n = 1) (hB : F.B ^ n = 1) (hC : F.C ^ n = 1)
    (hD : F.D ^ n = 1) (k : ℕ) : F.m (k + n) = F.m k := by
  simp only [m, pow_add, hA, hB, hC, hD, mul_one]

/-- Lemma 5.3 (d): for a rational table, `K_n = {k ≡ 0, ±1 mod n}` is made of degenerate modes. -/
lemma m_eq_zero_of_rational {n : ℕ} (hn : 1 ≤ n) (hA : F.A ^ n = 1) (hB : F.B ^ n = 1)
    (hC : F.C ^ n = 1) (hD : F.D ^ n = 1) (j : ℕ) :
    F.m (n * j) = 0 ∧ F.m (n * j + 1) = 0 ∧ F.m (n * j + (n - 1)) = 0 := by
  have hj : ∀ k i, F.m (n * i + k) = F.m k := by
    intro k i
    induction i with
    | zero => simp
    | succ i ih => rw [show n * (i + 1) + k = (n * i + k) + n by ring, m_add_of_rational F hA hB hC hD, ih]
  refine ⟨by simpa using (hj 0 j).trans F.m_zero, (hj 1 j).trans F.m_one, ?_⟩
  rw [hj]
  -- `m(n - 1) = m(-1) = conj m(1) = 0`
  have hinv : ∀ z : ℂ, z ^ n = 1 → z ^ (n - 1) = z⁻¹ := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; simp [zero_pow (by omega : n ≠ 0)] at hz
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hn, hz])
  have : F.m (n - 1) = F.mbar 1 := by
    simp only [m, mbar, pow_one, hinv _ hA, hinv _ hB, hinv _ hC, hinv _ hD]
  rw [this, mbar_one]

/-! ### Lemma 5.3 (e) -/

/-- The weighted sum `Σ_E c_E φ(e_E)`, with `(c_A, c_B, c_C, c_D) = (τ, -μ, 1 - τ, -(1 - μ))`. -/
def S (φ : ℂ → ℂ) : ℂ :=
  (F.τ : ℂ) * φ F.A - (F.μ : ℂ) * φ F.B + ((1 - F.τ : ℝ) : ℂ) * φ F.C
    - ((1 - F.μ : ℝ) : ℂ) * φ F.D

lemma m_eq_S (k : ℕ) : F.m k = -F.S (fun z => z ^ k) := rfl

lemma mbar_eq_S (k : ℕ) : F.mbar k = -F.S (fun z => z⁻¹ ^ k) := rfl

lemma S_congr {φ ψ : ℂ → ℂ} (hA : φ F.A = ψ F.A) (hB : φ F.B = ψ F.B) (hC : φ F.C = ψ F.C)
    (hD : φ F.D = ψ F.D) : F.S φ = F.S ψ := by
  simp only [S, hA, hB, hC, hD]

lemma S_lin3 (a b c : ℂ) (φ ψ χ : ℂ → ℂ) :
    F.S (fun z => a * φ z + b * ψ z + c * χ z) = a * F.S φ + b * F.S ψ + c * F.S χ := by
  simp only [S]; ring

lemma S_const (c : ℂ) : F.S (fun _ => c) = 0 := by
  simp only [S]; push_cast; ring

lemma S_pow (k : ℕ) : F.S (fun z => z ^ k) = -F.m k := by rw [m_eq_S, neg_neg]

lemma S_inv_pow (k : ℕ) : F.S (fun z => z⁻¹ ^ k) = -F.mbar k := by rw [mbar_eq_S, neg_neg]

/-- Lemma 5.3 (e): `m(2) ≠ 0`. -/
theorem m_two_ne_zero : F.m 2 ≠ 0 := by
  intro h2
  have h2' : F.mbar 2 = 0 := by rw [mbar_eq_conj, h2, map_zero]
  -- `p(z) = |z - B|² |z - D|²` on the unit circle, a trigonometric polynomial of degree 2
  let p : ℂ → ℂ := fun z => (z - F.B) * (z⁻¹ - F.B⁻¹) * ((z - F.D) * (z⁻¹ - F.D⁻¹))
  have hB0 := F.B_ne
  have hD0 := F.D_ne
  have hp : ∀ z : ℂ, z ≠ 0 → p z = (4 + F.D / F.B + F.B / F.D) * 1 + (-2 * (1 / F.B + 1 / F.D)) * z ^ 1
      + (-2 * (F.B + F.D)) * z⁻¹ ^ 1 + (1 / (F.B * F.D)) * z ^ 2 + (F.B * F.D) * z⁻¹ ^ 2 := by
    intro z hz
    simp only [p]
    field_simp
    ring
  have hsum : F.S p = 0 := by
    have e : F.S p = F.S (fun z => (4 + F.D / F.B + F.B / F.D) * 1 + (-2 * (1 / F.B + 1 / F.D)) * z ^ 1
      + (-2 * (F.B + F.D)) * z⁻¹ ^ 1 + (1 / (F.B * F.D)) * z ^ 2 + (F.B * F.D) * z⁻¹ ^ 2) :=
      F.S_congr (hp _ F.A_ne) (hp _ F.B_ne) (hp _ F.C_ne) (hp _ F.D_ne)
    rw [e]
    have := F.S_const 1
    simp only [S] at this ⊢
    have h1 := F.S_pow 1
    have h1' := F.S_inv_pow 1
    have h2s := F.S_pow 2
    have h2s' := F.S_inv_pow 2
    simp only [S] at h1 h1' h2s h2s'
    rw [F.m_one] at h1
    rw [F.mbar_one] at h1'
    rw [h2] at h2s
    rw [h2'] at h2s'
    linear_combination (4 + F.D / F.B + F.B / F.D) * this + (-2 * (1 / F.B + 1 / F.D)) * h1 +
      (-2 * (F.B + F.D)) * h1' + (1 / (F.B * F.D)) * h2s + (F.B * F.D) * h2s'
  have hpB : p F.B = 0 := by simp [p]
  have hpD : p F.D = 0 := by simp [p]
  have hnorm : ∀ z w : ℂ, ‖z‖ = 1 → ‖w‖ = 1 → (z - w) * (z⁻¹ - w⁻¹) = ((‖z - w‖ ^ 2 : ℝ) : ℂ) := by
    intro z w hz hw
    rw [inv_eq_conj_of_norm_eq_one hz, inv_eq_conj_of_norm_eq_one hw, ← map_sub,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpA : p F.A = ((‖F.A - F.B‖ ^ 2 * ‖F.A - F.D‖ ^ 2 : ℝ) : ℂ) := by
    simp only [p]; rw [hnorm _ _ F.nA F.nB, hnorm _ _ F.nA F.nD]; push_cast; ring
  have hpC : p F.C = ((‖F.C - F.B‖ ^ 2 * ‖F.C - F.D‖ ^ 2 : ℝ) : ℂ) := by
    simp only [p]; rw [hnorm _ _ F.nC F.nB, hnorm _ _ F.nC F.nD]; push_cast; ring
  simp only [S] at hsum
  rw [hpB, hpD, hpA, hpC] at hsum
  set X := ‖F.A - F.B‖ ^ 2 * ‖F.A - F.D‖ ^ 2
  set Y := ‖F.C - F.B‖ ^ 2 * ‖F.C - F.D‖ ^ 2
  have h' : ((F.τ * X + (1 - F.τ) * Y : ℝ) : ℂ) = 0 := by
    push_cast at hsum ⊢; linear_combination hsum
  have h'' : F.τ * X + (1 - F.τ) * Y = 0 := by exact_mod_cast h'
  have a1 : 0 < ‖F.A - F.B‖ := norm_pos_iff.2 (sub_ne_zero.2 F.AB)
  have a2 : 0 < ‖F.A - F.D‖ := norm_pos_iff.2 (sub_ne_zero.2 F.AD)
  have a3 : 0 < ‖F.C - F.B‖ := norm_pos_iff.2 (sub_ne_zero.2 F.BC.symm)
  have a4 : 0 < ‖F.C - F.D‖ := norm_pos_iff.2 (sub_ne_zero.2 F.CD)
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  nlinarith [mul_pos F.τ0 hX, mul_pos (sub_pos.2 F.τ1) hY]

/-- The identity of Lemma 5.3 (e), for three coefficients. -/
def Interp (k : ℕ) (a₀ a₁ a₂ : ℂ) : Prop :=
  F.A ^ k = a₀ + a₁ * F.A + a₂ * conj F.A ∧ F.B ^ k = a₀ + a₁ * F.B + a₂ * conj F.B ∧
    F.C ^ k = a₀ + a₁ * F.C + a₂ * conj F.C ∧ F.D ^ k = a₀ + a₁ * F.D + a₂ * conj F.D

/-- Lemma 5.3 (e): `k` is a degenerate mode iff `e_E^k = α₀ + α₁ e_E + α₂ ē_E` for the four feet. -/
theorem m_eq_zero_iff (k : ℕ) : F.m k = 0 ↔ ∃ a₀ a₁ a₂ : ℂ, F.Interp k a₀ a₁ a₂ := by
  have cA := inv_eq_conj_of_norm_eq_one F.nA
  have cB := inv_eq_conj_of_norm_eq_one F.nB
  have cC := inv_eq_conj_of_norm_eq_one F.nC
  have cD := inv_eq_conj_of_norm_eq_one F.nD
  constructor
  · intro hk
    have hA0 := F.A_ne
    have hB0 := F.B_ne
    have hC0 := F.C_ne
    have hAB := sub_ne_zero.2 F.AB
    have hAC := sub_ne_zero.2 F.AC
    have hBC := sub_ne_zero.2 F.BC
    set A := F.A
    set B := F.B
    set C := F.C
    -- Lagrange interpolation of `z^(k+1)` at `A, B, C` by `a₁ z² + a₀ z + a₂`
    set a₁ := A ^ (k + 1) / ((A - B) * (A - C)) + B ^ (k + 1) / ((B - A) * (B - C)) +
      C ^ (k + 1) / ((C - A) * (C - B))
    set a₀ := -(A ^ (k + 1) * (B + C) / ((A - B) * (A - C)) + B ^ (k + 1) * (A + C) / ((B - A) * (B - C))
      + C ^ (k + 1) * (A + B) / ((C - A) * (C - B)))
    set a₂ := A ^ (k + 1) * (B * C) / ((A - B) * (A - C)) + B ^ (k + 1) * (A * C) / ((B - A) * (B - C))
      + C ^ (k + 1) * (A * B) / ((C - A) * (C - B))
    have hBA : B - A ≠ 0 := sub_ne_zero.2 F.AB.symm
    have hCA : C - A ≠ 0 := sub_ne_zero.2 F.AC.symm
    have hCB : C - B ≠ 0 := sub_ne_zero.2 F.BC.symm
    have iA : A ^ k = a₀ + a₁ * A + a₂ * A⁻¹ := by
      simp only [a₀, a₁, a₂]; field_simp; ring
    have iB : B ^ k = a₀ + a₁ * B + a₂ * B⁻¹ := by
      simp only [a₀, a₁, a₂]; field_simp; ring
    have iC : C ^ k = a₀ + a₁ * C + a₂ * C⁻¹ := by
      simp only [a₀, a₁, a₂]; field_simp; ring
    refine ⟨a₀, a₁, a₂, by rw [← cA]; exact iA, by rw [← cB]; exact iB, by rw [← cC]; exact iC, ?_⟩
    rw [← cD]
    -- the fourth foot: `Σ c_E (e_E^k - Q(e_E)) = 0`
    have hsum : F.S (fun z => z ^ k) =
        F.S (fun z => a₀ * z ^ 0 + a₁ * z ^ 1 + a₂ * z⁻¹ ^ 1) := by
      rw [F.S_lin3, F.S_pow, F.S_pow, F.S_inv_pow, F.S_pow, hk, F.m_zero, F.m_one, F.mbar_one]
      ring
    simp only [S, pow_zero, pow_one, mul_one] at hsum
    rw [iA, iB, iC] at hsum
    have hμ : ((1 - F.μ : ℝ) : ℂ) ≠ 0 := by
      have := F.μ1; exact_mod_cast (by linarith : (1 - F.μ) ≠ 0)
    have : ((1 - F.μ : ℝ) : ℂ) * (F.D ^ k - (a₀ + a₁ * F.D + a₂ * F.D⁻¹)) = 0 := by
      linear_combination -hsum
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hμ)
  · rintro ⟨a₀, a₁, a₂, hA, hB, hC, hD⟩
    have h : F.S (fun z => z ^ k) = F.S (fun z => a₀ * z ^ 0 + a₁ * z ^ 1 + a₂ * z⁻¹ ^ 1) :=
      F.S_congr (by simp [hA, cA]) (by simp [hB, cB]) (by simp [hC, cC]) (by simp [hD, cD])
    rw [F.S_lin3, F.S_pow, F.S_pow, F.S_pow, F.S_inv_pow, F.m_zero, F.m_one, F.mbar_one] at h
    simpa using h

/-- Lemma 5.3 (e): the coefficients `α₁`, `α₂` and the identity `Re(m(2) m(k-1) conj m(k+1)) = 0`. -/
theorem interp_coeffs {k : ℕ} (hk1 : 1 ≤ k) (hk : F.m k = 0) {a₀ a₁ a₂ : ℂ}
    (h : F.Interp k a₀ a₁ a₂) :
    F.m (k + 1) = a₁ * F.m 2 ∧ F.m (k - 1) = a₂ * conj (F.m 2) ∧
      (F.m 2 * F.m (k - 1) * conj (F.m (k + 1))).re = 0 := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  have cA := inv_eq_conj_of_norm_eq_one F.nA
  have cB := inv_eq_conj_of_norm_eq_one F.nB
  have cC := inv_eq_conj_of_norm_eq_one F.nC
  have cD := inv_eq_conj_of_norm_eq_one F.nD
  rw [← cA] at hA
  rw [← cB] at hB
  rw [← cC] at hC
  rw [← cD] at hD
  have hA0 := F.A_ne
  have hB0 := F.B_ne
  have hC0 := F.C_ne
  have hD0 := F.D_ne
  -- multiply the identity by `e`, by `e⁻¹` and by `e^{-k}`
  have up : ∀ z : ℂ, z ≠ 0 → z ^ k = a₀ + a₁ * z + a₂ * z⁻¹ →
      z ^ (k + 1) = a₀ * z ^ 1 + a₁ * z ^ 2 + a₂ * z ^ 0 := by
    intro z hz e; rw [pow_succ, e]; field_simp
  have down : ∀ z : ℂ, z ≠ 0 → z ^ k = a₀ + a₁ * z + a₂ * z⁻¹ →
      z ^ (k - 1) = a₀ * z⁻¹ ^ 1 + a₁ * z ^ 0 + a₂ * z⁻¹ ^ 2 := by
    intro z hz e
    have : z ^ (k - 1) = z ^ k * z⁻¹ := by
      rw [← Nat.sub_add_cancel hk1, pow_succ, Nat.add_sub_cancel, mul_assoc, mul_inv_cancel₀ hz,
        mul_one]
    rw [this, e]; field_simp
  have inv : ∀ z : ℂ, z ≠ 0 → z ^ k = a₀ + a₁ * z + a₂ * z⁻¹ →
      (1 : ℂ) = a₀ * z⁻¹ ^ k + a₁ * z⁻¹ ^ (k - 1) + a₂ * z⁻¹ ^ (k + 1) := by
    intro z hz e
    have e1 : z⁻¹ ^ (k - 1) = z⁻¹ ^ k * z := by
      rw [← Nat.sub_add_cancel hk1, pow_succ, Nat.add_sub_cancel, mul_assoc, inv_mul_cancel₀ hz,
        mul_one]
    have hzk : z ^ k ≠ 0 := pow_ne_zero _ hz
    have h1 : (1 : ℂ) = z⁻¹ ^ k * z ^ k := by rw [inv_pow, inv_mul_cancel₀ hzk]
    rw [h1, e, e1, pow_succ]
    ring
  have h1 : F.S (fun z => z ^ (k + 1)) = F.S (fun z => a₀ * z ^ 1 + a₁ * z ^ 2 + a₂ * z ^ 0) :=
    F.S_congr (up _ hA0 hA) (up _ hB0 hB) (up _ hC0 hC) (up _ hD0 hD)
  have h2 : F.S (fun z => z ^ (k - 1)) = F.S (fun z => a₀ * z⁻¹ ^ 1 + a₁ * z ^ 0 + a₂ * z⁻¹ ^ 2) :=
    F.S_congr (down _ hA0 hA) (down _ hB0 hB) (down _ hC0 hC) (down _ hD0 hD)
  have h3 : F.S (fun _ => (1 : ℂ)) =
      F.S (fun z => a₀ * z⁻¹ ^ k + a₁ * z⁻¹ ^ (k - 1) + a₂ * z⁻¹ ^ (k + 1)) :=
    F.S_congr (inv _ hA0 hA) (inv _ hB0 hB) (inv _ hC0 hC) (inv _ hD0 hD)
  rw [F.S_lin3, F.S_pow, F.S_pow, F.S_pow, F.S_pow, F.m_one, F.m_zero] at h1
  rw [F.S_lin3, F.S_pow, F.S_pow, F.S_inv_pow, F.S_inv_pow, F.m_zero, F.mbar_one,
    F.mbar_eq_conj 2] at h2
  rw [F.S_lin3, F.S_const, F.S_inv_pow, F.S_inv_pow, F.S_inv_pow, F.mbar_eq_conj,
    F.mbar_eq_conj, F.mbar_eq_conj, hk, map_zero] at h3
  have e1 : F.m (k + 1) = a₁ * F.m 2 := by linear_combination -h1
  have e2 : F.m (k - 1) = a₂ * conj (F.m 2) := by linear_combination -h2
  refine ⟨e1, e2, ?_⟩
  -- `a₁ conj m(k-1) + a₂ conj m(k+1) = 0`
  have e3 : a₁ * conj (F.m (k - 1)) + a₂ * conj (F.m (k + 1)) = 0 := by linear_combination h3
  have hm2 := F.m_two_ne_zero
  have hm2c : conj (F.m 2) ≠ 0 := (map_ne_zero _).2 hm2
  set M := F.m 2
  have ha₁ : a₁ = F.m (k + 1) / M := by rw [e1]; field_simp
  have ha₂ : a₂ = F.m (k - 1) / conj M := by rw [e2]; field_simp
  rw [ha₁, ha₂] at e3
  have e4 : M * F.m (k - 1) * conj (F.m (k + 1)) + conj (M * F.m (k - 1) * conj (F.m (k + 1))) = 0 := by
    simp only [map_mul, Complex.conj_conj]
    field_simp at e3
    linear_combination e3
  have := congrArg Complex.re e4
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
  linarith

/-! ### Lemma 5.3 (f): the modes `3`, `4`, `5` -/

/-- Elementary symmetric functions of the feet. -/
def s₁ : ℂ := F.A + F.B + F.C + F.D
def s₂ : ℂ := F.A * F.B + F.A * F.C + F.A * F.D + F.B * F.C + F.B * F.D + F.C * F.D
def s₃ : ℂ := F.A * F.B * F.C + F.A * F.B * F.D + F.A * F.C * F.D + F.B * F.C * F.D
def s₄ : ℂ := F.A * F.B * F.C * F.D

/-- If a cubic polynomial vanishes at the four (distinct) feet, its leading coefficient is `0`. -/
lemma lead_eq_zero {a b c d : ℂ} (hA : a * F.A ^ 3 + b * F.A ^ 2 + c * F.A + d = 0)
    (hB : a * F.B ^ 3 + b * F.B ^ 2 + c * F.B + d = 0) (hC : a * F.C ^ 3 + b * F.C ^ 2 + c * F.C + d = 0)
    (hD : a * F.D ^ 3 + b * F.D ^ 2 + c * F.D + d = 0) : a = 0 := by
  have h1 := sub_ne_zero.2 F.AB
  have h2 := sub_ne_zero.2 F.AC
  have h3 := sub_ne_zero.2 F.AD
  have h4 := sub_ne_zero.2 F.BC
  have h5 := sub_ne_zero.2 F.BD
  have h6 := sub_ne_zero.2 F.CD
  have key : a = (a * F.A ^ 3 + b * F.A ^ 2 + c * F.A + d) / ((F.A - F.B) * (F.A - F.C) * (F.A - F.D))
      + (a * F.B ^ 3 + b * F.B ^ 2 + c * F.B + d) / ((F.B - F.A) * (F.B - F.C) * (F.B - F.D))
      + (a * F.C ^ 3 + b * F.C ^ 2 + c * F.C + d) / ((F.C - F.A) * (F.C - F.B) * (F.C - F.D))
      + (a * F.D ^ 3 + b * F.D ^ 2 + c * F.D + d) / ((F.D - F.A) * (F.D - F.B) * (F.D - F.C)) := by
    have h1' := sub_ne_zero.2 F.AB.symm
    have h2' := sub_ne_zero.2 F.AC.symm
    have h3' := sub_ne_zero.2 F.AD.symm
    have h4' := sub_ne_zero.2 F.BC.symm
    have h5' := sub_ne_zero.2 F.BD.symm
    have h6' := sub_ne_zero.2 F.CD.symm
    field_simp
    ring
  rw [key, hA, hB, hC, hD]; simp

/-- If `e^(k+1) = a e³ + b e² + c e + d` at the four feet, then `k` is degenerate iff `a = 0`. -/
lemma m_eq_zero_iff_of_red {k : ℕ} {a b c d : ℂ}
    (hA : F.A ^ (k + 1) = a * F.A ^ 3 + b * F.A ^ 2 + c * F.A + d)
    (hB : F.B ^ (k + 1) = a * F.B ^ 3 + b * F.B ^ 2 + c * F.B + d)
    (hC : F.C ^ (k + 1) = a * F.C ^ 3 + b * F.C ^ 2 + c * F.C + d)
    (hD : F.D ^ (k + 1) = a * F.D ^ 3 + b * F.D ^ 2 + c * F.D + d) : F.m k = 0 ↔ a = 0 := by
  rw [m_eq_zero_iff]
  have cA := inv_eq_conj_of_norm_eq_one F.nA
  have cB := inv_eq_conj_of_norm_eq_one F.nB
  have cC := inv_eq_conj_of_norm_eq_one F.nC
  have cD := inv_eq_conj_of_norm_eq_one F.nD
  have down : ∀ z : ℂ, z ≠ 0 → z ^ (k + 1) = b * z ^ 2 + c * z + d → z ^ k = c + b * z + d * z⁻¹ := by
    intro z hz e
    have : z ^ k = z ^ (k + 1) * z⁻¹ := by rw [pow_succ, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    rw [this, e]; field_simp; ring
  constructor
  · rintro ⟨a₀, a₁, a₂, iA, iB, iC, iD⟩
    have up : ∀ z : ℂ, z ≠ 0 → z ^ k = a₀ + a₁ * z + a₂ * z⁻¹ →
        z ^ (k + 1) = a₁ * z ^ 2 + a₀ * z + a₂ := by
      intro z hz e; rw [pow_succ, e]; field_simp; ring
    rw [← cA] at iA
    rw [← cB] at iB
    rw [← cC] at iC
    rw [← cD] at iD
    have uA := up _ F.A_ne iA
    have uB := up _ F.B_ne iB
    have uC := up _ F.C_ne iC
    have uD := up _ F.D_ne iD
    exact F.lead_eq_zero (b := b - a₁) (c := c - a₀) (d := d - a₂)
      (by linear_combination hA.symm.trans uA) (by linear_combination hB.symm.trans uB)
      (by linear_combination hC.symm.trans uC) (by linear_combination hD.symm.trans uD)
  · intro ha
    subst ha
    refine ⟨c, b, d, ?_, ?_, ?_, ?_⟩
    · rw [← cA]; exact down _ F.A_ne (by rw [hA]; ring)
    · rw [← cB]; exact down _ F.B_ne (by rw [hB]; ring)
    · rw [← cC]; exact down _ F.C_ne (by rw [hC]; ring)
    · rw [← cD]; exact down _ F.D_ne (by rw [hD]; ring)

/-- Lemma 5.3 (f): `3 ∈ K ↔ s₁ = 0`. -/
theorem m_three_iff : F.m 3 = 0 ↔ F.s₁ = 0 :=
  F.m_eq_zero_iff_of_red (b := -F.s₂) (c := F.s₃) (d := -F.s₄)
    (by simp only [s₁, s₂, s₃, s₄]; ring) (by simp only [s₁, s₂, s₃, s₄]; ring)
    (by simp only [s₁, s₂, s₃, s₄]; ring) (by simp only [s₁, s₂, s₃, s₄]; ring)

/-- Lemma 5.3 (f): `4 ∈ K ↔ s₂ = s₁²`. -/
theorem m_four_iff : F.m 4 = 0 ↔ F.s₂ = F.s₁ ^ 2 := by
  rw [F.m_eq_zero_iff_of_red (a := F.s₁ ^ 2 - F.s₂) (b := F.s₃ - F.s₁ * F.s₂)
    (c := F.s₁ * F.s₃ - F.s₄) (d := -F.s₁ * F.s₄)
    (by simp only [s₁, s₂, s₃, s₄]; ring) (by simp only [s₁, s₂, s₃, s₄]; ring)
    (by simp only [s₁, s₂, s₃, s₄]; ring) (by simp only [s₁, s₂, s₃, s₄]; ring)]
  constructor <;> intro h <;> linear_combination -h

/-- Lemma 5.3 (f): `5 ∈ K ↔ s₃ = 2 s₁ s₂ - s₁³`. -/
theorem m_five_iff : F.m 5 = 0 ↔ F.s₃ = 2 * F.s₁ * F.s₂ - F.s₁ ^ 3 := by
  rw [F.m_eq_zero_iff_of_red (a := F.s₁ ^ 3 - 2 * F.s₁ * F.s₂ + F.s₃)
    (b := -F.s₁ ^ 2 * F.s₂ + F.s₁ * F.s₃ + F.s₂ ^ 2 - F.s₄)
    (c := F.s₁ ^ 2 * F.s₃ - F.s₁ * F.s₄ - F.s₂ * F.s₃) (d := -F.s₁ ^ 2 * F.s₄ + F.s₂ * F.s₄)
    (by simp only [s₁, s₂, s₃, s₄]; ring) (by simp only [s₁, s₂, s₃, s₄]; ring)
    (by simp only [s₁, s₂, s₃, s₄]; ring) (by simp only [s₁, s₂, s₃, s₄]; ring)]
  constructor <;> intro h <;> linear_combination h

/-- The feet are on the unit circle: `conj s₁ · s₄ = s₃` and `conj s₂ · s₄ = s₂`. -/
lemma conj_s₁ : conj F.s₁ * F.s₄ = F.s₃ := by
  simp only [s₁, s₃, s₄, map_add, ← inv_eq_conj_of_norm_eq_one F.nA, ← inv_eq_conj_of_norm_eq_one F.nB,
    ← inv_eq_conj_of_norm_eq_one F.nC, ← inv_eq_conj_of_norm_eq_one F.nD]
  have := F.A_ne; have := F.B_ne; have := F.C_ne; have := F.D_ne
  field_simp; ring

lemma conj_s₂ : conj F.s₂ * F.s₄ = F.s₂ := by
  simp only [s₂, s₄, map_add, map_mul, ← inv_eq_conj_of_norm_eq_one F.nA,
    ← inv_eq_conj_of_norm_eq_one F.nB, ← inv_eq_conj_of_norm_eq_one F.nC,
    ← inv_eq_conj_of_norm_eq_one F.nD]
  have := F.A_ne; have := F.B_ne; have := F.C_ne; have := F.D_ne
  field_simp; ring

lemma prod_eq : (F.A * F.B - F.C * F.D) * (F.A * F.C - F.B * F.D) * (F.A * F.D - F.B * F.C) =
    F.s₁ ^ 2 * F.s₄ - F.s₃ ^ 2 := by
  simp only [s₁, s₃, s₄]; ring

/-- Non-parallel diagonals. -/
def NonParallel : Prop := ((F.A - F.C) * conj (F.B - F.D)).im ≠ 0

lemma AC_ne_BD (h : F.NonParallel) : F.A * F.C - F.B * F.D ≠ 0 := by
  intro hAC
  apply h
  have hB0 := F.B_ne
  have hD0 := F.D_ne
  have hA0 := F.A_ne
  have hC0 := F.C_ne
  -- `z = (A - C) conj(B - D)` is real
  have cA : conj F.A = F.A⁻¹ := (inv_eq_conj_of_norm_eq_one F.nA).symm
  have cB : conj F.B = F.B⁻¹ := (inv_eq_conj_of_norm_eq_one F.nB).symm
  have cC : conj F.C = F.C⁻¹ := (inv_eq_conj_of_norm_eq_one F.nC).symm
  have cD : conj F.D = F.D⁻¹ := (inv_eq_conj_of_norm_eq_one F.nD).symm
  have key : (F.A⁻¹ - F.C⁻¹) * (F.B - F.D) - (F.A - F.C) * (F.B⁻¹ - F.D⁻¹) =
      (F.C - F.A) * (F.B - F.D) * (F.B * F.D - F.A * F.C) / (F.A * F.B * F.C * F.D) := by
    field_simp; ring
  have hBD : F.B * F.D - F.A * F.C = 0 := by linear_combination -hAC
  rw [hBD, mul_zero, zero_div] at key
  have e : conj ((F.A - F.C) * conj (F.B - F.D)) = (F.A - F.C) * conj (F.B - F.D) := by
    rw [map_mul, Complex.conj_conj, map_sub, map_sub, cA, cC, cB, cD]
    linear_combination key
  have := congrArg Complex.im e
  simp only [Complex.conj_im] at this
  linarith

/-- The diagonals have the same length as soon as `(AB - CD)(AD - BC) = 0`. -/
lemma diag_eq_of (h : (F.A * F.B - F.C * F.D) * (F.A * F.D - F.B * F.C) = 0) :
    ‖F.A - F.C‖ = ‖F.B - F.D‖ := by
  have hsq : ∀ z w : ℂ, ‖z‖ = 1 → ‖w‖ = 1 → ((‖z - w‖ ^ 2 : ℝ) : ℂ) = 2 - z / w - w / z := by
    intro z w hz hw
    have hz0 := ne_zero_of_norm_eq_one hz
    have hw0 := ne_zero_of_norm_eq_one hw
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sub, ← inv_eq_conj_of_norm_eq_one hz,
      ← inv_eq_conj_of_norm_eq_one hw]
    field_simp; ring
  have e : ((‖F.A - F.C‖ ^ 2 : ℝ) : ℂ) = ((‖F.B - F.D‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsq _ _ F.nA F.nC, hsq _ _ F.nB F.nD]
    have := F.A_ne; have := F.B_ne; have := F.C_ne; have := F.D_ne
    field_simp
    linear_combination -h
  have e' : ‖F.A - F.C‖ ^ 2 = ‖F.B - F.D‖ ^ 2 := by exact_mod_cast e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e'

lemma prod_ne_of_diag_ne (h : F.NonParallel) (hd : ‖F.A - F.C‖ ≠ ‖F.B - F.D‖) :
    F.s₁ ^ 2 * F.s₄ - F.s₃ ^ 2 ≠ 0 := by
  rw [← prod_eq]
  have h1 : (F.A * F.B - F.C * F.D) * (F.A * F.D - F.B * F.C) ≠ 0 := fun h0 => hd (F.diag_eq_of h0)
  have h2 := F.AC_ne_BD h
  intro h0
  apply h1
  have : (F.A * F.B - F.C * F.D) * (F.A * F.D - F.B * F.C) * (F.A * F.C - F.B * F.D) = 0 := by
    linear_combination h0
  exact (mul_eq_zero.1 this).resolve_right h2

/-- Lemma 5.3 (f): if `3` or `4` is a degenerate mode, then the diagonals have the same length. -/
theorem diag_eq_of_m_three_or_four (h : F.NonParallel) (hk : F.m 3 = 0 ∨ F.m 4 = 0) :
    ‖F.A - F.C‖ = ‖F.B - F.D‖ := by
  by_contra hd
  apply F.prod_ne_of_diag_ne h hd
  have c1 := F.conj_s₁
  have c2 := F.conj_s₂
  rcases hk with h3 | h4
  · rw [m_three_iff] at h3
    rw [← c1, h3]; simp
  · rw [m_four_iff] at h4
    rw [← c1]
    have : F.s₁ ^ 2 = conj F.s₁ ^ 2 * F.s₄ := by rw [← h4, ← c2, h4, map_pow]
    linear_combination F.s₄ * this

/-- Lemma 5.3 (f): `3 ∈ K` iff the table is a rectangle (`C = -A`, `D = -B`). -/
theorem m_three_iff_rectangle (h : F.NonParallel) : F.m 3 = 0 ↔ F.C = -F.A ∧ F.D = -F.B := by
  rw [m_three_iff]
  constructor
  · intro h1
    have h3 : F.s₃ = 0 := by rw [← F.conj_s₁, h1]; simp
    have hA0 := F.A_ne
    -- `-A` is also a root of `z⁴ + s₂ z² + s₄`
    have hQ : (-F.A - F.A) * (-F.A - F.B) * (-F.A - F.C) * (-F.A - F.D) = 0 := by
      have e1 : (-F.A - F.A) * (-F.A - F.B) * (-F.A - F.C) * (-F.A - F.D) =
          F.A ^ 4 + F.s₂ * F.A ^ 2 + F.s₄ + F.s₁ * F.A ^ 3 + F.s₃ * F.A := by
        simp only [s₁, s₂, s₃, s₄]; ring
      have e2 : F.A ^ 4 + F.s₂ * F.A ^ 2 + F.s₄ - F.s₁ * F.A ^ 3 - F.s₃ * F.A = 0 := by
        simp only [s₁, s₂, s₃, s₄]; ring
      rw [e1]; linear_combination e2 + 2 * F.A ^ 3 * h1 + 2 * F.A * h3
    have h2A : -F.A - F.A ≠ 0 := by
      intro h0; apply hA0; linear_combination -h0 / 2
    rcases mul_eq_zero.1 hQ with hQ | hD
    · rcases mul_eq_zero.1 hQ with hQ | hC
      · rcases mul_eq_zero.1 hQ with hQ | hB
        · exact absurd hQ h2A
        · -- `B = -A`, then `D = -C` and the diagonals are parallel
          exfalso
          have hB' : F.B = -F.A := by linear_combination -hB
          have hD' : F.D = -F.C := by
            have := h1; simp only [s₁] at this; linear_combination this - hB'
          apply h
          rw [hB', hD']
          have : (F.A - F.C) * conj (-F.A - -F.C) = -((‖F.A - F.C‖ ^ 2 : ℝ) : ℂ) := by
            rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; simp [map_sub]; ring
          rw [this, Complex.neg_im, Complex.ofReal_im, neg_zero]
      · refine ⟨by linear_combination -hC, ?_⟩
        have := h1; simp only [s₁] at this; linear_combination this + hC
    · -- `D = -A`, then `C = -B` and the diagonals are parallel
      exfalso
      have hD' : F.D = -F.A := by linear_combination -hD
      have hC' : F.C = -F.B := by
        have := h1; simp only [s₁] at this; linear_combination this - hD'
      apply h
      rw [hD', hC']
      have : (F.A - -F.B) * conj (F.B - -F.A) = ((‖F.A + F.B‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; congr 1 <;> ring_nf
      rw [this, Complex.ofReal_im]
  · rintro ⟨hC, hD⟩
    simp only [s₁, hC, hD]; ring

/-- Lemma 5.3 (f) for `k = 5`: if `5 ∈ K`, the diagonals have different lengths and `s₄ = 1`
(which can be achieved by a rotation), then `s₁ = e^{iχ}`, `s₂ = cos 2χ` and `s₃ = e^{-iχ}` with
`sin 2χ ≠ 0`, i.e. the feet are the roots of `z⁴ - e^{iχ} z³ + cos(2χ) z² - e^{-iχ} z + 1`. -/
theorem m_five_family (h : F.NonParallel) (h5 : F.m 5 = 0) (hd : ‖F.A - F.C‖ ≠ ‖F.B - F.D‖)
    (h4 : F.s₄ = 1) :
    ∃ χ : ℝ, Real.sin (2 * χ) ≠ 0 ∧ F.s₁ = Complex.exp (χ * I) ∧ F.s₂ = Real.cos (2 * χ) ∧
      F.s₃ = Complex.exp (-(χ * I)) := by
  have hp := F.prod_ne_of_diag_ne h hd
  have c1 := F.conj_s₁
  have c2 := F.conj_s₂
  rw [h4, mul_one] at c1 c2
  rw [h4, mul_one, ← c1] at hp
  rw [m_five_iff, ← c1] at h5
  set w := F.s₁ ^ 2 with hw
  -- `s₂` is real, and `w` is not real
  have hs2 : F.s₂.im = 0 := by
    have := congrArg Complex.im c2; simp at this; linarith
  have hwim : w.im ≠ 0 := by
    intro h0
    apply hp
    have : conj w = w := Complex.conj_eq_iff_im.2 h0
    rw [hw, map_pow] at this
    rw [this]; ring
  have hs1 : F.s₁ ≠ 0 := by rintro h0; apply hwim; rw [hw, h0]; simp
  -- `|s₁|² = 2 s₂ w - w²`
  have key : ((Complex.normSq F.s₁ : ℝ) : ℂ) = 2 * F.s₂ * w - w ^ 2 := by
    rw [← Complex.mul_conj, h5]; ring
  have kim := congrArg Complex.im key
  have kre := congrArg Complex.re key
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, Complex.sub_re, Complex.mul_im,
    Complex.mul_re, pow_two, hs2] at kim kre
  norm_num at kim kre
  have hre : F.s₂.re = w.re := by
    have : (F.s₂.re - w.re) * w.im = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hwim
    linarith
  have hn : Complex.normSq F.s₁ = Complex.normSq w := by
    rw [Complex.normSq_apply w]; rw [hre] at kre; linarith
  have hn1 : Complex.normSq F.s₁ = 1 := by
    have h0 : 0 < Complex.normSq F.s₁ := Complex.normSq_pos.2 hs1
    rw [hw, map_pow] at hn
    nlinarith
  have habs : ‖F.s₁‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hn1
    nlinarith [norm_nonneg F.s₁]
  set χ := Complex.arg F.s₁
  have he : F.s₁ = Complex.exp (χ * I) := by
    have := Complex.norm_mul_exp_arg_mul_I F.s₁
    rw [habs] at this; simpa using this.symm
  have hw' : w = Complex.exp ((2 * χ : ℝ) * I) := by
    rw [hw, he, ← Complex.exp_nat_mul]; push_cast; ring_nf
  refine ⟨χ, ?_, he, ?_, ?_⟩
  · have : w.im = Real.sin (2 * χ) := by rw [hw', Complex.exp_ofReal_mul_I_im]
    rwa [← this]
  · apply Complex.ext
    · rw [hre, hw', Complex.exp_ofReal_mul_I_re, Complex.ofReal_re]
    · rw [hs2, Complex.ofReal_im]
  · rw [← c1, he, ← Complex.exp_conj]; congr 1; simp

/-- The table rotated by `ω` (`|ω| = 1`). -/
noncomputable def rotate (ω : ℂ) (hω : ‖ω‖ = 1) : Feet where
  A := ω * F.A
  B := ω * F.B
  C := ω * F.C
  D := ω * F.D
  τ := F.τ
  μ := F.μ
  nA := by rw [norm_mul, hω, F.nA, one_mul]
  nB := by rw [norm_mul, hω, F.nB, one_mul]
  nC := by rw [norm_mul, hω, F.nC, one_mul]
  nD := by rw [norm_mul, hω, F.nD, one_mul]
  hX := by linear_combination ω * F.hX
  τ0 := F.τ0
  τ1 := F.τ1
  μ0 := F.μ0
  μ1 := F.μ1
  AB := fun h => F.AB (mul_left_cancel₀ (ne_zero_of_norm_eq_one hω) h)
  AC := fun h => F.AC (mul_left_cancel₀ (ne_zero_of_norm_eq_one hω) h)
  AD := fun h => F.AD (mul_left_cancel₀ (ne_zero_of_norm_eq_one hω) h)
  BC := fun h => F.BC (mul_left_cancel₀ (ne_zero_of_norm_eq_one hω) h)
  BD := fun h => F.BD (mul_left_cancel₀ (ne_zero_of_norm_eq_one hω) h)
  CD := fun h => F.CD (mul_left_cancel₀ (ne_zero_of_norm_eq_one hω) h)

lemma rotate_m {ω : ℂ} (hω : ‖ω‖ = 1) (k : ℕ) : (F.rotate ω hω).m k = ω ^ k * F.m k := by
  simp only [m, rotate, mul_pow]; ring

lemma rotate_s₄ {ω : ℂ} (hω : ‖ω‖ = 1) : (F.rotate ω hω).s₄ = ω ^ 4 * F.s₄ := by
  simp only [s₄, rotate]; ring

lemma rotate_diag {ω : ℂ} (hω : ‖ω‖ = 1) :
    ‖(F.rotate ω hω).A - (F.rotate ω hω).C‖ = ‖F.A - F.C‖ ∧
      ‖(F.rotate ω hω).B - (F.rotate ω hω).D‖ = ‖F.B - F.D‖ := by
  simp only [rotate, ← mul_sub, norm_mul, hω, one_mul, and_self]

lemma rotate_nonParallel {ω : ℂ} (hω : ‖ω‖ = 1) (h : F.NonParallel) :
    (F.rotate ω hω).NonParallel := by
  have e : ((F.rotate ω hω).A - (F.rotate ω hω).C) * conj ((F.rotate ω hω).B - (F.rotate ω hω).D) =
      (F.A - F.C) * conj (F.B - F.D) := by
    simp only [rotate, ← mul_sub, map_mul]
    have : ω * conj ω = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; simp
    linear_combination ((F.A - F.C) * conj (F.B - F.D)) * this
  unfold NonParallel; rw [e]; exact h

/-- `e^{-2iθ} Q_χ(e^{iθ}) = G_χ(θ)` with `G_χ(θ) = 2 cos 2θ - 2 cos(θ + χ) + cos 2χ`. -/
lemma G_eq (χ θ : ℝ) :
    Complex.exp (-(2 * θ * I)) * (Complex.exp (θ * I) ^ 4 - Complex.exp (χ * I) * Complex.exp (θ * I) ^ 3
      + (Real.cos (2 * χ) : ℂ) * Complex.exp (θ * I) ^ 2 - Complex.exp (-(χ * I)) * Complex.exp (θ * I) + 1)
      = ((2 * Real.cos (2 * θ) - 2 * Real.cos (θ + χ) + Real.cos (2 * χ) : ℝ) : ℂ) := by
  have hE := Complex.exp_ne_zero (θ * I)
  have hX := Complex.exp_ne_zero (χ * I)
  have e1 : Complex.exp (-(2 * θ * I)) = (Complex.exp (θ * I) ^ 2)⁻¹ := by
    rw [exp_ofReal_mul_I_pow, ← Complex.exp_neg]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(χ * I)) = (Complex.exp (χ * I))⁻¹ := Complex.exp_neg _
  have c1 : ((Real.cos (2 * θ) : ℝ) : ℂ) = (Complex.exp (θ * I) ^ 2 + (Complex.exp (θ * I) ^ 2)⁻¹) / 2 := by
    rw [ofReal_cos_eq, exp_ofReal_mul_I_pow θ 2]; push_cast; ring_nf
  have c2 : ((Real.cos (θ + χ) : ℝ) : ℂ) = (Complex.exp (θ * I) * Complex.exp (χ * I) +
      (Complex.exp (θ * I) * Complex.exp (χ * I))⁻¹) / 2 := by
    rw [ofReal_cos_eq, ← Complex.exp_add]; push_cast; ring_nf
  have c3 : ((Real.cos (2 * χ) : ℝ) : ℂ) = (Complex.exp (χ * I) ^ 2 + (Complex.exp (χ * I) ^ 2)⁻¹) / 2 := by
    rw [ofReal_cos_eq, exp_ofReal_mul_I_pow χ 2]; push_cast; ring_nf
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [e1, e2, c1, c2, c3]
  generalize Complex.exp (θ * I) = E at hE ⊢
  generalize Complex.exp (χ * I) = X at hX ⊢
  field_simp
  ring

/-- Lemma 5.3 (f) for `k = 5`, with the normalisation: if `5 ∈ K` and the diagonals have different
lengths, then, after a rotation by some `ω`, the feet are roots of
`z⁴ - e^{iχ} z³ + cos(2χ) z² - e^{-iχ} z + 1` with `sin 2χ ≠ 0` (equivalently, by `G_eq`, zeros of
`G_χ`). -/
theorem m_five_family' (h : F.NonParallel) (h5 : F.m 5 = 0) (hd : ‖F.A - F.C‖ ≠ ‖F.B - F.D‖) :
    ∃ ω : ℂ, ∃ hω : ‖ω‖ = 1, ∃ χ : ℝ, Real.sin (2 * χ) ≠ 0 ∧
      ∀ z ∈ ({(F.rotate ω hω).A, (F.rotate ω hω).B, (F.rotate ω hω).C, (F.rotate ω hω).D} : Set ℂ),
        z ^ 4 - Complex.exp (χ * I) * z ^ 3 + (Real.cos (2 * χ) : ℂ) * z ^ 2
          - Complex.exp (-(χ * I)) * z + 1 = 0 := by
  -- a rotation with `s₄ = 1`
  have hs4 : ‖F.s₄‖ = 1 := by simp [s₄, F.nA, F.nB, F.nC, F.nD]
  set φ := Complex.arg F.s₄
  set ω := Complex.exp ((-(φ / 4) : ℝ) * I)
  have hω : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hs4' : F.s₄ = Complex.exp (φ * I) := by
    have := Complex.norm_mul_exp_arg_mul_I F.s₄; rw [hs4] at this; simpa using this.symm
  have h41 : (F.rotate ω hω).s₄ = 1 := by
    rw [rotate_s₄, hs4', ← Complex.exp_nat_mul, ← Complex.exp_add]; push_cast; ring_nf; simp
  set G := F.rotate ω hω
  have hG5 : G.m 5 = 0 := by rw [rotate_m, h5, mul_zero]
  have hGd : ‖G.A - G.C‖ ≠ ‖G.B - G.D‖ := by
    rw [(F.rotate_diag hω).1, (F.rotate_diag hω).2]; exact hd
  obtain ⟨χ, hχ, e1, e2, e3⟩ := G.m_five_family (F.rotate_nonParallel hω h) hG5 hGd h41
  refine ⟨ω, hω, χ, hχ, ?_⟩
  intro z hz
  have hQ : z ^ 4 - G.s₁ * z ^ 3 + G.s₂ * z ^ 2 - G.s₃ * z + G.s₄ = 0 := by
    rcases hz with rfl | rfl | rfl | rfl <;> simp only [s₁, s₂, s₃, s₄] <;> ring
  rw [e1, e2, e3, h41] at hQ
  exact hQ

/-! ### Lemma 5.3 (c): isosceles trapezoids -/

/-- Lemma 5.3 (c): for the isosceles trapezoid with feet at `α, -α, -β, β`, the intersection of
the diagonals is given by `τ = μ = sin β / (sin α + sin β)`. -/
lemma trapezoid_hX (α β : ℝ) (h : Real.sin α + Real.sin β ≠ 0) :
    ((Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (α * I) +
        ((1 - Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (-(β * I)) =
      ((Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (-(α * I)) +
        ((1 - Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (β * I) := by
  have e : ∀ x : ℝ, Complex.exp (x * I) - Complex.exp (-(x * I)) = 2 * I * Real.sin x := by
    intro x; rw [exp_sub_exp_neg, Complex.ofReal_sin]
  have eα := e α
  have eβ := e β
  set sa := Real.sin α
  set sb := Real.sin β
  have hc : (sa : ℂ) + sb ≠ 0 := by exact_mod_cast h
  push_cast
  generalize Complex.exp (α * I) = Ea at eα ⊢
  generalize Complex.exp (-(α * I)) = Ea' at eα ⊢
  generalize Complex.exp (β * I) = Eb at eβ ⊢
  generalize Complex.exp (-(β * I)) = Eb' at eβ ⊢
  field_simp
  linear_combination (sb : ℂ) * eα - (sa : ℂ) * eβ

/-- Lemma 5.3 (c): `m(k) = 2i (sin α sin kβ - sin β sin kα) / (sin α + sin β)` for the isosceles
trapezoid with feet at `α, -α, -β, β` (and `τ = μ = sin β / (sin α + sin β)`). -/
lemma trapezoid_m (α β : ℝ) (h : Real.sin α + Real.sin β ≠ 0) (k : ℕ) :
    -(((Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (α * I) ^ k
      - ((Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (-(α * I)) ^ k
      + ((1 - Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (-(β * I)) ^ k
      - ((1 - Real.sin β / (Real.sin α + Real.sin β) : ℝ) : ℂ) * Complex.exp (β * I) ^ k) =
      2 * I * ((Real.sin α * Real.sin (k * β) - Real.sin β * Real.sin (k * α) : ℝ) : ℂ) /
        ((Real.sin α + Real.sin β : ℝ) : ℂ) := by
  have e : ∀ x : ℝ, Complex.exp (x * I) ^ k - Complex.exp (-(x * I)) ^ k = 2 * I * Real.sin (k * x) := by
    intro x
    rw [exp_ofReal_mul_I_pow, exp_neg_ofReal_mul_I_pow, exp_sub_exp_neg, Complex.ofReal_sin]
  have eα := e α
  have eβ := e β
  set sa := Real.sin α
  set sb := Real.sin β
  set ska := Real.sin (k * α)
  set skb := Real.sin (k * β)
  have hc : (sa : ℂ) + sb ≠ 0 := by exact_mod_cast h
  push_cast
  generalize Complex.exp (α * I) ^ k = Ea at eα ⊢
  generalize Complex.exp (-(α * I)) ^ k = Ea' at eα ⊢
  generalize Complex.exp (β * I) ^ k = Eb at eβ ⊢
  generalize Complex.exp (-(β * I)) ^ k = Eb' at eβ ⊢
  field_simp
  linear_combination (-(sb : ℂ)) * eα + (sa : ℂ) * eβ

/-- Lemma 5.3 (c) for `k = 4`: if `0 < α < β < π`, then `sin α sin 4β = sin β sin 4α` iff
`cos² α + cos α cos β + cos² β = 1/2`. -/
lemma trapezoid_four_iff {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < Real.pi) :
    Real.sin α * Real.sin (4 * β) - Real.sin β * Real.sin (4 * α) = 0 ↔
      Real.cos α ^ 2 + Real.cos α * Real.cos β + Real.cos β ^ 2 = 1 / 2 := by
  have s4 : ∀ x : ℝ, Real.sin (4 * x) = Real.sin x * (8 * Real.cos x ^ 3 - 4 * Real.cos x) := by
    intro x
    have : 4 * x = 2 * (2 * x) := by ring
    rw [this, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul]; ring
  have sa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (hαβ.trans hβ)
  have sb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (hα.trans hαβ) hβ
  have hcos : Real.cos β < Real.cos α :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hα.le hβ.le hαβ
  rw [s4, s4]
  set x := Real.cos α
  set y := Real.cos β
  have key : Real.sin α * (Real.sin β * (8 * y ^ 3 - 4 * y)) - Real.sin β * (Real.sin α * (8 * x ^ 3 - 4 * x))
      = -(Real.sin α * Real.sin β) * 8 * (x - y) * (x ^ 2 + x * y + y ^ 2 - 1 / 2) := by ring
  rw [key]
  have hxy : x - y ≠ 0 := by linarith
  have hs : Real.sin α * Real.sin β ≠ 0 := by positivity
  constructor
  · intro h0
    have := mul_eq_zero.1 h0
    rcases this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd (neg_eq_zero.1 h3) hs
        · norm_num at h3
      · exact absurd h2 hxy
    · linarith
  · intro h0; rw [show x ^ 2 + x * y + y ^ 2 - 1 / 2 = 0 by linarith]; ring

end Feet

end Wobbly
