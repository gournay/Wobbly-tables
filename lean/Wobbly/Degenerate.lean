import Wobbly.ClosedForm
import Wobbly.Remainder

/-!
# Proposition 5.6 (continued): the idealised tilt, and the cancellation by `g₃`

Here the table `T` (with feet on the unit circle) and the feet `F` have the same feet.
-/

open Complex ComplexConjugate

namespace Wobbly

namespace Table

variable {T : Table}

/-- The idealised tilt of `g₁` when `g₁ = Re(z^k)` on the unit circle and `k` is degenerate
(Lemma 5.3 (e)): `q₀(θ) = e^{iθ}(α₂ ζ + conj(α₁) conj(ζ))`, `ζ = e^{ikθ}`. -/
theorem idealTilt_eq {g : ℂ → ℝ} {k : ℕ} {a₀ a₁ a₂ : ℂ}
    (nA : ‖T.A‖ = 1) (nB : ‖T.B‖ = 1) (nC : ‖T.C‖ = 1) (nD : ‖T.D‖ = 1)
    (hg : ∀ z : ℂ, ‖z‖ = 1 → g z = (z ^ k).re)
    (iA : T.A ^ k = a₀ + a₁ * T.A + a₂ * conj T.A) (iB : T.B ^ k = a₀ + a₁ * T.B + a₂ * conj T.B)
    (iC : T.C ^ k = a₀ + a₁ * T.C + a₂ * conj T.C) (iD : T.D ^ k = a₀ + a₁ * T.D + a₂ * conj T.D)
    (θ : ℝ) :
    T.Q g θ 0 = rot θ * (a₂ * rot θ ^ k + conj a₁ * conj (rot θ ^ k)) := by
  set q := rot θ * (a₂ * rot θ ^ k + conj a₁ * conj (rot θ ^ k)) with hq
  -- the values of `g` at the feet are affine, with gradient `q`
  have key : ∀ a : ℂ, ‖a‖ = 1 → a ^ k = a₀ + a₁ * a + a₂ * conj a →
      g (rot θ * a) = (rot θ ^ k * a₀).re + dot (rot θ * a) q := by
    intro a ha e
    rw [hg _ (by rw [norm_rot_mul, ha]), mul_pow, e]
    have hR : conj (rot θ) * rot θ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_rot]; simp
    have hdot : (dot (rot θ * a) q : ℂ) = (conj (rot θ * a) * q + (rot θ * a) * conj q) / 2 :=
      dot_eq_complex' _ _
    apply Complex.ofReal_injective
    rw [Complex.ofReal_add, hdot, re_eq_complex, re_eq_complex]
    simp only [hq, map_mul, map_add, map_pow, Complex.conj_conj]
    linear_combination (-(1 / 2) : ℂ) * (conj a * (a₂ * rot θ ^ k + conj a₁ * conj (rot θ) ^ k)
      + a * (conj a₂ * conj (rot θ) ^ k + a₁ * rot θ ^ k)) * hR
  have hd := T.det_rot_ne θ
  unfold Q
  simp only [foot_zero_tilt]
  symm
  apply eq_solve2 hd
  · rw [key _ nA iA, key _ nC iC, eq_div_iff T.d₁_pos.ne']
    have := T.rot_A_sub_C θ
    have e : dot (rot θ * T.A) q - dot (rot θ * T.C) q = T.d₁ * dot (rot θ * T.e₁) q := by
      rw [← dot_sub_left, this, dot_real_mul_left]
    linarith
  · rw [key _ nB iB, key _ nD iD, eq_div_iff T.d₂_pos.ne']
    have := T.rot_B_sub_D θ
    have e : dot (rot θ * T.B) q - dot (rot θ * T.D) q = T.d₂ * dot (rot θ * T.e₂) q := by
      rw [← dot_sub_left, this, dot_real_mul_left]
    linarith

/-- The idealised wobbling function of `Re(a z^j)` is `-Re(m(j) a e^{ijθ})`. -/
lemma F₀_monomial (F : Feet) (hA : T.A = F.A) (hB : T.B = F.B) (hC : T.C = F.C) (hD : T.D = F.D)
    (a : ℂ) (j : ℕ) (θ : ℝ) :
    F₀ T (fun z => (a * z ^ j).re) F.τ F.μ θ = -(F.m j * a * rot θ ^ j).re := by
  unfold F₀
  simp only [hA, hB, hC, hD, Feet.m, mul_pow]
  apply Complex.ofReal_injective
  push_cast
  simp only [re_eq_complex, map_mul, map_neg, map_sub, map_add, map_pow, map_one, Complex.conj_ofReal]
  ring

/-- `F₀` is additive in the terrain. -/
lemma F₀_add (g h : ℂ → ℝ) (τ μ θ : ℝ) :
    F₀ T (fun z => g z + h z) τ μ θ = F₀ T g τ μ θ + F₀ T h τ μ θ := by
  unfold F₀; ring

/-- The third order terms `w₃` of the table and of the feet agree. -/
lemma w3_eq_feet (F : Feet) (hA : T.A = F.A) (hB : T.B = F.B) (hC : T.C = F.C) (hD : T.D = F.D)
    {G G' : ℂ → ℂ} (hG : ∀ u : ℂ, ‖u‖ = 1 → G u = G' u) (θ : ℝ) (q : ℂ) :
    T.w3 G F.τ F.μ θ q = F.w3 G' θ q := by
  have n : ∀ a : ℂ, ‖a‖ = 1 → ‖rot θ * a‖ = 1 := fun a ha => by rw [norm_rot_mul, ha]
  unfold Table.w3 Feet.w3
  rw [hA, hB, hC, hD, hG _ (n _ F.nA), hG _ (n _ F.nB), hG _ (n _ F.nC), hG _ (n _ F.nD)]

/-- **Proposition 5.6** (consequence): for a degenerate mode `k ≥ 2`, `g₁ = Re(z^k)` on the circle
with gradient `grad₁ k b` there, and `g₃ = Re(a z^{2k} + a' z^{3k} + a'' z^{4k})`,
`W₃ = w₃ + F₀[g₃] = κ(b) + Re(A_k ζ) + Σ_j Re((W_j - m(j) a_j) ζ^{j/k})`; in particular
`W₃ ≥ κ(b) - |A_k| - Σ_j |W_j - m(j) a_j|`. -/
theorem W3_ge (F : Feet) (hA : T.A = F.A) (hB : T.B = F.B) (hC : T.C = F.C) (hD : T.D = F.D)
    {k : ℕ} (hk : 2 ≤ k) (hmk : F.m k = 0) (b a a' a'' : ℂ) {g₁ : ℂ → ℝ} {G₁ : ℂ → ℂ}
    (hg₁ : ∀ z : ℂ, ‖z‖ = 1 → g₁ z = (z ^ k).re) (hG₁ : ∀ u : ℂ, ‖u‖ = 1 → G₁ u = Feet.grad₁ k b u)
    (θ : ℝ) :
    F.κ k b (F.m (k - 1) / conj (F.m 2)) (conj (F.m (k + 1)) / conj (F.m 2))
      - ‖(k : ℂ) / 4 * (2 * F.m (k - 2) * (F.m (k - 1) / conj (F.m 2)) *
          (conj (F.m (k + 1)) / conj (F.m 2)) +
          conj (F.m (k - 2)) * conj (conj (F.m (k + 1)) / conj (F.m 2)) ^ 2)‖
      - ‖F.W2 k b (F.m (k - 1) / conj (F.m 2)) (conj (F.m (k + 1)) / conj (F.m 2)) - F.m (2 * k) * a‖
      - ‖(k : ℂ) / 4 * (F.m (k - 2) * (F.m (k - 1) / conj (F.m 2)) ^ 2) - F.m (3 * k) * a'‖
      - ‖F.W4 k b (F.m (k - 1) / conj (F.m 2)) (conj (F.m (k + 1)) / conj (F.m 2)) - F.m (4 * k) * a''‖
      ≤ T.w3 G₁ F.τ F.μ θ (T.Q g₁ θ 0) +
        F₀ T (fun z => (a * z ^ (2 * k) + a' * z ^ (3 * k) + a'' * z ^ (4 * k)).re) F.τ F.μ θ := by
  obtain ⟨a₀, a₁, a₂, iA, iB, iC, iD⟩ := (F.m_eq_zero_iff k).1 hmk
  obtain ⟨e1, e2, -⟩ := F.interp_coeffs (by omega) hmk ⟨iA, iB, iC, iD⟩
  have hm2 := F.m_two_ne_zero
  have hm2c : conj (F.m 2) ≠ 0 := (map_ne_zero _).2 hm2
  have hX : a₂ = F.m (k - 1) / conj (F.m 2) := by rw [e2]; field_simp
  have hY : conj a₁ = conj (F.m (k + 1)) / conj (F.m 2) := by
    rw [e1, map_mul]; field_simp
  have nA : ‖T.A‖ = 1 := hA ▸ F.nA
  have nB : ‖T.B‖ = 1 := hB ▸ F.nB
  have nC : ‖T.C‖ = 1 := hC ▸ F.nC
  have nD : ‖T.D‖ = 1 := hD ▸ F.nD
  rw [idealTilt_eq nA nB nC nD hg₁ (hA ▸ iA) (hB ▸ iB) (hC ▸ iC) (hD ▸ iD) θ,
    w3_eq_feet F hA hB hC hD hG₁, F.w3_eq hk hmk, hX, hY]
  set X := F.m (k - 1) / conj (F.m 2)
  set Y := conj (F.m (k + 1)) / conj (F.m 2)
  have hsum : (fun z : ℂ => (a * z ^ (2 * k) + a' * z ^ (3 * k) + a'' * z ^ (4 * k)).re) =
      fun z => (a * z ^ (2 * k)).re + ((a' * z ^ (3 * k)).re + (a'' * z ^ (4 * k)).re) := by
    ext z; simp only [Complex.add_re]; ring
  rw [hsum, F₀_add, F₀_add, F₀_monomial F hA hB hC hD, F₀_monomial F hA hB hC hD,
    F₀_monomial F hA hB hC hD]
  set ζ := rot θ ^ k
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_rot]
  have e2k : rot θ ^ (2 * k) = ζ ^ 2 := by rw [← pow_mul, mul_comm]
  have e3k : rot θ ^ (3 * k) = ζ ^ 3 := by rw [← pow_mul, mul_comm]
  have e4k : rot θ ^ (4 * k) = ζ ^ 4 := by rw [← pow_mul, mul_comm]
  rw [e2k, e3k, e4k]
  have r1 : ∀ z : ℂ, ∀ n : ℕ, -‖z‖ ≤ (z * ζ ^ n).re := fun z n => by
    have := Complex.abs_re_le_norm (z * ζ ^ n)
    rw [norm_mul, norm_pow, hζ, one_pow, mul_one] at this
    linarith [neg_abs_le (z * ζ ^ n).re]
  have c1 := r1 ((k : ℂ) / 4 * (2 * F.m (k - 2) * X * Y + conj (F.m (k - 2)) * conj Y ^ 2)) 1
  have c2 := r1 (F.W2 k b X Y - F.m (2 * k) * a) 2
  have c3 := r1 ((k : ℂ) / 4 * (F.m (k - 2) * X ^ 2) - F.m (3 * k) * a') 3
  have c4 := r1 (F.W4 k b X Y - F.m (4 * k) * a'') 4
  simp only [pow_one] at c1
  simp only [sub_mul, Complex.sub_re] at c2 c3 c4
  have hm : ∀ z w : ℂ, (z * w * ζ ^ 2).re = (z * w * ζ ^ 2).re := fun _ _ => rfl
  linarith [show (F.m (2 * k) * a * ζ ^ 2).re = (F.m (2 * k) * a * ζ ^ 2).re from rfl]

end Table

end Wobbly
