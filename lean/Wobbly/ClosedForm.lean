import Wobbly.Modes

/-!
# The third order term for a degenerate mode (Proposition 5.6 of the paper)

For a degenerate mode `k ≥ 2` and `g₁(z) = Re(z^k) + ½(|z|² - 1) Re(b z^{2k})`, the gradient of `g₁`
on the unit circle is `G(u) = conj(k u^{k-1}) + Re(b u^{2k}) u`, and the idealised tilt is
`q₀(θ) = e^{iθ}(X ζ + Y conj ζ)` with `ζ = e^{ikθ}` (`X = α₂`, `Y = conj α₁` in Lemma 5.3 (e), see
`idealTilt_eq` below). Then `w₃(θ) = κ(b) + Re(A_k ζ) + Re(W_{2k} ζ²) + Re(W_{3k} ζ³) + Re(W_{4k} ζ⁴)`.
-/

open Complex ComplexConjugate

namespace Wobbly

lemma dot_eq_complex' (u v : ℂ) : (dot u v : ℂ) = (conj u * v + u * conj v) / 2 := by
  apply Complex.ext <;> simp [dot]; ring

lemma re_eq_complex (z : ℂ) : ((z.re : ℝ) : ℂ) = (z + conj z) / 2 := by
  rw [Complex.re_eq_add_conj]

lemma conj_rot (θ : ℝ) : conj (rot θ) = (rot θ)⁻¹ :=
  (inv_eq_conj_of_norm_eq_one (norm_rot θ)).symm

namespace Feet

variable (F : Feet)

/-- The third order term `w₃ = -½ Σ_E c_E (G(u_E)·q)(u_E·q)`, `u_E = e^{iθ} e_E`. -/
noncomputable def w3 (G : ℂ → ℂ) (θ : ℝ) (q : ℂ) : ℝ :=
  -(1 / 2) * (F.τ * (dot (G (rot θ * F.A)) q * dot (rot θ * F.A) q)
    - F.μ * (dot (G (rot θ * F.B)) q * dot (rot θ * F.B) q)
    + (1 - F.τ) * (dot (G (rot θ * F.C)) q * dot (rot θ * F.C) q)
    - (1 - F.μ) * (dot (G (rot θ * F.D)) q * dot (rot θ * F.D) q))

/-- The gradient on the unit circle of `g₁(z) = Re(z^k) + ½(|z|² - 1) Re(b z^{2k})`. -/
noncomputable def grad₁ (k : ℕ) (b : ℂ) (u : ℂ) : ℂ :=
  conj ((k : ℂ) * u ^ (k - 1)) + (((b * u ^ (2 * k)).re : ℝ) : ℂ) * u

/-- The coefficients of Proposition 5.6 (keeping the terms with `m(k)`). -/
noncomputable def κ (k : ℕ) (b X Y : ℂ) : ℝ :=
  (1 / 8) * (b * (F.m (2 * k + 2) * conj X ^ 2 + 2 * F.m (2 * k) * conj X * Y
    + F.m (2 * k - 2) * Y ^ 2)).re

noncomputable def Ak (k : ℕ) (X Y : ℂ) : ℂ :=
  (k : ℂ) / 4 * (2 * F.m (k - 2) * X * Y + conj (F.m (k - 2)) * conj Y ^ 2
    + F.m k * (X * conj X + Y * conj Y) + conj (F.m k) * X * conj Y)

noncomputable def W2 (k : ℕ) (b X Y : ℂ) : ℂ :=
  b / 4 * ((X * conj X + Y * conj Y) * F.m (2 * k) + X * Y * F.m (2 * k - 2)
    + conj X * conj Y * F.m (2 * k + 2))

noncomputable def W3 (k : ℕ) (X Y : ℂ) : ℂ :=
  (k : ℂ) / 4 * (F.m (k - 2) * X ^ 2 + F.m k * X * conj Y)

noncomputable def W4 (k : ℕ) (b X Y : ℂ) : ℂ :=
  b / 8 * (X ^ 2 * F.m (2 * k - 2) + 2 * X * conj Y * F.m (2 * k) + conj Y ^ 2 * F.m (2 * k + 2))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Proposition 5.6 (identity valid for every `k ≥ 2`, with the terms containing `m(k)`). -/
theorem w3_eq_full {k : ℕ} (hk : 2 ≤ k) (b X Y : ℂ) (θ : ℝ) :
    F.w3 (grad₁ k b) θ (rot θ * (X * rot θ ^ k + Y * conj (rot θ ^ k))) =
      F.κ k b X Y + (F.Ak k X Y * rot θ ^ k).re + (F.W2 k b X Y * (rot θ ^ k) ^ 2).re
        + (F.W3 k X Y * (rot θ ^ k) ^ 3).re + (F.W4 k b X Y * (rot θ ^ k) ^ 4).re := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e1 : j + 2 - 1 = j + 1 := rfl
  have e2 : 2 * (j + 2) - 2 = 2 * j + 2 := by omega
  have e3 : j + 2 - 2 = j := rfl
  apply Complex.ofReal_injective
  simp only [w3, grad₁, κ, Ak, W2, W3, W4, m, e1, e2, e3]
  push_cast
  simp only [dot_eq_complex', re_eq_complex]
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_div₀, map_one, map_inv₀,
    map_ofNat, map_natCast, Complex.conj_conj, Complex.conj_ofReal, conj_rot, inv_inv]
  rw [← inv_eq_conj_of_norm_eq_one F.nA, ← inv_eq_conj_of_norm_eq_one F.nB,
    ← inv_eq_conj_of_norm_eq_one F.nC, ← inv_eq_conj_of_norm_eq_one F.nD]
  have hR : rot θ ≠ 0 := ne_zero_of_norm_eq_one (norm_rot θ)
  have hA := F.A_ne
  have hB := F.B_ne
  have hC := F.C_ne
  have hD := F.D_ne
  generalize rot θ = R at hR ⊢
  have p1 : ∀ z : ℂ, z ^ (j + 1) = z ^ j * z := fun z => by ring
  have p2 : ∀ z : ℂ, z ^ (j + 2) = z ^ j * z ^ 2 := fun z => by ring
  have p3 : ∀ z : ℂ, z ^ (2 * (j + 2)) = (z ^ j) ^ 2 * z ^ 4 := fun z => by ring
  have p4 : ∀ z : ℂ, z ^ (2 * (j + 2) + 2) = (z ^ j) ^ 2 * z ^ 6 := fun z => by ring
  have p5 : ∀ z : ℂ, z ^ (2 * j + 2) = (z ^ j) ^ 2 * z ^ 2 := fun z => by ring
  simp only [inv_pow, p1, p2, p3, p4, p5, mul_pow]
  have hPA : F.A ^ j ≠ 0 := pow_ne_zero _ hA
  have hPB : F.B ^ j ≠ 0 := pow_ne_zero _ hB
  have hPC : F.C ^ j ≠ 0 := pow_ne_zero _ hC
  have hPD : F.D ^ j ≠ 0 := pow_ne_zero _ hD
  have hPR : R ^ j ≠ 0 := pow_ne_zero _ hR
  generalize F.A ^ j = PA at hPA ⊢
  generalize F.B ^ j = PB at hPB ⊢
  generalize F.C ^ j = PC at hPC ⊢
  generalize F.D ^ j = PD at hPD ⊢
  generalize R ^ j = PR at hPR ⊢
  field_simp
  ring

/-- **Proposition 5.6**: if `k ≥ 2` is a degenerate mode, then
`w₃(θ) = κ(b) + Re(A_k ζ) + Re(W_{2k} ζ²) + Re(W_{3k} ζ³) + Re(W_{4k} ζ⁴)`, `ζ = e^{ikθ}`, with
`A_k = (k/4)(2 m(k-2) X Y + conj(m(k-2)) conj(Y)²)` and `W_{3k} = (k/4) m(k-2) X²`. -/
theorem w3_eq {k : ℕ} (hk : 2 ≤ k) (hmk : F.m k = 0) (b X Y : ℂ) (θ : ℝ) :
    F.w3 (grad₁ k b) θ (rot θ * (X * rot θ ^ k + Y * conj (rot θ ^ k))) =
      F.κ k b X Y + ((k : ℂ) / 4 * (2 * F.m (k - 2) * X * Y + conj (F.m (k - 2)) * conj Y ^ 2)
          * rot θ ^ k).re + (F.W2 k b X Y * (rot θ ^ k) ^ 2).re
        + ((k : ℂ) / 4 * (F.m (k - 2) * X ^ 2) * (rot θ ^ k) ^ 3).re
        + (F.W4 k b X Y * (rot θ ^ k) ^ 4).re := by
  rw [F.w3_eq_full hk]
  simp only [Ak, W3, hmk, map_zero, zero_mul, add_zero]

end Feet

end Wobbly
