import Wobbly.Orbit

/-!
# The hexagonal table (Corollary 5.12 of the paper)

The feet are four consecutive vertices of the regular hexagon of radius `1`:
`A = 1`, `B = ω`, `C = ω²`, `D = ω³ = -1` with `ω = exp (iπ/3)`. The diagonals `AC` and `BD` have
length `√3` and make an angle of `60°`, so that `K = 2`; they meet at
`X = (1/3) A + (2/3) C = (2/3) B + (1/3) D`.
We check the coercivity of the circulant operator with `σ = 2/√3`, and deduce that the table can
be stabilised on every terrain with Lipschitz constant `L ≤ 0.065`.
-/

noncomputable section

open Complex

namespace Wobbly

/-! ## The sixth roots of unity -/

lemma ω6_eq : ω 6 = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  have h : (2 * Real.pi / ((6 : ℕ) : ℝ)) = Real.pi / 3 := by push_cast; ring
  apply Complex.ext
  · simp only [ω, rot]
    rw [h, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  · simp only [ω, rot]
    rw [h, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma ω6_pow_two : ω 6 ^ 2 = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := by
  rw [ω6_eq, sq]
  apply Complex.ext <;> simp only [mul_re, mul_im] <;> nlinarith [sqrt3_sq]

lemma ω6_pow_three : ω 6 ^ 3 = -1 := by
  rw [pow_succ, ω6_pow_two, ω6_eq]
  apply Complex.ext <;> simp only [mul_re, mul_im, neg_re, neg_im, one_re, one_im] <;>
    nlinarith [sqrt3_sq]

lemma ω6_pow_four : ω 6 ^ 4 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  rw [pow_succ, ω6_pow_three, ω6_eq]
  apply Complex.ext <;> simp only [mul_re, mul_im, neg_re, neg_im, one_re, one_im] <;> ring

lemma ω6_pow_five : ω 6 ^ 5 = ⟨1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  rw [pow_succ, ω6_pow_four, ω6_eq]
  apply Complex.ext <;> simp only [mul_re, mul_im] <;> nlinarith [sqrt3_sq]

/-! ## The hexagonal table -/

lemma norm_ω6_pow (k : ℕ) : ‖ω 6 ^ k‖ = 1 := norm_ω_pow 6 k

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

lemma hex_AC : (1 : ℂ) - ω 6 ^ 2 = ⟨3 / 2, -(Real.sqrt 3 / 2)⟩ := by
  rw [ω6_pow_two]; apply Complex.ext <;> simp; ring

lemma hex_BD : ω 6 - ω 6 ^ 3 = ⟨3 / 2, Real.sqrt 3 / 2⟩ := by
  rw [ω6_pow_three, ω6_eq]; apply Complex.ext <;> simp; ring

lemma norm_hex_AC : ‖(1 : ℂ) - ω 6 ^ 2‖ = Real.sqrt 3 := by
  rw [hex_AC, ← Real.sqrt_sq (norm_nonneg _), sq_norm_eq]
  congr 1
  simp only
  nlinarith [sqrt3_sq]

lemma norm_hex_BD : ‖ω 6 - ω 6 ^ 3‖ = Real.sqrt 3 := by
  rw [hex_BD, ← Real.sqrt_sq (norm_nonneg _), sq_norm_eq]
  congr 1
  simp only
  nlinarith [sqrt3_sq]

lemma unit_hex_AC : unit ((1 : ℂ) - ω 6 ^ 2) = ⟨Real.sqrt 3 / 2, -(1 / 2)⟩ := by
  rw [unit, norm_hex_AC, hex_AC]
  have h := sqrt3_pos.ne'
  apply Complex.ext <;> simp [mul_re, mul_im] <;> field_simp; nlinarith [sqrt3_sq]

lemma unit_hex_BD : unit (ω 6 - ω 6 ^ 3) = ⟨Real.sqrt 3 / 2, 1 / 2⟩ := by
  rw [unit, norm_hex_BD, hex_BD]
  have h := sqrt3_pos.ne'
  apply Complex.ext <;> simp [mul_re, mul_im] <;> field_simp; nlinarith [sqrt3_sq]

lemma dot_hex_diagonals : dot (unit ((1 : ℂ) - ω 6 ^ 2)) (unit (ω 6 - ω 6 ^ 3)) = 1 / 2 := by
  rw [unit_hex_AC, unit_hex_BD]
  unfold dot
  simp only
  nlinarith [sqrt3_sq]

/-- The hexagonal table: feet at `1, ω, ω², ω³` with `ω = exp (iπ/3)`. -/
def hexTable : Table where
  A := 1
  B := ω 6
  C := ω 6 ^ 2
  D := ω 6 ^ 3
  r := 1
  normA := by simp
  normB := by rw [show ω 6 = ω 6 ^ 1 by ring, norm_ω6_pow]
  normC := by rw [norm_ω6_pow]
  normD := by rw [norm_ω6_pow]
  AC_ne := by
    intro h
    have := norm_hex_AC
    rw [sub_eq_zero.2 h, norm_zero] at this
    exact sqrt3_pos.ne this
  BD_ne := by
    intro h
    have := norm_hex_BD
    rw [sub_eq_zero.2 h, norm_zero] at this
    exact sqrt3_pos.ne this
  not_parallel := by
    rw [dot_hex_diagonals]; norm_num [abs_of_pos]

lemma hex_d₁ : hexTable.d₁ = Real.sqrt 3 := norm_hex_AC
lemma hex_d₂ : hexTable.d₂ = Real.sqrt 3 := norm_hex_BD
lemma hex_dmin : hexTable.dmin = Real.sqrt 3 := by
  rw [Table.dmin, hex_d₁, hex_d₂, min_self]
lemma hex_γ : hexTable.γ = 1 / 2 := by
  rw [Table.γ, Table.e₁, Table.e₂]
  show |dot (unit ((1 : ℂ) - ω 6 ^ 2)) (unit (ω 6 - ω 6 ^ 3))| = 1 / 2
  rw [dot_hex_diagonals]; norm_num
lemma hex_K : hexTable.K = 2 := by
  rw [Table.K, hex_γ]
  rw [show (2 : ℝ) / (1 - 1 / 2) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## Rationality and coercivity -/

lemma hex_rational :
    IsRational hexTable 6 0 1 2 3 (1 / 3) (2 / 3) where
  hn := by norm_num
  hA := by simp [hexTable]
  hB := by
    show ω 6 = ((1 : ℝ) : ℂ) * ω 6 ^ (1 : ZMod 6).val
    rw [show (1 : ZMod 6).val = 1 from rfl]; simp
  hC := by
    show ω 6 ^ 2 = ((1 : ℝ) : ℂ) * ω 6 ^ (2 : ZMod 6).val
    rw [show (2 : ZMod 6).val = 2 from rfl]; simp
  hD := by
    show ω 6 ^ 3 = ((1 : ℝ) : ℂ) * ω 6 ^ (3 : ZMod 6).val
    rw [show (3 : ZMod 6).val = 3 from rfl]; simp
  hX := by
    show ((1 / 3 : ℝ) : ℂ) * 1 + ((1 - 1 / 3 : ℝ) : ℂ) * ω 6 ^ 2 =
      ((2 / 3 : ℝ) : ℂ) * ω 6 + ((1 - 2 / 3 : ℝ) : ℂ) * ω 6 ^ 3
    rw [ω6_pow_two, ω6_pow_three, ω6_eq]
    apply Complex.ext <;> simp <;> ring
  hτ0 := by norm_num
  hτ1 := by norm_num
  hμ0 := by norm_num
  hμ1 := by norm_num

lemma sum_zmod6 (f : ZMod 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 :=
  Fin.sum_univ_six f

lemma sum_zmod6_complex (f : ZMod 6 → ℂ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 :=
  Fin.sum_univ_six f

/-- The circulant operator of the hexagonal table is coercive with `σ = 2/√3`. -/
lemma hex_coercive : Coercive (0 : ZMod 6) 1 2 3 (1 / 3) (2 / 3) (2 / Real.sqrt 3) := by
  intro N h1 h2
  rw [sum_zmod6] at h1
  rw [sum_zmod6_complex] at h2
  -- the real and imaginary parts of `Σ N_i ω^i = 0`
  have hv : ∀ k : ZMod 6, ω 6 ^ k.val = ω 6 ^ (k.val : ℕ) := fun k => rfl
  have e0 : (0 : ZMod 6).val = 0 := rfl
  have e1 : (1 : ZMod 6).val = 1 := rfl
  have e2 : (2 : ZMod 6).val = 2 := rfl
  have e3 : (3 : ZMod 6).val = 3 := rfl
  have e4 : (4 : ZMod 6).val = 4 := rfl
  have e5 : (5 : ZMod 6).val = 5 := rfl
  rw [e0, e1, e2, e3, e4, e5, pow_zero, pow_one, ω6_pow_two, ω6_pow_three, ω6_pow_four,
    ω6_pow_five, ω6_eq] at h2
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp only [add_re, mul_re, ofReal_re, ofReal_im, one_re, one_im, neg_re, zero_re, add_im,
    mul_im, neg_im, zero_im] at hre him
  have c2 : N 0 + N 1 / 2 - N 2 / 2 - N 3 - N 4 / 2 + N 5 / 2 = 0 := by linarith
  have c3 : N 1 + N 2 - N 4 - N 5 = 0 := by
    have hs := sqrt3_pos
    have : Real.sqrt 3 / 2 * (N 1 + N 2 - N 4 - N 5) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  -- the quadratic form
  rw [sum_zmod6, sum_zmod6]
  simp only [circ]
  have i1 : (1 : ZMod 6) + 5 = 0 := rfl
  have i2 : (2 : ZMod 6) + 4 = 0 := rfl
  have i3 : (3 : ZMod 6) + 3 = 0 := rfl
  have i4 : (2 : ZMod 6) + 5 = 1 := rfl
  have i5 : (3 : ZMod 6) + 4 = 1 := rfl
  have i6 : (3 : ZMod 6) + 5 = 2 := rfl
  have j1 : (0 : ZMod 6) + 1 = 1 := rfl
  have j2 : (0 : ZMod 6) + 2 = 2 := rfl
  have j3 : (0 : ZMod 6) + 3 = 3 := rfl
  have j4 : (0 : ZMod 6) + 4 = 4 := rfl
  have j5 : (0 : ZMod 6) + 5 = 5 := rfl
  have j0 : (0 : ZMod 6) + 0 = 0 := rfl
  have k1 : (1 : ZMod 6) + 0 = 1 := rfl
  have k2 : (1 : ZMod 6) + 1 = 2 := rfl
  have k3 : (1 : ZMod 6) + 2 = 3 := rfl
  have k4 : (1 : ZMod 6) + 3 = 4 := rfl
  have k5 : (1 : ZMod 6) + 4 = 5 := rfl
  have l0 : (2 : ZMod 6) + 0 = 2 := rfl
  have l1 : (2 : ZMod 6) + 1 = 3 := rfl
  have l2 : (2 : ZMod 6) + 2 = 4 := rfl
  have l3 : (2 : ZMod 6) + 3 = 5 := rfl
  have m0 : (3 : ZMod 6) + 0 = 3 := rfl
  have m1 : (3 : ZMod 6) + 1 = 4 := rfl
  have m2 : (3 : ZMod 6) + 2 = 5 := rfl
  rw [i1, i2, i3, i4, i5, i6, j1, j2, j3, j4, j5, j0, k1, k2, k3, k4, k5, l0, l1, l2, l3, m0, m1,
    m2]
  have hσ : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by rw [div_pow, sqrt3_sq]; norm_num
  rw [hσ]
  have key : (1 / 3 * N 0 - 2 / 3 * N 1 + (1 - 1 / 3) * N 2 - (1 - 2 / 3) * N 3) ^ 2 +
      (1 / 3 * N 1 - 2 / 3 * N 2 + (1 - 1 / 3) * N 3 - (1 - 2 / 3) * N 4) ^ 2 +
      (1 / 3 * N 2 - 2 / 3 * N 3 + (1 - 1 / 3) * N 4 - (1 - 2 / 3) * N 5) ^ 2 +
      (1 / 3 * N 3 - 2 / 3 * N 4 + (1 - 1 / 3) * N 5 - (1 - 2 / 3) * N 0) ^ 2 +
      (1 / 3 * N 4 - 2 / 3 * N 5 + (1 - 1 / 3) * N 0 - (1 - 2 / 3) * N 1) ^ 2 +
      (1 / 3 * N 5 - 2 / 3 * N 0 + (1 - 1 / 3) * N 1 - (1 - 2 / 3) * N 2) ^ 2 -
      4 / 3 * (N 0 ^ 2 + N 1 ^ 2 + N 2 ^ 2 + N 3 ^ 2 + N 4 ^ 2 + N 5 ^ 2) =
      4 / 9 * (N 0 - N 1 + N 2 - N 3 + N 4 - N 5) ^ 2 := by
    linear_combination
      (-4 / 9 * N 0 + 2 / 9 * N 2 - 4 / 9 * N 4 - 2 / 3 * N 5) * h1 +
      (-2 / 9 * N 0 + 4 / 9 * N 2 + 2 / 3 * N 3 + 4 / 9 * N 4) * c2 +
      (-1 / 3 * N 0 - 2 / 3 * N 1 - 2 / 3 * N 2 - 1 / 3 * N 3) * c3
  nlinarith [sq_nonneg (N 0 - N 1 + N 2 - N 3 + N 4 - N 5)]

/-! ## Corollary 5.12 -/

lemma sqrt2_bounds : 1.4142 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.4143 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma sqrt3_bounds : 1.7320 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 1.7321 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma sqrt6_bounds : 2.4494 ≤ Real.sqrt 6 ∧ Real.sqrt 6 ≤ 2.4495 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- Corollary 5.12: the hexagonal table can be stabilised by rotating it on every terrain with
Lipschitz constant `L ≤ 0.065`. -/
theorem hexagon_balanced {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) (hL : L ≤ 0.065) :
    ∃ θ, ∃ q c, ‖q‖ < 1 ∧ resid g θ q c hexTable.A = 0 ∧ resid g θ q c hexTable.B = 0 ∧
      resid g θ q c hexTable.C = 0 ∧ resid g θ q c hexTable.D = 0 := by
  have hL0 := hg.nonneg
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds
  obtain ⟨s3l, s3u⟩ := sqrt3_bounds
  obtain ⟨s6l, s6u⟩ := sqrt6_bounds
  have hK := hex_K
  have hdmin := hex_dmin
  have hr : hexTable.r = 1 := rfl
  -- `t = 2√2 L` and `ψ(t) ≤ (2/√3) t`
  set t := Real.sqrt 2 * hexTable.K * L with ht
  have ht' : t = 2 * Real.sqrt 2 * L := by rw [ht, hK]; ring
  have ht0 : 0 ≤ t := by rw [ht']; positivity
  have ht1 : t ≤ 0.1839 := by rw [ht']; nlinarith
  have hψ : Table.ψ t ≤ 2 / Real.sqrt 3 * t := psi_le ht0 (by linarith)
  have hψ' : Table.ψ t ≤ 1.1548 * t := by
    have : 2 / Real.sqrt 3 ≤ 1.1548 := by
      rw [div_le_iff₀ sqrt3_pos]; nlinarith
    nlinarith
  have hψ0 : 0 ≤ Table.ψ t := Table.ψ_nonneg ht0
  -- `η = 2 L r ψ(t) ≤ 2 · 1.1548 · 2 · 1.4143 · L² ≤ 0.02761`
  have hL2 : L ^ 2 ≤ 0.004225 := by nlinarith
  have hη : 2 * L * hexTable.r * Table.ψ t ≤ 0.02761 := by
    rw [hr]
    calc 2 * L * 1 * Table.ψ t ≤ 2 * L * (1.1548 * t) := by nlinarith
      _ = 2 * 1.1548 * 2 * Real.sqrt 2 * L ^ 2 := by rw [ht']; ring
      _ ≤ 2 * 1.1548 * 2 * 1.4143 * 0.004225 := by gcongr
      _ ≤ 0.02761 := by norm_num
  have hη0 : 0 ≤ 2 * L * hexTable.r * Table.ψ t := by rw [hr]; positivity
  -- `λ' = K η / d_min ≤ 2 · 0.02761 / 1.732 ≤ 0.03189`
  have hlam : hexTable.K * (2 * L * hexTable.r * Table.ψ t / hexTable.dmin) ≤ 0.03189 := by
    rw [hK, hdmin]
    have : 2 * L * hexTable.r * Table.ψ t / Real.sqrt 3 ≤ 0.02761 / 1.7320 := by
      apply div_le_div₀ (by norm_num) hη (by norm_num) s3l
    nlinarith
  have hlam0 : 0 ≤ hexTable.K * (2 * L * hexTable.r * Table.ψ t / hexTable.dmin) := by
    rw [hK, hdmin]; positivity
  have hsmall : Table.SmallL hexTable L := by
    refine ⟨hL0, by rw [hK]; linarith, ?_⟩
    rw [hK, hdmin, hr]
    have : 4 / Real.sqrt 3 * (1 / Real.sqrt 3) * (L * 2) ^ 2 = 16 / 3 * L ^ 2 := by
      field_simp; rw [sqrt3_sq]; ring
    rw [this]; nlinarith
  have hd : Table.OrbitData hexTable L 6 (2 / Real.sqrt 3) := by
    refine ⟨by linarith, ?_, by linarith, by positivity, by rw [hr]; norm_num, ?_⟩
    · -- `2 L ψ(t) < 1`
      have : 2 * L * Table.ψ t ≤ 0.02761 := by rw [hr] at hη; linarith
      linarith
    · -- `(n + 1) A η < 1` with `A = 2 K √6 / (σ d_min (1 - λ')) = 2√6 / (1 - λ')`
      rw [← ht, hK, hdmin, hr]
      rw [hr] at hη hη0
      set η := 2 * L * 1 * Table.ψ t with hη'
      have hs3 : Real.sqrt 3 ≠ 0 := sqrt3_pos.ne'
      have hlam1 : 2 * (η / Real.sqrt 3) ≤ 0.03189 := by
        have : η / Real.sqrt 3 ≤ 0.02761 / 1.7320 := div_le_div₀ (by norm_num) hη (by norm_num) s3l
        linarith
      have hden : 0 < 1 - 2 * (η / Real.sqrt 3) := by linarith
      refine lt_of_eq_of_lt (b := 14 * Real.sqrt 6 * η / (1 - 2 * (η / Real.sqrt 3))) ?_ ?_
      · have h1 := hden.ne'
        push_cast
        field_simp
        ring
      · rw [div_lt_one hden]
        nlinarith [mul_le_mul s6u hη hη0 (by norm_num : (0 : ℝ) ≤ 2.4495)]
  exact Table.exists_balanced hex_rational hex_coercive hg hsmall hd

end Wobbly
