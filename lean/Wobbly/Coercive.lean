import Wobbly.Rectangle

/-!
# Coercivity of the circulant operator from `m(s) ≠ 0` (Theorem 5.11)

For a rational table with feet at the vertices `iA, iB, iC, iD` of the regular `n`-gon, the
circulant operator `C` of `Wobbly.circ` is diagonal in the discrete Fourier basis: it multiplies the
mode `s` by `-m(-s)`, where `m(s) = -Σ_E c_E ω^{s i_E}` (`mR`). By Parseval's identity, if
`|m(s)| ≥ σ` for all `s ≢ 0, ±1 mod n`, then `‖C N‖ ≥ σ ‖N‖` for the vectors `N` without modes
`0, ±1`; this is `Wobbly.Coercive`.
-/

open Complex ComplexConjugate Finset

namespace Wobbly

variable {n : ℕ} [NeZero n]

/-- The character `χ_s(j) = ω^{s j}` of `ZMod n`. -/
noncomputable def χ (s j : ZMod n) : ℂ := ω n ^ (s * j).val

lemma χ_add_right (s a b : ZMod n) : χ s (a + b) = χ s a * χ s b := by
  unfold χ; rw [mul_add, ω_pow_val_add]

lemma χ_add_left (s t j : ZMod n) : χ (s + t) j = χ s j * χ t j := by
  unfold χ; rw [add_mul, ω_pow_val_add]

omit [NeZero n] in
lemma χ_comm (s j : ZMod n) : χ s j = χ j s := by unfold χ; rw [mul_comm]

omit [NeZero n] in
lemma χ_zero_left (j : ZMod n) : χ 0 j = 1 := by simp [χ]

omit [NeZero n] in
lemma χ_zero_right (s : ZMod n) : χ s 0 = 1 := by simp [χ]

omit [NeZero n] in
lemma norm_χ (s j : ZMod n) : ‖χ s j‖ = 1 := norm_ω_pow n _

omit [NeZero n] in
lemma χ_mul_conj (s j : ZMod n) : χ s j * conj (χ s j) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_χ]; simp

omit [NeZero n] in
lemma χ_one_left (j : ZMod n) : χ 1 j = ω n ^ j.val := by simp [χ]

lemma χ_neg_left (s j : ZMod n) : χ (-s) j = conj (χ s j) := by
  have h := χ_add_left (-s) s j
  rw [neg_add_cancel, χ_zero_left] at h
  have h2 := χ_mul_conj s j
  have hne : χ s j ≠ 0 := by
    intro h0; have := norm_χ s j; rw [h0, norm_zero] at this; exact zero_ne_one this
  calc χ (-s) j = χ (-s) j * (χ s j * conj (χ s j)) := by rw [h2, mul_one]
    _ = (χ (-s) j * χ s j) * conj (χ s j) := by ring
    _ = conj (χ s j) := by rw [← h, one_mul]

/-- Orthogonality of the characters. -/
lemma sum_χ (d : ZMod n) : ∑ s : ZMod n, χ s d = if d = 0 then (n : ℂ) else 0 := by
  split_ifs with hd
  · subst hd; simp [χ_zero_right]
  · have e : ∀ s : ZMod n, χ s d = (ω n ^ d.val) ^ s.val := fun s => by
      unfold χ; rw [ZMod.val_mul, ω_pow_mod (NeZero.ne n), ← pow_mul, mul_comm]
    simp only [e]
    have hprim := ω_isPrimitiveRoot (NeZero.ne n)
    have h1 : ω n ^ d.val ≠ 1 := by
      apply hprim.pow_ne_one_of_pos_of_lt
      · exact fun h => hd ((ZMod.val_eq_zero d).1 h)
      · exact ZMod.val_lt d
    have hpow : (ω n ^ d.val) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ω_pow_n (NeZero.ne n), one_pow]
    rw [sum_zmod_pow, geom_sum_eq h1, hpow, sub_self, zero_div]

/-- The discrete Fourier transform `x̂(s) = Σ_j x_j χ_s(j)`. -/
noncomputable def dft (x : ZMod n → ℝ) (s : ZMod n) : ℂ := ∑ j, (x j : ℂ) * χ s j

/-- Parseval's identity: `Σ_s |x̂(s)|² = n Σ_j x_j²`. -/
lemma parseval (x : ZMod n → ℝ) : ∑ s, ‖dft x s‖ ^ 2 = n * ∑ j, x j ^ 2 := by
  have key : ∑ s, dft x s * conj (dft x s) = ∑ j, (n : ℂ) * (x j : ℂ) ^ 2 := by
    have e1 : ∀ s, dft x s * conj (dft x s) =
        ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * χ s (j - k) := by
      intro s
      unfold dft
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      have h : χ s j = χ s (j - k) * χ s k := by rw [← χ_add_right, sub_add_cancel]
      rw [map_mul, Complex.conj_ofReal, h]
      have := χ_mul_conj s k
      linear_combination ((x j : ℂ) * (x k : ℂ) * χ s (j - k)) * this
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have e2 : ∀ k, ∑ s, (x j : ℂ) * (x k : ℂ) * χ s (j - k) =
        (x j : ℂ) * (x k : ℂ) * (if j - k = 0 then (n : ℂ) else 0) := by
      intro k; rw [← Finset.mul_sum, sum_χ]
    simp only [e2, sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at key
  push_cast at key
  have : ((∑ s, ‖dft x s‖ ^ 2 : ℝ) : ℂ) = ((n * ∑ j, x j ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [key, Finset.mul_sum]
  exact_mod_cast this

/-- The multiplier `m(s) = -Σ_E c_E e_E^s` of a rational table, with `e_E = ω^{i_E}`
(Remark 4.12 and Lemma 5.3 for the feet at the vertices `iA, iB, iC, iD` of the `n`-gon). -/
noncomputable def mR (iA iB iC iD : ZMod n) (τ μ : ℝ) (s : ZMod n) : ℂ :=
  -((τ : ℂ) * χ s iA - (μ : ℂ) * χ s iB + ((1 - τ : ℝ) : ℂ) * χ s iC - ((1 - μ : ℝ) : ℂ) * χ s iD)

omit [NeZero n] in
lemma χ_neg_neg (s a : ZMod n) : χ (-s) a = χ s (-a) := by unfold χ; congr 2; ring

/-- Shifting a vector multiplies its Fourier transform by a character. -/
lemma dft_shift (N : ZMod n → ℝ) (a s : ZMod n) :
    ∑ j, (N (a + j) : ℂ) * χ s j = χ s (-a) * dft N s := by
  unfold dft
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun j => ?_
  simp only [Equiv.coe_addLeft]
  have h1 : χ s (-a) * χ s (a + j) = χ s j := by
    rw [← χ_add_right, neg_add_cancel_left]
  rw [← h1]; ring

/-- The circulant operator is diagonal in the Fourier basis. -/
lemma dft_circ (iA iB iC iD : ZMod n) (τ μ : ℝ) (N : ZMod n → ℝ) (s : ZMod n) :
    dft (circ iA iB iC iD τ μ N) s = -mR iA iB iC iD τ μ (-s) * dft N s := by
  have e : dft (circ iA iB iC iD τ μ N) s = (τ : ℂ) * ∑ j, (N (iA + j) : ℂ) * χ s j
      - (μ : ℂ) * ∑ j, (N (iB + j) : ℂ) * χ s j + ((1 - τ : ℝ) : ℂ) * ∑ j, (N (iC + j) : ℂ) * χ s j
      - ((1 - μ : ℝ) : ℂ) * ∑ j, (N (iD + j) : ℂ) * χ s j := by
    unfold dft circ
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [e, dft_shift, dft_shift, dft_shift, dft_shift, mR]
  simp only [χ_neg_neg]
  ring

/-- **Coercivity from non-degeneracy** (the step of Theorem 5.11 which uses `σ`): if
`|m(s)| ≥ σ` for all `s ≢ 0, ±1 mod n`, then `σ ‖N‖ ≤ ‖C N‖` for all `N` orthogonal to the affine
functions on the `n`-gon. -/
theorem coercive_of_nondeg {iA iB iC iD : ZMod n} {τ μ σ : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ s : ZMod n, s ≠ 0 → s ≠ 1 → s ≠ -1 → σ ≤ ‖mR iA iB iC iD τ μ s‖) :
    Coercive iA iB iC iD τ μ σ := by
  intro N h0 h1
  have hN0 : dft N 0 = 0 := by
    unfold dft; simp only [χ_zero_left, mul_one]; exact_mod_cast h0
  have hN1 : dft N 1 = 0 := by
    unfold dft; simp only [χ_one_left]; exact h1
  have hNm1 : dft N (-1) = 0 := by
    have : dft N (-1) = conj (dft N 1) := by
      unfold dft; rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [χ_neg_left, map_mul, Complex.conj_ofReal]
    rw [this, hN1, map_zero]
  have hterm : ∀ s, σ ^ 2 * ‖dft N s‖ ^ 2 ≤ ‖dft (circ iA iB iC iD τ μ N) s‖ ^ 2 := by
    intro s
    rw [dft_circ, norm_mul, norm_neg, mul_pow]
    by_cases hs : s = 0 ∨ s = 1 ∨ s = -1
    · rcases hs with rfl | rfl | rfl
      · rw [hN0]; simp
      · rw [hN1]; simp
      · rw [hNm1]; simp
    · push Not at hs
      obtain ⟨hs0, hs1, hs2⟩ := hs
      have h := hm (-s) (neg_ne_zero.2 hs0) (fun e => hs2 (by rw [← neg_neg s, e]))
        (fun e => hs1 (by rw [← neg_neg s, e, neg_neg]))
      have : σ ^ 2 ≤ ‖mR iA iB iC iD τ μ (-s)‖ ^ 2 := pow_le_pow_left₀ hσ h 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
  rw [← Finset.mul_sum, parseval, parseval] at hsum
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith

lemma le_norm_mk {a b B : ℝ} (hB : 0 ≤ B) (h : B ^ 2 ≤ a ^ 2 + b ^ 2) : B ≤ ‖(⟨a, b⟩ : ℂ)‖ := by
  rw [Complex.norm_def, Complex.normSq_mk, Real.le_sqrt hB (by nlinarith)]; nlinarith

/-- The coercivity of the hexagonal table (`Wobbly.hex_coercive`) as a special case of
`coercive_of_nondeg`: `|m(2)| = |m(4)| = 2/√3` and `|m(3)| = 2`. -/
theorem hex_coercive' : Coercive (0 : ZMod 6) 1 2 3 (1 / 3) (2 / 3) (2 / Real.sqrt 3) := by
  apply coercive_of_nondeg (by positivity)
  have s3 := sqrt3_sq
  have s3p := sqrt3_pos
  have hB : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by rw [div_pow, s3]; norm_num
  intro s h0 h1 h2
  have : s = 2 ∨ s = 3 ∨ s = 4 := by revert s; decide
  rcases this with rfl | rfl | rfl
  · have e : mR (0 : ZMod 6) 1 2 3 (1 / 3) (2 / 3) 2 = ⟨0, 2 / 3 * Real.sqrt 3⟩ := by
      simp only [mR, χ, show ((2 : ZMod 6) * 0).val = 0 from rfl, show ((2 : ZMod 6) * 1).val = 2 from rfl,
        show ((2 : ZMod 6) * 2).val = 4 from rfl, show ((2 : ZMod 6) * 3).val = 0 from rfl,
        pow_zero, ω6_pow_two, ω6_pow_four]
      apply Complex.ext <;> simp <;> ring
    rw [e]; exact le_norm_mk (by positivity) (by rw [hB]; nlinarith)
  · have e : mR (0 : ZMod 6) 1 2 3 (1 / 3) (2 / 3) 3 = ⟨-2, 0⟩ := by
      simp only [mR, χ, show ((3 : ZMod 6) * 0).val = 0 from rfl, show ((3 : ZMod 6) * 1).val = 3 from rfl,
        show ((3 : ZMod 6) * 2).val = 0 from rfl, show ((3 : ZMod 6) * 3).val = 3 from rfl,
        pow_zero, ω6_pow_three]
      apply Complex.ext <;> simp; ring
    rw [e]; exact le_norm_mk (by positivity) (by rw [hB]; nlinarith)
  · have e : mR (0 : ZMod 6) 1 2 3 (1 / 3) (2 / 3) 4 = ⟨0, -(2 / 3 * Real.sqrt 3)⟩ := by
      simp only [mR, χ, show ((4 : ZMod 6) * 0).val = 0 from rfl, show ((4 : ZMod 6) * 1).val = 4 from rfl,
        show ((4 : ZMod 6) * 2).val = 2 from rfl, show ((4 : ZMod 6) * 3).val = 0 from rfl,
        pow_zero, ω6_pow_two, ω6_pow_four]
      apply Complex.ext <;> simp <;> ring
    rw [e]; exact le_norm_mk (by positivity) (by rw [hB]; nlinarith)

namespace Table

variable {T : Table} {g : ℂ → ℝ} {L : ℝ} {iA iB iC iD : ZMod n} {τ μ σ : ℝ}

/-- **Theorem 5.11**: a rational non-degenerate table (`|m(s)| ≥ σ > 0` for all `s ≢ 0, ±1`) can be
stabilised by rotating it, on any terrain with a small enough Lipschitz constant. -/
theorem exists_balanced_of_nondeg (hR : IsRational T n iA iB iC iD τ μ)
    (hm : ∀ s : ZMod n, s ≠ 0 → s ≠ 1 → s ≠ -1 → σ ≤ ‖mR iA iB iC iD τ μ s‖)
    (hg : IsLip g L) (hs : SmallL T L) (hd : OrbitData T L n σ) :
    ∃ θ, ∃ q c, ‖q‖ < 1 ∧ resid g θ q c T.A = 0 ∧ resid g θ q c T.B = 0 ∧
      resid g θ q c T.C = 0 ∧ resid g θ q c T.D = 0 :=
  exists_balanced hR (coercive_of_nondeg hd.hσ.le hm) hg hs hd

end Table

end Wobbly
