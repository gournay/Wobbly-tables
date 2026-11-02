import Wobbly.Wobble
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Lemma 4.1: the coordinates of the feet (§4.1 of the paper)

The rest of the formalisation takes the formulas of Lemma 4.1 as the definition of the model: in the
position `(θ, q, c)`, the foot which is at `a` in the frame of the table is at the horizontal
position `foot (rot θ * a) q` and at the height `c + dot (rot θ * a) q`. This file derives these
formulas from the rigid motion of the paper: the foot is at `S_q (R_θ a, 0) + (0, 0, c)`, where
`S_q ∈ SO(3)` is the rotation around the horizontal axis orthogonal to `q`, by the angle
`arcsin ‖q‖`, in the direction which lifts `q` upwards. Points of `ℝ³` are `pt x z = (x, z)` with
`x ∈ ℂ ≅ ℝ²`.

* `S q`: the matrix of `S_q` (with `c = √(1 - ‖q‖²)` and `f(‖q‖²) = 1/(1 + c)`), `S_zero`;
* `S_mem`: `S_q ∈ SO(3)` for `‖q‖ ≤ 1`;
* `S_axis`, `S_dir`: `S_q` fixes the horizontal vector `(iq, 0)` orthogonal to `q`, and rotates
  `(q, 0)` upwards by the angle `arcsin ‖q‖`; `S_unique`: it is the only rotation with these two
  properties (for `q ≠ 0`);
* `feet_eq`: **Lemma 4.1**; `resid_eq`: the residual `resid` of `Wobble.lean` is the height of the
  foot above the ground;
* `plane_eq`: equation (4.1);
* `exists_S_mul_Rz`, `S_mul_Rz_inj`: every rotation which neither turns the table upside down nor
  makes it vertical is `S_q ∘ R_θ`, with a unique `q` (`‖q‖ < 1`) and a unique `θ` modulo `2π`.
-/

noncomputable section

open Complex Matrix

namespace Wobbly

/-- The point `(x, z)` of `ℝ³ = ℝ² × ℝ`, the horizontal plane being identified with `ℂ`. -/
def pt (x : ℂ) (z : ℝ) : Fin 3 → ℝ := ![x.re, x.im, z]

/-- The rotation `R_θ` around the vertical axis. -/
def Rz (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The rotation `S_q` (see `S_axis`, `S_dir` and `S_unique`). -/
def S (q : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - f (‖q‖ ^ 2) * q.re ^ 2, -(f (‖q‖ ^ 2) * q.re * q.im), -q.re;
     -(f (‖q‖ ^ 2) * q.re * q.im), 1 - f (‖q‖ ^ 2) * q.im ^ 2, -q.im;
     q.re, q.im, Real.sqrt (1 - ‖q‖ ^ 2)]

lemma rot_re (θ : ℝ) : (rot θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

lemma rot_im (θ : ℝ) : (rot θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

lemma Rz_pt (θ : ℝ) (a : ℂ) (z : ℝ) : Rz θ *ᵥ pt a z = pt (rot θ * a) z := by
  ext i
  fin_cases i <;> simp [Rz, pt, Matrix.mulVec, dotProduct, Fin.sum_univ_three, rot_re, rot_im] <;>
    ring

lemma S_zero : S 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]

/-- `S_q (u, 0) = (u - Φ_u(q), u · q)`: the formula of Lemma 4.1 for the image of a horizontal
vector. -/
lemma S_pt (q u : ℂ) : S q *ᵥ pt u 0 = pt (foot u q) (dot u q) := by
  ext i
  fin_cases i <;> simp [S, pt, Matrix.mulVec, dotProduct, Fin.sum_univ_three, foot, Φ, dot] <;> ring

lemma eq_zero_of_sq_add_sq {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  exact ⟨(pow_eq_zero_iff two_ne_zero).1 (by linarith),
    (pow_eq_zero_iff two_ne_zero).1 (by linarith)⟩

lemma eq_zero_of_sq_add_sq_add_sq {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  have hz := sq_nonneg z
  exact ⟨(pow_eq_zero_iff two_ne_zero).1 (by linarith),
    (pow_eq_zero_iff two_ne_zero).1 (by linarith), (pow_eq_zero_iff two_ne_zero).1 (by linarith)⟩

lemma lt_one_of_sq_lt_one {x : ℝ} (hx : 0 ≤ x) (h : x ^ 2 < 1) : x < 1 := by nlinarith

lemma eq_one_of_sq_eq_one {x : ℝ} (hx : 0 ≤ x) (h : x ^ 2 = 1) : x = 1 := by nlinarith

/-- Both forms of the orthogonality of a matrix of `SO(3)`, and its determinant. -/
lemma SO3_iff {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Mᵀ * M = 1 ∧ M * Mᵀ = 1 ∧ M.det = 1 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hM
  exact ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 hM.1,
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).1 hM.1, hM.2⟩

section

variable {q : ℂ}

/-- The relations between `q = a + ib`, `c = √(1 - ‖q‖²)` and `f(‖q‖²) = 1/(1 + c)`. -/
lemma S_rel (hq : ‖q‖ ≤ 1) :
    f (‖q‖ ^ 2) * (1 + Real.sqrt (1 - ‖q‖ ^ 2)) = 1 ∧
    q.re ^ 2 + q.im ^ 2 + Real.sqrt (1 - ‖q‖ ^ 2) ^ 2 = 1 ∧
    f (‖q‖ ^ 2) * (q.re ^ 2 + q.im ^ 2) = 1 - Real.sqrt (1 - ‖q‖ ^ 2) := by
  have hs := sq_norm_eq q
  have h0 : 0 ≤ 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have hc := Real.sq_sqrt h0
  have hF : f (‖q‖ ^ 2) * (1 + Real.sqrt (1 - ‖q‖ ^ 2)) = 1 := by
    rw [f, one_div, inv_mul_cancel₀ (by positivity)]
  refine ⟨hF, by linarith, ?_⟩
  linear_combination (-f (‖q‖ ^ 2)) * hs + f (‖q‖ ^ 2) * hc
    + (1 - Real.sqrt (1 - ‖q‖ ^ 2)) * hF

/-- `S_q ∈ SO(3)`. -/
theorem S_mem (hq : ‖q‖ ≤ 1) : S q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  obtain ⟨hF, h1, h2⟩ := S_rel hq
  set F := f (‖q‖ ^ 2)
  set c := Real.sqrt (1 - ‖q‖ ^ 2)
  set a := q.re
  set b := q.im
  have hE : F ^ 2 * (a ^ 2 + b ^ 2) - 2 * F + 1 = 0 := by linear_combination F * h2 - hF
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
      | linear_combination a ^ 2 * hE
      | linear_combination a * b * hE
      | linear_combination b ^ 2 * hE
      | linear_combination a * h2
      | linear_combination b * h2
      | linear_combination h1
  · rw [Matrix.det_fin_three]
    simp [S]
    linear_combination h1 - c * h2

/-- `S_q` fixes the horizontal vector `(iq, 0)` orthogonal to `q`: it is a rotation around this
horizontal axis. -/
lemma S_axis (q : ℂ) : S q *ᵥ pt (I * q) 0 = pt (I * q) 0 := by
  rw [S_pt]
  have h : dot (I * q) q = 0 := by simp [dot]; ring
  simp [foot, Φ, h]

/-- `S_q` rotates `(q, 0)` upwards by the angle `α = arcsin ‖q‖`, in the vertical plane through
`q`: `(q, 0) ↦ (cos α · q, sin α · ‖q‖)`. -/
lemma S_dir (hq : ‖q‖ ≤ 1) :
    S q *ᵥ pt q 0 = pt (Real.cos (Real.arcsin ‖q‖) * q) (Real.sin (Real.arcsin ‖q‖) * ‖q‖) := by
  obtain ⟨-, -, h2⟩ := S_rel hq
  have hd : dot q q = q.re ^ 2 + q.im ^ 2 := by simp [dot]; ring
  have hfoot : foot q q = ((Real.sqrt (1 - ‖q‖ ^ 2) : ℝ) : ℂ) * q := by
    rw [foot, Φ, hd, h2]; push_cast; ring
  rw [Real.cos_arcsin, Real.sin_arcsin (by linarith [norm_nonneg q]) hq, S_pt, hfoot, hd,
    ← sq_norm_eq]
  congr 1
  ring

/-- `S_q` is the only rotation which fixes `(iq, 0)` and rotates `(q, 0)` upwards by the angle
`arcsin ‖q‖` (for `q ≠ 0`). -/
theorem S_unique (hq : ‖q‖ ≤ 1) (hq0 : q ≠ 0) {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h1 : M *ᵥ pt (I * q) 0 = pt (I * q) 0)
    (h2 : M *ᵥ pt q 0 =
      pt (Real.cos (Real.arcsin ‖q‖) * q) (Real.sin (Real.arcsin ‖q‖) * ‖q‖)) :
    M = S q := by
  obtain ⟨-, hs1, hs2⟩ := S_rel hq
  rw [Real.cos_arcsin, Real.sin_arcsin (by linarith [norm_nonneg q]) hq] at h2
  obtain ⟨hMM, -, hdet⟩ := SO3_iff hM
  have hsn := sq_norm_eq q
  set F := f (‖q‖ ^ 2)
  set c := Real.sqrt (1 - ‖q‖ ^ 2)
  set a := q.re
  set b := q.im
  have hs : 0 < a ^ 2 + b ^ 2 := by
    rw [← hsn]; exact pow_pos (norm_pos_iff.2 hq0) 2
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have a2 := congrFun h1 2
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  have b2 := congrFun h2 2
  simp [pt, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a0 a1 a2 b0 b1 b2
  -- the first two columns
  have m00 : M 0 0 = 1 - F * a ^ 2 := by
    apply mul_left_cancel₀ hs.ne'
    linear_combination (-b) * a0 + a * b0 + a ^ 2 * hs2
  have m01 : M 0 1 = -(F * a * b) := by
    apply mul_left_cancel₀ hs.ne'
    linear_combination a * a0 + b * b0 + a * b * hs2
  have m10 : M 1 0 = -(F * a * b) := by
    apply mul_left_cancel₀ hs.ne'
    linear_combination (-b) * a1 + a * b1 + a * b * hs2
  have m11 : M 1 1 = 1 - F * b ^ 2 := by
    apply mul_left_cancel₀ hs.ne'
    linear_combination a * a1 + b * b1 + b ^ 2 * hs2
  have m20 : M 2 0 = a := by
    apply mul_left_cancel₀ hs.ne'
    linear_combination (-b) * a2 + a * b2 + a * hsn
  have m21 : M 2 1 = b := by
    apply mul_left_cancel₀ hs.ne'
    linear_combination a * a2 + b * b2 + b * hsn
  -- the third column: a unit vector `v` with `v · (-a, -b, c) = det M = 1`
  have hn := congrFun (congrFun hMM 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hn
  rw [Matrix.det_fin_three, m00, m01, m10, m11, m20, m21] at hdet
  have hd : c * M 2 2 - b * M 1 2 - a * M 0 2 = 1 := by
    linear_combination hdet + M 2 2 * hs2
  have hz : (M 0 2 + a) ^ 2 + (M 1 2 + b) ^ 2 + (M 2 2 - c) ^ 2 = 0 := by
    linear_combination hn + hs1 - 2 * hd
  obtain ⟨z0, z1, z2⟩ := eq_zero_of_sq_add_sq_add_sq hz
  have m02 : M 0 2 = -a := by linear_combination z0
  have m12 : M 1 2 = -b := by linear_combination z1
  have m22 : M 2 2 = c := by linear_combination z2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S, m00, m01, m02, m10, m11, m12, m20, m21, m22, F, c, a, b]

end

/-- **Lemma 4.1**: in the position `(θ, q, c)`, the foot which is at `a` in the frame of the table,
i.e. at `S_q (R_θ a, 0) + (0, 0, c)`, is at the horizontal position `x = u - Φ_u(q)` and at the
height `z = c + u · q`, where `u = R_θ a`. -/
theorem feet_eq (θ : ℝ) (q : ℂ) (c : ℝ) (a : ℂ) :
    S q *ᵥ (Rz θ *ᵥ pt a 0) + pt 0 c = pt (foot (rot θ * a) q) (c + dot (rot θ * a) q) := by
  rw [Rz_pt, S_pt]
  ext i
  fin_cases i <;> simp [pt]; ring

/-- The residual `resid g θ q c a` of `Wobble.lean` is the height of the foot above the ground. -/
lemma resid_eq (g : ℂ → ℝ) (θ : ℝ) (q : ℂ) (c : ℝ) (a : ℂ) :
    resid g θ q c a = (S q *ᵥ (Rz θ *ᵥ pt a 0) + pt 0 c) 2
      - g ⟨(S q *ᵥ (Rz θ *ᵥ pt a 0) + pt 0 c) 0, (S q *ᵥ (Rz θ *ᵥ pt a 0) + pt 0 c) 1⟩ := by
  rw [feet_eq]
  simp [pt, resid]

/-- Equation (4.1): the heights of the feet satisfy `τ z_A + (1-τ) z_C = μ z_B + (1-μ) z_D`, since
`τ a_A + (1-τ) a_C = μ a_B + (1-μ) a_D`. -/
theorem plane_eq {A B C D : ℂ} {τ μ : ℝ}
    (hX : (τ : ℂ) * A + ((1 - τ : ℝ) : ℂ) * C = (μ : ℂ) * B + ((1 - μ : ℝ) : ℂ) * D)
    (θ : ℝ) (q : ℂ) (c : ℝ) :
    τ * (c + dot (rot θ * A) q) + (1 - τ) * (c + dot (rot θ * C) q) =
      μ * (c + dot (rot θ * B) q) + (1 - μ) * (c + dot (rot θ * D) q) := by
  have h := congrArg (fun z => dot (rot θ * z) q) hX
  simp only [mul_add, dot_add_left, mul_left_comm (rot θ), dot_real_mul_left] at h
  linear_combination h

/-! ### The decomposition `T = S_q ∘ R_θ` -/

lemma Rz_mem (θ : ℝ) : Rz θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination Real.sin_sq_add_cos_sq θ
  · rw [Matrix.det_fin_three]; simp [Rz]; linear_combination Real.sin_sq_add_cos_sq θ

/-- Every rotation `T ∈ SO(3)` which neither turns the table upside down nor makes it vertical
(the image of the vertical vector points upwards) is `S_q ∘ R_θ` with `‖q‖ < 1`. -/
theorem exists_S_mul_Rz {T : Matrix (Fin 3) (Fin 3) ℝ}
    (hT : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : 0 < T 2 2) :
    ∃ (q : ℂ) (θ : ℝ), ‖q‖ < 1 ∧ T = S q * Rz θ := by
  obtain ⟨hTT, -, hTdet⟩ := SO3_iff hT
  have hcol0 := congrFun (congrFun hTT 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hcol0
  have hcol : T 0 2 ^ 2 + T 1 2 ^ 2 + T 2 2 ^ 2 = 1 := by linear_combination hcol0
  -- `q` is determined by the image of the vertical vector
  set q : ℂ := ⟨-T 0 2, -T 1 2⟩ with hqdef
  have hq2 : ‖q‖ ^ 2 = T 0 2 ^ 2 + T 1 2 ^ 2 := by rw [sq_norm_eq]; simp [q]
  have hq1 : ‖q‖ < 1 := by
    have h22 := pow_pos h 2
    exact lt_one_of_sq_lt_one (norm_nonneg q) (by rw [hq2]; linarith)
  have hc : Real.sqrt (1 - ‖q‖ ^ 2) = T 2 2 := by
    rw [hq2, show 1 - (T 0 2 ^ 2 + T 1 2 ^ 2) = T 2 2 ^ 2 by linarith, Real.sqrt_sq h.le]
  obtain ⟨hSS, hSS', hSdet⟩ := SO3_iff (S_mem hq1.le)
  have hS2 : ∀ k, S q k 2 = T k 2 := fun k => by fin_cases k <;> simp [S, q, hc]
  -- `N = S_qᵀ T` is a rotation which fixes the vertical vector
  set N := (S q)ᵀ * T with hN
  have hNN : Nᵀ * N = 1 := by
    rw [hN, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (S q), hSS', Matrix.one_mul, hTT]
  have hNdet : N.det = 1 := by rw [hN, Matrix.det_mul, Matrix.det_transpose, hSdet, hTdet, one_mul]
  have hN2 : ∀ i, N i 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 := fun i => by
    rw [← hSS]
    simp only [hN, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hS2 k]
  have n02 : N 0 2 = 0 := by simpa using hN2 0
  have n12 : N 1 2 = 0 := by simpa using hN2 1
  have n22 : N 2 2 = 1 := by simpa using hN2 2
  have hrow : ∀ j, N 2 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j := fun j => by
    have := congrFun (congrFun hNN 2) j
    simp [Matrix.mul_apply, Fin.sum_univ_three, n02, n12, n22] at this
    exact this
  have n20 : N 2 0 = 0 := by simpa using hrow 0
  have n21 : N 2 1 = 0 := by simpa using hrow 1
  -- the horizontal block is a rotation of the plane
  have o00 := congrFun (congrFun hNN 0) 0
  have o01 := congrFun (congrFun hNN 0) 1
  have o11 := congrFun (congrFun hNN 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, n20, n21] at o00 o01 o11
  rw [Matrix.det_fin_three, n02, n12, n20, n21, n22] at hNdet
  have hz : (N 1 1 - N 0 0) ^ 2 + (N 0 1 + N 1 0) ^ 2 = 0 := by
    linear_combination o11 + o00 - 2 * hNdet
  obtain ⟨z1, z2⟩ := eq_zero_of_sq_add_sq hz
  have n11 : N 1 1 = N 0 0 := by linear_combination z1
  have n01 : N 0 1 = -N 1 0 := by linear_combination z2
  set w : ℂ := ⟨N 0 0, N 1 0⟩
  have hw : ‖w‖ = 1 := by
    refine eq_one_of_sq_eq_one (norm_nonneg w) ?_
    rw [sq_norm_eq]; simp only [w]; linear_combination o00
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; exact zero_ne_one hw
  refine ⟨q, Complex.arg w, hq1, ?_⟩
  have hcos : Real.cos (Complex.arg w) = N 0 0 := by rw [Complex.cos_arg hw0, hw]; simp [w]
  have hsin : Real.sin (Complex.arg w) = N 1 0 := by rw [Complex.sin_arg, hw]; simp [w]
  have hNR : N = Rz (Complex.arg w) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz, hcos, hsin, n02, n12, n22, n20, n21, n11, n01]
  calc T = (S q * (S q)ᵀ) * T := by rw [hSS', Matrix.one_mul]
    _ = S q * N := by rw [Matrix.mul_assoc]
    _ = S q * Rz (Complex.arg w) := by rw [hNR]

/-- Uniqueness in the decomposition: `q` is unique and `θ` is unique modulo `2π`. -/
theorem S_mul_Rz_inj {q q' : ℂ} {θ θ' : ℝ} (hq : ‖q‖ ≤ 1) (h : S q * Rz θ = S q' * Rz θ') :
    q = q' ∧ rot θ = rot θ' := by
  have h2 : ∀ i, S q i 2 = S q' i 2 := fun i => by
    have := congrFun (congrFun h i) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Rz] using this
  have hqq : q = q' := by
    have e0 := h2 0
    have e1 := h2 1
    simp [S] at e0 e1
    exact Complex.ext e0 e1
  subst hqq
  obtain ⟨hS, -, -⟩ := SO3_iff (S_mem hq)
  have hR : Rz θ = Rz θ' := by
    calc Rz θ = (S q)ᵀ * S q * Rz θ := by rw [hS, Matrix.one_mul]
      _ = (S q)ᵀ * (S q * Rz θ') := by rw [Matrix.mul_assoc, h]
      _ = Rz θ' := by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have hc := congrFun (congrFun hR 0) 0
  have hs := congrFun (congrFun hR 1) 0
  simp [Rz] at hc hs
  refine ⟨rfl, Complex.ext ?_ ?_⟩
  · rw [rot_re, rot_re, hc]
  · rw [rot_im, rot_im, hs]

/-- Conversely, `S_q ∘ R_θ` is a rotation which neither turns the table upside down nor makes it
vertical, for `‖q‖ < 1`. -/
lemma S_mul_Rz_mem {q : ℂ} (hq : ‖q‖ < 1) (θ : ℝ) :
    S q * Rz θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ 0 < (S q * Rz θ) 2 2 := by
  refine ⟨Submonoid.mul_mem _ (S_mem hq.le) (Rz_mem θ), ?_⟩
  have e : (S q * Rz θ) 2 2 = Real.sqrt (1 - ‖q‖ ^ 2) := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, S, Rz]
  rw [e, Real.sqrt_pos]
  nlinarith [norm_nonneg q]

end Wobbly
