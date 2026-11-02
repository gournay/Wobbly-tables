import Wobbly.Wobble
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.ZMod.Basic

/-!
# The orbit argument (Theorem 5.11 of the paper)

A *rational* table has its feet at vertices of a regular `n`-gon of radius `r`:
`A = r ω^{iA}`, `B = r ω^{iB}`, `C = r ω^{iC}`, `D = r ω^{iD}` with `ω = exp (2πi/n)`.
For such a table and a fixed `θ`, we compare the `n` rotated tables `θ + 2πj/n` with one common
tilt `q̄` (the least-squares fit of the heights of the ground under the vertices), and show that
the orbit sum of the wobbling function is small compared to its maximum. The non-degeneracy of the
table enters through the coercivity of the circulant operator `C` (`Coercive`), which follows from
`m(s) ≠ 0` for `s ≢ 0, ±1` by a discrete Fourier argument; here it is an explicit hypothesis, and
it is checked for the hexagonal table in `Wobbly.Hexagon`.
-/

noncomputable section

open Complex Metric Finset ComplexConjugate

namespace Wobbly

/-! ## Roots of unity -/

/-- `ω n = exp (2πi/n)`. -/
def ω (n : ℕ) : ℂ := rot (2 * Real.pi / n)

lemma ω_eq (n : ℕ) : ω n = Complex.exp (2 * Real.pi * I / n) := by
  unfold ω rot; congr 1; push_cast; ring

lemma ω_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (ω n) n := by
  rw [ω_eq]; exact Complex.isPrimitiveRoot_exp n hn

lemma ω_pow_n {n : ℕ} (hn : n ≠ 0) : ω n ^ n = 1 := (ω_isPrimitiveRoot hn).pow_eq_one

lemma ω_pow_mod {n : ℕ} (hn : n ≠ 0) (k : ℕ) : ω n ^ (k % n) = ω n ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, ω_pow_n hn, one_pow, mul_one]

lemma norm_ω_pow (n k : ℕ) : ‖ω n ^ k‖ = 1 := by
  rw [norm_pow, ω, norm_rot, one_pow]

/-- `rot (2π k / n) = ω^k`. -/
lemma rot_two_pi_mul (n k : ℕ) : rot (2 * Real.pi * k / n) = ω n ^ k := by
  unfold ω rot
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  unfold rot; rw [← Complex.exp_add]; congr 1; push_cast; ring

variable {n : ℕ} [NeZero n]

lemma sum_zmod_pow (z : ℂ) : ∑ i : ZMod n, z ^ i.val = ∑ i ∈ range n, z ^ i := by
  refine Finset.sum_bij (fun i _ => i.val) (fun i _ => Finset.mem_range.2 (ZMod.val_lt i))
    (fun a _ b _ h => ZMod.val_injective n h) (fun k hk => ⟨(k : ZMod n), Finset.mem_univ _, ?_⟩)
    (fun i _ => rfl)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hk)]

lemma sum_ω_pow (hn : 2 ≤ n) : ∑ i : ZMod n, ω n ^ i.val = 0 := by
  rw [sum_zmod_pow]
  exact (ω_isPrimitiveRoot (NeZero.ne n)).geom_sum_eq_zero (by omega)

lemma sum_ω_pow_sq (hn : 3 ≤ n) : ∑ i : ZMod n, (ω n ^ i.val) ^ 2 = 0 := by
  have hprim := ω_isPrimitiveRoot (NeZero.ne n)
  have h1 : ω n ^ 2 ≠ 1 := by
    intro h
    have := (hprim.pow_eq_one_iff_dvd 2).1 h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have e : ∀ i : ZMod n, (ω n ^ i.val) ^ 2 = (ω n ^ 2) ^ i.val := fun i => by ring
  simp only [e]
  have hpow : (ω n ^ 2) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ω_pow_n (NeZero.ne n), one_pow]
  rw [sum_zmod_pow, geom_sum_eq h1, hpow, sub_self, zero_div]

lemma ω_pow_val_add (a b : ZMod n) : ω n ^ (a + b).val = ω n ^ a.val * ω n ^ b.val := by
  rw [ZMod.val_add, ω_pow_mod (NeZero.ne n), pow_add]

/-! ## The dot product and complex numbers -/

lemma dot_eq_complex (u v : ℂ) : (dot u v : ℂ) = (conj u * v + u * conj v) / 2 := by
  apply Complex.ext <;> simp [dot, mul_re, mul_im, conj_re, conj_im]; ring

lemma dot_sum_left {ι : Type*} (s : Finset ι) (u : ι → ℂ) (v : ℂ) :
    dot (∑ i ∈ s, u i) v = ∑ i ∈ s, dot (u i) v := by
  simp only [dot, Complex.re_sum, Complex.im_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

/-! ## Vertices of the rotated `n`-gon -/

/-- The vertex `i` of the regular `n`-gon of radius `r`, rotated by `θ`. -/
def vtx (n : ℕ) (r θ : ℝ) (i : ZMod n) : ℂ := (r : ℂ) * rot θ * ω n ^ i.val

omit [NeZero n] in
lemma norm_vtx {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (i : ZMod n) : ‖vtx n r θ i‖ = r := by
  rw [vtx, Complex.norm_mul, Complex.norm_mul, norm_rot, norm_ω_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr]; ring

lemma sum_vtx (hn : 2 ≤ n) (r θ : ℝ) : ∑ i : ZMod n, vtx n r θ i = 0 := by
  simp only [vtx, ← Finset.mul_sum, sum_ω_pow hn, mul_zero]

lemma sum_vtx_sq (hn : 3 ≤ n) (r θ : ℝ) : ∑ i : ZMod n, vtx n r θ i ^ 2 = 0 := by
  have e : ∀ i : ZMod n, vtx n r θ i ^ 2 = ((r : ℂ) * rot θ) ^ 2 * (ω n ^ i.val) ^ 2 :=
    fun i => by rw [vtx]; ring
  simp only [e, ← Finset.mul_sum, sum_ω_pow_sq hn, mul_zero]

/-- `Σ_i (v_i · q) v_i = (n r² / 2) q`. -/
lemma sum_dot_vtx_mul (hn : 3 ≤ n) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (q : ℂ) :
    ∑ i : ZMod n, (dot (vtx n r θ i) q : ℂ) * vtx n r θ i = ((n * r ^ 2 / 2 : ℝ) : ℂ) * q := by
  have hnorm : ∀ i : ZMod n, conj (vtx n r θ i) * vtx n r θ i = (r ^ 2 : ℝ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_vtx hr]
  have e : ∀ i : ZMod n, (dot (vtx n r θ i) q : ℂ) * vtx n r θ i =
      ((r ^ 2 / 2 : ℝ) : ℂ) * q + vtx n r θ i ^ 2 * conj q / 2 := by
    intro i
    rw [dot_eq_complex]
    have := hnorm i
    push_cast at this ⊢
    linear_combination (q / 2) * this
  have hsum : ∑ i : ZMod n, (dot (vtx n r θ i) q : ℂ) * vtx n r θ i =
      ∑ i : ZMod n, (((r ^ 2 / 2 : ℝ) : ℂ) * q + vtx n r θ i ^ 2 * (conj q / 2)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e i]; ring
  rw [hsum, Finset.sum_add_distrib]
  have h2 : ∑ x : ZMod n, vtx n r θ x ^ 2 * (conj q / 2) = 0 := by
    rw [← Finset.sum_mul, sum_vtx_sq hn, zero_mul]
  rw [h2, add_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  push_cast; ring

/-! ## Rational tables -/

/-- A rational table: the feet are vertices `iA, iB, iC, iD` of the regular `n`-gon of radius
`T.r`, and `X = τ A + (1 - τ) C = μ B + (1 - μ) D` is the intersection of the diagonals. -/
structure IsRational (T : Table) (n : ℕ) [NeZero n] (iA iB iC iD : ZMod n) (τ μ : ℝ) : Prop where
  hn : 3 ≤ n
  hA : T.A = (T.r : ℂ) * ω n ^ iA.val
  hB : T.B = (T.r : ℂ) * ω n ^ iB.val
  hC : T.C = (T.r : ℂ) * ω n ^ iC.val
  hD : T.D = (T.r : ℂ) * ω n ^ iD.val
  hX : (τ : ℂ) * T.A + (1 - τ : ℝ) * T.C = (μ : ℂ) * T.B + (1 - μ : ℝ) * T.D
  hτ0 : 0 ≤ τ
  hτ1 : τ ≤ 1
  hμ0 : 0 ≤ μ
  hμ1 : μ ≤ 1

/-- The angle of the `j`-th rotated table of the orbit of `θ`. -/
def θj (n : ℕ) (θ : ℝ) (j : ZMod n) : ℝ := θ + 2 * Real.pi * j.val / n

lemma rot_θj_mul (θ : ℝ) (r : ℝ) (i j : ZMod n) :
    rot (θj n θ j) * ((r : ℂ) * ω n ^ i.val) = vtx n r θ (i + j) := by
  rw [θj, rot_add, rot_two_pi_mul, vtx, ω_pow_val_add]
  ring

/-- The circulant operator `(C N)_j = τ N_{iA+j} - μ N_{iB+j} + (1-τ) N_{iC+j} - (1-μ) N_{iD+j}`. -/
def circ (iA iB iC iD : ZMod n) (τ μ : ℝ) (N : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  τ * N (iA + j) - μ * N (iB + j) + (1 - τ) * N (iC + j) - (1 - μ) * N (iD + j)

/-- Coercivity of the circulant operator on the vectors which are orthogonal to the affine
functions on the `n`-gon (this is where the non-degeneracy `m(s) ≠ 0` for `s ≢ 0, ±1` enters,
with `σ = min |m(s)|`). -/
def Coercive (iA iB iC iD : ZMod n) (τ μ σ : ℝ) : Prop :=
  ∀ N : ZMod n → ℝ, ∑ i, N i = 0 → ∑ i, (N i : ℂ) * ω n ^ i.val = 0 →
    σ ^ 2 * ∑ i, N i ^ 2 ≤ ∑ j, circ iA iB iC iD τ μ N j ^ 2

lemma sum_shift (a : ZMod n) (F : ZMod n → ℝ) : ∑ j, F (a + j) = ∑ i, F i :=
  Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)

lemma sum_circ (iA iB iC iD : ZMod n) (τ μ : ℝ) (N : ZMod n → ℝ) :
    ∑ j, circ iA iB iC iD τ μ N j = 0 := by
  simp only [circ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_shift]
  ring

/-! ## The orbit estimate

The proof of Theorem 5.11 is split into the steps of the paper:
1. the least-squares map `lsq` and its fixed point `qbar` (the common tilt);
2. the non-affine part `N` of the heights for the common tilt, and the identity
   `w_j = (C N)_j + e_j` with `|e_j| ≤ η ‖q_j - qbar‖`;
3. the bound `‖q_j - qbar‖ ≤ 2K ‖N‖_∞ / (d_min (1 - λ'))`;
4. the orbit sum. -/

lemma foot_zero (q : ℂ) : foot 0 q = 0 := by
  simp [foot, Φ, dot]

lemma norm_foot_le {u q : ℂ} (hq : ‖q‖ ≤ 1) : ‖foot u q‖ ≤ ‖u‖ := by
  have := norm_foot_sub_foot_le (u := u) (v := 0) hq
  rwa [foot_zero, sub_zero, sub_zero] at this

namespace Table

variable {T : Table} {g : ℂ → ℝ} {L : ℝ}

lemma sqrt_two_le_K (T : Table) : Real.sqrt 2 ≤ T.K := by
  unfold K
  apply Real.sqrt_le_sqrt
  have h0 : 0 ≤ T.γ := abs_nonneg _
  have h1 := T.γ_lt_one
  rw [le_div_iff₀ (by linarith)]
  nlinarith

variable {n : ℕ} [NeZero n] {iA iB iC iD : ZMod n} {τ μ σ : ℝ}

/-- The heights of the ground under the vertices of the rotated `n`-gon, for the tilt `q`. -/
def heights (T : Table) (g : ℂ → ℝ) (n : ℕ) (θ : ℝ) (q : ℂ) (i : ZMod n) : ℝ :=
  g (foot (vtx n T.r θ i) q)

/-- The gradient of the least-squares affine fit of the heights (Step 1 of the proof). -/
def lsq (T : Table) (g : ℂ → ℝ) (n : ℕ) [NeZero n] (θ : ℝ) (q : ℂ) : ℂ :=
  ((2 / (n * T.r ^ 2) : ℝ) : ℂ) * ∑ i, (heights T g n θ q i : ℂ) * vtx n T.r θ i


lemma foot_sub_foot_same (v q q' : ℂ) : foot v q - foot v q' = -(Φ v q - Φ v q') := by
  unfold foot; ring

omit [NeZero n] in
lemma abs_heights_sub_le (hr : 0 < T.r) (hg : IsLip g L) (θ : ℝ) {q q' : ℂ} {t : ℝ}
    (hq : ‖q‖ ≤ t) (hq' : ‖q'‖ ≤ t) (ht : t < 1) (i : ZMod n) :
    |heights T g n θ q i - heights T g n θ q' i| ≤ L * (T.r * ψ t * ‖q - q'‖) := by
  unfold heights
  calc _ ≤ L * ‖foot (vtx n T.r θ i) q - foot (vtx n T.r θ i) q'‖ := hg _ _
    _ = L * ‖Φ (vtx n T.r θ i) q - Φ (vtx n T.r θ i) q'‖ := by
        rw [foot_sub_foot_same, norm_neg]
    _ ≤ L * (T.r * ψ t * ‖q - q'‖) :=
        mul_le_mul_of_nonneg_left (norm_Φ_sub_le (norm_vtx hr.le θ i).le hq hq' ht) hg.nonneg

lemma card_zmod_real : ((Fintype.card (ZMod n) : ℕ) : ℝ) = n := by
  rw [ZMod.card]

lemma norm_lsq_le (hn : 2 ≤ n) (hr : 0 < T.r) (hg : IsLip g L) (θ : ℝ) {q : ℂ} (hq : ‖q‖ ≤ 1) :
    ‖lsq T g n θ q‖ ≤ 2 * L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsum0 : ∑ i : ZMod n, ((g 0 : ℝ) : ℂ) * vtx n T.r θ i = 0 := by
    rw [← Finset.mul_sum, sum_vtx hn, mul_zero]
  have e : ∑ i, (heights T g n θ q i : ℂ) * vtx n T.r θ i =
      ∑ i, ((heights T g n θ q i - g 0 : ℝ) : ℂ) * vtx n T.r θ i := by
    have h : ∑ i, ((heights T g n θ q i - g 0 : ℝ) : ℂ) * vtx n T.r θ i =
        ∑ i, (heights T g n θ q i : ℂ) * vtx n T.r θ i -
          ∑ i : ZMod n, ((g 0 : ℝ) : ℂ) * vtx n T.r θ i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [h, hsum0, sub_zero]
  have hterm : ∀ i : ZMod n,
      ‖((heights T g n θ q i - g 0 : ℝ) : ℂ) * vtx n T.r θ i‖ ≤ L * T.r * T.r := by
    intro i
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_vtx hr.le]
    gcongr
    calc |heights T g n θ q i - g 0| ≤ L * ‖foot (vtx n T.r θ i) q - 0‖ := hg _ _
      _ ≤ L * T.r := by
          gcongr
          · exact hg.nonneg
          · rw [sub_zero]
            exact (norm_foot_le hq).trans (norm_vtx hr.le θ i).le
  unfold lsq
  rw [e, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / (n * T.r ^ 2))]
  calc 2 / (n * T.r ^ 2) * ‖∑ i, ((heights T g n θ q i - g 0 : ℝ) : ℂ) * vtx n T.r θ i‖
      ≤ 2 / (n * T.r ^ 2) * ∑ _i : ZMod n, L * T.r * T.r := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = 2 * L := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_zmod_real]
        field_simp

lemma norm_lsq_sub_le (hr : 0 < T.r) (hg : IsLip g L) (θ : ℝ) {q q' : ℂ} {t : ℝ}
    (hq : ‖q‖ ≤ t) (hq' : ‖q'‖ ≤ t) (ht : t < 1) :
    ‖lsq T g n θ q - lsq T g n θ q'‖ ≤ 2 * L * ψ t * ‖q - q'‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have e : lsq T g n θ q - lsq T g n θ q' = ((2 / (n * T.r ^ 2) : ℝ) : ℂ) *
      ∑ i, ((heights T g n θ q i - heights T g n θ q' i : ℝ) : ℂ) * vtx n T.r θ i := by
    unfold lsq
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hterm : ∀ i : ZMod n,
      ‖((heights T g n θ q i - heights T g n θ q' i : ℝ) : ℂ) * vtx n T.r θ i‖ ≤
        L * (T.r * ψ t * ‖q - q'‖) * T.r := by
    intro i
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_vtx hr.le]
    gcongr
    exact abs_heights_sub_le hr hg θ hq hq' ht i
  rw [e, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / (n * T.r ^ 2))]
  calc 2 / (n * T.r ^ 2) *
        ‖∑ i, ((heights T g n θ q i - heights T g n θ q' i : ℝ) : ℂ) * vtx n T.r θ i‖
      ≤ 2 / (n * T.r ^ 2) * ∑ _i : ZMod n, L * (T.r * ψ t * ‖q - q'‖) * T.r := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = 2 * L * ψ t * ‖q - q'‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_zmod_real]
        field_simp

/-- Step 1: existence of the common tilt. -/
lemma exists_qbar (hn : 2 ≤ n) (hr : 0 < T.r) (hg : IsLip g L) (θ : ℝ) {t : ℝ} (ht : t < 1)
    (h2L : 2 * L ≤ t) (hP : 2 * L * ψ t < 1) :
    ∃ qbar : ℂ, ‖qbar‖ ≤ t ∧ lsq T g n θ qbar = qbar := by
  have hL := hg.nonneg
  have ht0 : 0 ≤ t := by linarith
  have hmaps : Set.MapsTo (lsq T g n θ) (closedBall (0 : ℂ) t) (closedBall (0 : ℂ) t) := by
    intro q hq
    rw [mem_closedBall, dist_zero_right] at hq ⊢
    exact (norm_lsq_le hn hr hg θ (hq.trans ht.le)).trans h2L
  have hcomplete : IsComplete (closedBall (0 : ℂ) t) := isClosed_closedBall.isComplete
  have hK0 : 0 ≤ 2 * L * ψ t := by have := ψ_nonneg ht0; positivity
  have hcontr : ContractingWith ⟨2 * L * ψ t, hK0⟩ (hmaps.restrict (lsq T g n θ) _ _) := by
    refine ⟨by exact_mod_cast hP, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, Set.MapsTo.val_restrict_apply, dist_eq_norm]
    have hx := x.2
    have hy := y.2
    rw [mem_closedBall, dist_zero_right] at hx hy
    exact norm_lsq_sub_le hr hg θ hx hy ht
  obtain ⟨q, hq, hfix, -⟩ := hcontr.exists_fixedPoint' hcomplete hmaps
    (mem_closedBall_self ht0) (edist_ne_top _ _)
  rw [mem_closedBall, dist_zero_right] at hq
  exact ⟨q, hq, hfix⟩

/-- The non-affine part of the heights for the tilt `qbar`. -/
def nonAffine (T : Table) (g : ℂ → ℝ) (n : ℕ) [NeZero n] (θ : ℝ) (qbar : ℂ) (i : ZMod n) : ℝ :=
  heights T g n θ qbar i - (∑ k, heights T g n θ qbar k) / n - dot (vtx n T.r θ i) qbar

lemma sum_nonAffine (hn : 3 ≤ n) (θ : ℝ) (qbar : ℂ) :
    ∑ i, nonAffine T g n θ qbar i = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  unfold nonAffine
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_zmod_real, ← dot_sum_left, sum_vtx (by omega), mul_div_cancel₀ _ hn0]
  simp [dot]

lemma sum_nonAffine_mul_vtx (hn : 3 ≤ n) (hr : 0 < T.r) (θ : ℝ) {qbar : ℂ}
    (hfix : lsq T g n θ qbar = qbar) :
    ∑ i, (nonAffine T g n θ qbar i : ℂ) * vtx n T.r θ i = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hS : ∑ i, (heights T g n θ qbar i : ℂ) * vtx n T.r θ i =
      ((n * T.r ^ 2 / 2 : ℝ) : ℂ) * qbar := by
    conv_rhs => rw [← hfix]
    unfold lsq
    rw [← mul_assoc, ← ofReal_mul]
    have h1 : n * T.r ^ 2 / 2 * (2 / (n * T.r ^ 2)) = 1 := by field_simp
    rw [h1, ofReal_one, one_mul]
  have hsplit : ∀ i : ZMod n, (nonAffine T g n θ qbar i : ℂ) * vtx n T.r θ i =
      (heights T g n θ qbar i : ℂ) * vtx n T.r θ i
        - (((∑ k, heights T g n θ qbar k) / n : ℝ) : ℂ) * vtx n T.r θ i
        - (dot (vtx n T.r θ i) qbar : ℂ) * vtx n T.r θ i := by
    intro i; unfold nonAffine; push_cast; ring
  simp only [hsplit, Finset.sum_sub_distrib]
  rw [hS, ← Finset.mul_sum, sum_vtx (by omega), mul_zero, sub_zero,
    sum_dot_vtx_mul hn hr.le, sub_self]

lemma sum_nonAffine_mul_ω (hn : 3 ≤ n) (hr : 0 < T.r) (θ : ℝ) {qbar : ℂ}
    (hfix : lsq T g n θ qbar = qbar) :
    ∑ i, (nonAffine T g n θ qbar i : ℂ) * ω n ^ i.val = 0 := by
  have h := sum_nonAffine_mul_vtx hn hr θ hfix
  have hr0 : (T.r : ℂ) * rot θ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hr.ne') ?_
    rw [← norm_ne_zero_iff, norm_rot]; norm_num
  have e : ∑ i, (nonAffine T g n θ qbar i : ℂ) * vtx n T.r θ i =
      ((T.r : ℂ) * rot θ) * ∑ i, (nonAffine T g n θ qbar i : ℂ) * ω n ^ i.val := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vtx]; ring
  rw [e] at h
  exact (mul_eq_zero.1 h).resolve_left hr0

/-- The idealised heights `c̄ + v · q̄ + N` of the common tilt. -/
lemma heights_eq (θ : ℝ) (qbar : ℂ) (i : ZMod n) :
    heights T g n θ qbar i = (∑ k, heights T g n θ qbar k) / n + dot (vtx n T.r θ i) qbar +
      nonAffine T g n θ qbar i := by
  unfold nonAffine; ring

/-- The feet of the rotated tables of the orbit are vertices of the `n`-gon. -/
lemma rot_feet (hR : IsRational T n iA iB iC iD τ μ) (θ : ℝ) (j : ZMod n) :
    rot (θj n θ j) * T.A = vtx n T.r θ (iA + j) ∧ rot (θj n θ j) * T.B = vtx n T.r θ (iB + j) ∧
    rot (θj n θ j) * T.C = vtx n T.r θ (iC + j) ∧ rot (θj n θ j) * T.D = vtx n T.r θ (iD + j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hR.hA]; exact rot_θj_mul θ T.r iA j
  · rw [hR.hB]; exact rot_θj_mul θ T.r iB j
  · rw [hR.hC]; exact rot_θj_mul θ T.r iC j
  · rw [hR.hD]; exact rot_θj_mul θ T.r iD j

/-- The combination of the vertices of a rotated table which defines `X` vanishes. -/
lemma dot_comb_zero (hR : IsRational T n iA iB iC iD τ μ) (θ : ℝ) (j : ZMod n) (q : ℂ) :
    τ * dot (vtx n T.r θ (iA + j)) q - μ * dot (vtx n T.r θ (iB + j)) q
      + (1 - τ) * dot (vtx n T.r θ (iC + j)) q - (1 - μ) * dot (vtx n T.r θ (iD + j)) q = 0 := by
  obtain ⟨hA, hB, hC, hD⟩ := rot_feet hR θ j
  rw [← hA, ← hB, ← hC, ← hD]
  have e1 : dot (rot (θj n θ j) * ((τ : ℂ) * T.A + ((1 - τ : ℝ) : ℂ) * T.C)) q =
      τ * dot (rot (θj n θ j) * T.A) q + (1 - τ) * dot (rot (θj n θ j) * T.C) q := by
    rw [mul_add, show rot (θj n θ j) * ((τ : ℂ) * T.A) = (τ : ℂ) * (rot (θj n θ j) * T.A) by ring,
      show rot (θj n θ j) * (((1 - τ : ℝ) : ℂ) * T.C) =
        ((1 - τ : ℝ) : ℂ) * (rot (θj n θ j) * T.C) by ring,
      dot_add_left, dot_real_mul_left, dot_real_mul_left]
  have e2 : dot (rot (θj n θ j) * ((μ : ℂ) * T.B + ((1 - μ : ℝ) : ℂ) * T.D)) q =
      μ * dot (rot (θj n θ j) * T.B) q + (1 - μ) * dot (rot (θj n θ j) * T.D) q := by
    rw [mul_add, show rot (θj n θ j) * ((μ : ℂ) * T.B) = (μ : ℂ) * (rot (θj n θ j) * T.B) by ring,
      show rot (θj n θ j) * (((1 - μ : ℝ) : ℂ) * T.D) =
        ((1 - μ : ℝ) : ℂ) * (rot (θj n θ j) * T.D) by ring,
      dot_add_left, dot_real_mul_left, dot_real_mul_left]
  have e3 := hR.hX
  have : dot (rot (θj n θ j) * ((τ : ℂ) * T.A + ((1 - τ : ℝ) : ℂ) * T.C)) q =
      dot (rot (θj n θ j) * ((μ : ℂ) * T.B + ((1 - μ : ℝ) : ℂ) * T.D)) q := by rw [e3]
  rw [e1, e2] at this
  linarith

/-- Step 2: `w_j = (C N)_j + e_j` with `|e_j| ≤ η ‖q_j - qbar‖`. -/
lemma wob_sub_circ_le (hR : IsRational T n iA iB iC iD τ μ) (hg : IsLip g L) (hs : SmallL T L)
    (θ : ℝ) {qbar : ℂ} {t : ℝ} (ht : t < 1) (hLK : L * T.K ≤ t) (hq : ‖qbar‖ ≤ t) (j : ZMod n) :
    |wob T g L (θj n θ j) - circ iA iB iC iD τ μ (nonAffine T g n θ qbar) j| ≤
      2 * L * T.r * ψ t * ‖tilt T g L (θj n θ j) - qbar‖ := by
  have hr : 0 ≤ T.r := T.r_nonneg
  set q := tilt T g L (θj n θ j) with hqdef
  have hqt : ‖q‖ ≤ t := (norm_tilt_le hg hs _).trans hLK
  obtain ⟨hA, hB, hC, hD⟩ := rot_feet hR θ j
  -- the error for each foot
  set δ := L * (T.r * ψ t * ‖q - qbar‖) with hδ
  have herr : ∀ i : ZMod n, |g (foot (vtx n T.r θ i) q) - heights T g n θ qbar i| ≤ δ := by
    intro i
    unfold heights
    calc _ ≤ L * ‖foot (vtx n T.r θ i) q - foot (vtx n T.r θ i) qbar‖ := hg _ _
      _ = L * ‖Φ (vtx n T.r θ i) q - Φ (vtx n T.r θ i) qbar‖ := by
          rw [foot_sub_foot_same, norm_neg]
      _ ≤ δ := by
          rw [hδ]
          exact mul_le_mul_of_nonneg_left (norm_Φ_sub_le (norm_vtx hr θ i).le hqt hq ht) hg.nonneg
  have hw := wob_eq hg hs (θj n θ j) hR.hX
  rw [hA, hB, hC, hD] at hw
  have hcomb := dot_comb_zero hR θ j qbar
  have eA := heights_eq (T := T) (g := g) θ qbar (iA + j)
  have eB := heights_eq (T := T) (g := g) θ qbar (iB + j)
  have eC := heights_eq (T := T) (g := g) θ qbar (iC + j)
  have eD := heights_eq (T := T) (g := g) θ qbar (iD + j)
  -- `w_j - (C N)_j` is a combination of the errors
  have key : wob T g L (θj n θ j) - circ iA iB iC iD τ μ (nonAffine T g n θ qbar) j =
      τ * (g (foot (vtx n T.r θ (iA + j)) q) - heights T g n θ qbar (iA + j))
      - μ * (g (foot (vtx n T.r θ (iB + j)) q) - heights T g n θ qbar (iB + j))
      + (1 - τ) * (g (foot (vtx n T.r θ (iC + j)) q) - heights T g n θ qbar (iC + j))
      - (1 - μ) * (g (foot (vtx n T.r θ (iD + j)) q) - heights T g n θ qbar (iD + j)) := by
    rw [hw]
    unfold circ
    linear_combination τ * eA - μ * eB + (1 - τ) * eC - (1 - μ) * eD + hcomb
  rw [key]
  have h1 := abs_le.1 (herr (iA + j))
  have h2 := abs_le.1 (herr (iB + j))
  have h3 := abs_le.1 (herr (iC + j))
  have h4 := abs_le.1 (herr (iD + j))
  have hτ0 := hR.hτ0
  have hτ1 := hR.hτ1
  have hμ0 := hR.hμ0
  have hμ1 := hR.hμ1
  have hfinal : 2 * L * T.r * ψ t * ‖q - qbar‖ = 2 * δ := by rw [hδ]; ring
  rw [hfinal, abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1.1 hτ0, mul_le_mul_of_nonneg_left h1.2 hτ0,
    mul_le_mul_of_nonneg_left h2.1 hμ0, mul_le_mul_of_nonneg_left h2.2 hμ0,
    mul_le_mul_of_nonneg_left h3.1 (sub_nonneg.2 hτ1),
    mul_le_mul_of_nonneg_left h3.2 (sub_nonneg.2 hτ1),
    mul_le_mul_of_nonneg_left h4.1 (sub_nonneg.2 hμ1),
    mul_le_mul_of_nonneg_left h4.2 (sub_nonneg.2 hμ1)]

/-- Step 3: the actual tilts are close to the common one. -/
lemma norm_tilt_sub_qbar_le (hR : IsRational T n iA iB iC iD τ μ) (hg : IsLip g L)
    (hs : SmallL T L) (θ : ℝ) {qbar : ℂ} {t : ℝ} (ht : t < 1) (hLK : L * T.K ≤ t)
    (hq : ‖qbar‖ ≤ t) (hlam : T.K * (2 * L * T.r * ψ t / T.dmin) < 1) {M : ℝ}
    (hM : ∀ i, |nonAffine T g n θ qbar i| ≤ M) (j : ZMod n) :
    ‖tilt T g L (θj n θ j) - qbar‖ ≤
      2 * T.K * M / (T.dmin * (1 - T.K * (2 * L * T.r * ψ t / T.dmin))) := by
  obtain ⟨hA, hB, hC, hD⟩ := rot_feet hR θ j
  set θ' := θj n θ j with hθ'
  set q := tilt T g L θ' with hqdef
  set lam' := T.K * (2 * L * T.r * ψ t / T.dmin) with hlam'
  have hqt : ‖q‖ ≤ t := (norm_tilt_le hg hs _).trans hLK
  have hfix : T.Q g θ' q = q := Q_tilt hg hs θ'
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- `‖Q(qbar) - qbar‖ ≤ K · 2M / d_min`
  have hd := T.det_rot_ne θ'
  have hqbar_eq : qbar = solve2 (rot θ' * T.e₁) (rot θ' * T.e₂)
      (dot (rot θ' * T.e₁) qbar) (dot (rot θ' * T.e₂) qbar) := eq_solve2 hd rfl rfl
  have hα : |(g (foot (rot θ' * T.A) qbar) - g (foot (rot θ' * T.C) qbar)) / T.d₁ -
      dot (rot θ' * T.e₁) qbar| ≤ 2 * M / T.dmin := by
    have e1 := dot_rot_e₁ (T := T) θ' qbar
    have k : (g (foot (rot θ' * T.A) qbar) - g (foot (rot θ' * T.C) qbar)) / T.d₁ -
        dot (rot θ' * T.e₁) qbar =
        (nonAffine T g n θ qbar (iA + j) - nonAffine T g n θ qbar (iC + j)) / T.d₁ := by
      have hd1 := T.d₁_pos.ne'
      rw [eq_div_iff hd1, sub_mul, div_mul_cancel₀ _ hd1, e1, hA, hC]
      unfold nonAffine heights; ring
    rw [k, abs_div, abs_of_pos T.d₁_pos]
    have hnum : |nonAffine T g n θ qbar (iA + j) - nonAffine T g n θ qbar (iC + j)| ≤ 2 * M := by
      calc _ ≤ |nonAffine T g n θ qbar (iA + j)| + |nonAffine T g n θ qbar (iC + j)| :=
            abs_sub _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    calc _ ≤ 2 * M / T.d₁ := div_le_div_of_nonneg_right hnum T.d₁_pos.le
      _ ≤ 2 * M / T.dmin := div_le_div_of_nonneg_left (by positivity) T.dmin_pos T.dmin_le_d₁
  have hβ : |(g (foot (rot θ' * T.B) qbar) - g (foot (rot θ' * T.D) qbar)) / T.d₂ -
      dot (rot θ' * T.e₂) qbar| ≤ 2 * M / T.dmin := by
    have e2 := dot_rot_e₂ (T := T) θ' qbar
    have k : (g (foot (rot θ' * T.B) qbar) - g (foot (rot θ' * T.D) qbar)) / T.d₂ -
        dot (rot θ' * T.e₂) qbar =
        (nonAffine T g n θ qbar (iB + j) - nonAffine T g n θ qbar (iD + j)) / T.d₂ := by
      have hd2 := T.d₂_pos.ne'
      rw [eq_div_iff hd2, sub_mul, div_mul_cancel₀ _ hd2, e2, hB, hD]
      unfold nonAffine heights; ring
    rw [k, abs_div, abs_of_pos T.d₂_pos]
    have hnum : |nonAffine T g n θ qbar (iB + j) - nonAffine T g n θ qbar (iD + j)| ≤ 2 * M := by
      calc _ ≤ |nonAffine T g n θ qbar (iB + j)| + |nonAffine T g n θ qbar (iD + j)| :=
            abs_sub _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    calc _ ≤ 2 * M / T.d₂ := div_le_div_of_nonneg_right hnum T.d₂_pos.le
      _ ≤ 2 * M / T.dmin := div_le_div_of_nonneg_left (by positivity) T.dmin_pos T.dmin_le_d₂
  have hQq : ‖T.Q g θ' qbar - qbar‖ ≤ T.K * (2 * M / T.dmin) := by
    have e : T.Q g θ' qbar - qbar = solve2 (rot θ' * T.e₁) (rot θ' * T.e₂)
        ((g (foot (rot θ' * T.A) qbar) - g (foot (rot θ' * T.C) qbar)) / T.d₁ -
          dot (rot θ' * T.e₁) qbar)
        ((g (foot (rot θ' * T.B) qbar) - g (foot (rot θ' * T.D) qbar)) / T.d₂ -
          dot (rot θ' * T.e₂) qbar) := by
      calc T.Q g θ' qbar - qbar = T.Q g θ' qbar - solve2 (rot θ' * T.e₁) (rot θ' * T.e₂)
            (dot (rot θ' * T.e₁) qbar) (dot (rot θ' * T.e₂) qbar) := by rw [← hqbar_eq]
        _ = _ := by unfold Q; rw [solve2_sub hd]
    rw [e]
    have := norm_solve2_le (T.norm_rot_e₁ θ') (T.norm_rot_e₂ θ') (T.γ_rot_lt_one θ') hα hβ
    rwa [T.γ_rot] at this
  -- contraction on the disc of radius `t`
  have hc := norm_Q_sub_le (T := T) hg hg.nonneg θ' hqt hq ht
  have h2 : ‖q - qbar‖ ≤ lam' * ‖q - qbar‖ + T.K * (2 * M / T.dmin) := by
    have e : q - qbar = (T.Q g θ' q - T.Q g θ' qbar) + (T.Q g θ' qbar - qbar) := by
      rw [hfix]; ring
    calc ‖q - qbar‖ = ‖(T.Q g θ' q - T.Q g θ' qbar) + (T.Q g θ' qbar - qbar)‖ := by rw [← e]
      _ ≤ ‖T.Q g θ' q - T.Q g θ' qbar‖ + ‖T.Q g θ' qbar - qbar‖ := norm_add_le _ _
      _ ≤ T.K * (2 * L * T.r * ψ t / T.dmin * ‖q - qbar‖) + T.K * (2 * M / T.dmin) := by
          gcongr
      _ = lam' * ‖q - qbar‖ + T.K * (2 * M / T.dmin) := by rw [hlam']; ring
  have hpos : 0 < 1 - lam' := by linarith
  rw [le_div_iff₀ (mul_pos T.dmin_pos hpos)]
  have hK := T.K_nonneg
  have hdm := T.dmin_pos
  have : ‖q - qbar‖ * (1 - lam') ≤ T.K * (2 * M / T.dmin) := by nlinarith
  calc ‖q - qbar‖ * (T.dmin * (1 - lam')) = T.dmin * (‖q - qbar‖ * (1 - lam')) := by ring
    _ ≤ T.dmin * (T.K * (2 * M / T.dmin)) := by gcongr
    _ = 2 * T.K * M := by field_simp

/-- Step 2 (coercivity): the non-affine part is controlled by the wobbling. -/
lemma abs_nonAffine_le (hR : IsRational T n iA iB iC iD τ μ) (hC : Coercive iA iB iC iD τ μ σ)
    (hσ : 0 < σ) (hr : 0 < T.r) (θ : ℝ) {qbar : ℂ} (hfix : lsq T g n θ qbar = qbar) {B : ℝ}
    (hB : ∀ j, |circ iA iB iC iD τ μ (nonAffine T g n θ qbar) j| ≤ B) (i : ZMod n) :
    |nonAffine T g n θ qbar i| ≤ Real.sqrt n / σ * B := by
  set N := nonAffine T g n θ qbar with hN
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hcoerc := hC N (sum_nonAffine hR.hn θ qbar) (sum_nonAffine_mul_ω hR.hn hr θ hfix)
  have hsumB : ∑ j, circ iA iB iC iD τ μ N j ^ 2 ≤ n * B ^ 2 := by
    calc ∑ j, circ iA iB iC iD τ μ N j ^ 2 ≤ ∑ _j : ZMod n, B ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := hB j
          nlinarith [abs_nonneg (circ iA iB iC iD τ μ N j), sq_abs (circ iA iB iC iD τ μ N j)]
      _ = n * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_zmod_real]
  have hNi : N i ^ 2 ≤ ∑ k, N k ^ 2 :=
    Finset.single_le_sum (f := fun k => N k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : N i ^ 2 ≤ (Real.sqrt n / σ * B) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [mul_pow, div_pow, Real.sq_sqrt hn0]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hNi (sq_nonneg σ)]
  exact abs_le_of_sq_le_sq hsq (by positivity)

/-- The data of Theorem 5.11 (see `OrbitData.of_paper` for the conditions as stated in the paper). -/
structure OrbitData (T : Table) (L : ℝ) (n : ℕ) (σ : ℝ) : Prop where
  t_le : Real.sqrt 2 * T.K * L ≤ 1 / 2
  hP : 2 * L * ψ (Real.sqrt 2 * T.K * L) < 1
  hlam : T.K * (2 * L * T.r * ψ (Real.sqrt 2 * T.K * L) / T.dmin) < 1
  hσ : 0 < σ
  hr : 0 < T.r
  hmain : (n + 1) * ((2 * T.K * Real.sqrt n) / (σ * T.dmin *
      (1 - T.K * (2 * L * T.r * ψ (Real.sqrt 2 * T.K * L) / T.dmin)))) *
      (2 * L * T.r * ψ (Real.sqrt 2 * T.K * L)) < 1

omit [NeZero n] in
/-- The conditions of Theorem 5.11 as stated in the paper imply `OrbitData`: with
`t = √2 K L`, `λ' = (4/√3)(r/d_min) K L t`, `η = (4/√3) r L t` and
`A = 2K√n / (σ d_min (1 - λ'))`, the paper assumes `t ≤ 1/2`, `λ' < 1` and `(n+1) A η < 1`
(the Lean conditions use `ψ(t) ≤ (2/√3) t` instead of `(2/√3) t`, so they are weaker). -/
lemma OrbitData.of_paper (hL : 0 ≤ L) (hσ : 0 < σ) (hr : 0 < T.r)
    (ht : Real.sqrt 2 * T.K * L ≤ 1 / 2)
    (hlam : 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * (Real.sqrt 2 * T.K * L) < 1)
    (hmain : (n + 1) * (2 * T.K * Real.sqrt n / (σ * T.dmin *
        (1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * (Real.sqrt 2 * T.K * L)))) *
        (4 / Real.sqrt 3 * T.r * L * (Real.sqrt 2 * T.K * L)) < 1) :
    OrbitData T L n σ := by
  set t := Real.sqrt 2 * T.K * L with htdef
  have hK := sqrt_two_le_K T
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hK0 : 0 < T.K := lt_of_lt_of_le hs2 hK
  have ht0 : 0 ≤ t := by positivity
  have hψ : ψ t ≤ 2 / Real.sqrt 3 * t := psi_le ht0 ht
  have hψ0 := ψ_nonneg ht0
  have hd := T.dmin_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  -- `2 L r ψ(t) ≤ η` and `K (2 L r ψ(t) / d_min) ≤ λ'`
  have hη : 2 * L * T.r * ψ t ≤ 4 / Real.sqrt 3 * T.r * L * t := by
    have := mul_le_mul_of_nonneg_left hψ (by positivity : 0 ≤ 2 * L * T.r)
    calc _ ≤ 2 * L * T.r * (2 / Real.sqrt 3 * t) := this
      _ = _ := by ring
  have hlamψ : T.K * (2 * L * T.r * ψ t / T.dmin) ≤ 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t := by
    have := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hη hd.le) hK0.le
    calc _ ≤ T.K * (4 / Real.sqrt 3 * T.r * L * t / T.dmin) := this
      _ = _ := by ring
  have hlam0 : 0 ≤ T.K * (2 * L * T.r * ψ t / T.dmin) := by positivity
  refine ⟨ht, ?_, lt_of_le_of_lt hlamψ hlam, hσ, hr, ?_⟩
  · -- `2 L ψ(t) ≤ (4/√3) L t ≤ (4/√3)(1/4)(1/2) < 1`, as `L ≤ t / √2 ≤ 1/4`
    have hLt : L ≤ 1 / 4 := by
      have : Real.sqrt 2 * Real.sqrt 2 * L ≤ 1 / 2 := by
        calc Real.sqrt 2 * Real.sqrt 2 * L ≤ Real.sqrt 2 * T.K * L := by gcongr
          _ ≤ 1 / 2 := ht
      rw [Real.mul_self_sqrt (by norm_num)] at this; linarith
    have h3' : (1 : ℝ) ≤ Real.sqrt 3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have : 2 * L * ψ t ≤ 2 * L * (2 / Real.sqrt 3 * t) := mul_le_mul_of_nonneg_left hψ (by positivity)
    have h4 : 2 / Real.sqrt 3 ≤ 2 := by rw [div_le_iff₀ h3]; nlinarith
    have : 2 * L * (2 / Real.sqrt 3 * t) ≤ 2 * (1 / 4) * (2 * (1 / 2)) := by
      apply mul_le_mul (by linarith) (mul_le_mul h4 ht ht0 (by norm_num)) (by positivity) (by norm_num)
    linarith
  · -- monotonicity in `λ` and `η`
    have hlt : 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t < 1 := hlam
    have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hden : σ * T.dmin * (1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t) ≤
        σ * T.dmin * (1 - T.K * (2 * L * T.r * ψ t / T.dmin)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hden0 : 0 < σ * T.dmin * (1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t) := by
      have : 0 < 1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t := by linarith
      positivity
    have hA : 2 * T.K * Real.sqrt n / (σ * T.dmin * (1 - T.K * (2 * L * T.r * ψ t / T.dmin))) ≤
        2 * T.K * Real.sqrt n / (σ * T.dmin * (1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t)) :=
      div_le_div_of_nonneg_left (by positivity) hden0 hden
    have hA0 : 0 ≤ 2 * T.K * Real.sqrt n / (σ * T.dmin * (1 - T.K * (2 * L * T.r * ψ t / T.dmin))) := by
      apply div_nonneg (by positivity)
      have : T.K * (2 * L * T.r * ψ t / T.dmin) < 1 := lt_of_le_of_lt hlamψ hlt
      have : 0 < 1 - T.K * (2 * L * T.r * ψ t / T.dmin) := by linarith
      positivity
    have hn1 : (0 : ℝ) ≤ n + 1 := by positivity
    calc (n + 1) * (2 * T.K * Real.sqrt n / (σ * T.dmin * (1 - T.K * (2 * L * T.r * ψ t / T.dmin)))) *
          (2 * L * T.r * ψ t)
        ≤ (n + 1) * (2 * T.K * Real.sqrt n / (σ * T.dmin *
          (1 - 4 / Real.sqrt 3 * (T.r / T.dmin) * T.K * L * t))) * (4 / Real.sqrt 3 * T.r * L * t) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hA hn1) hη (by positivity) (by positivity)
      _ < 1 := hmain

/-- Theorem 5.11 (main estimate): on every orbit, the wobbling cannot have a constant strict
sign. -/
theorem not_all_pos (hR : IsRational T n iA iB iC iD τ μ) (hC : Coercive iA iB iC iD τ μ σ)
    (hg : IsLip g L) (hs : SmallL T L) (hd : OrbitData T L n σ) (θ : ℝ) :
    ¬ (∀ j, 0 < wob T g L (θj n θ j)) ∧ ¬ (∀ j, wob T g L (θj n θ j) < 0) := by
  -- notation
  set t := Real.sqrt 2 * T.K * L with ht
  set η := 2 * L * T.r * ψ t with hη
  set lam' := T.K * (2 * L * T.r * ψ t / T.dmin) with hlam'
  set A := (2 * T.K * Real.sqrt n) / (σ * T.dmin * (1 - lam')) with hA
  have hL := hg.nonneg
  have hr := hd.hr
  have hσ := hd.hσ
  have hK := T.K_nonneg
  have hdm := T.dmin_pos
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs21 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have ht1 : t < 1 := by linarith [hd.t_le]
  have ht0 : 0 ≤ t := by positivity
  have hLK : L * T.K ≤ t := by
    rw [ht]; nlinarith [mul_nonneg (sub_nonneg.2 hs21) (mul_nonneg hL hK)]
  have h2L : 2 * L ≤ t := by
    rw [ht]
    have h1 := mul_le_mul_of_nonneg_left (sqrt_two_le_K T) (Real.sqrt_nonneg 2)
    have h2 : 2 ≤ Real.sqrt 2 * T.K := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hL]
  have hη0 : 0 ≤ η := by have := ψ_nonneg ht0; positivity
  have hlam1 : lam' < 1 := hd.hlam
  have hpos : 0 < 1 - lam' := by linarith
  have hA0 : 0 ≤ A := by positivity
  have hmain : (n + 1) * A * η < 1 := hd.hmain
  -- Step 1: the common tilt
  have hn3 := hR.hn
  obtain ⟨qbar, hqbar, hfix⟩ := exists_qbar (T := T) (g := g) (by omega : 2 ≤ n) hr hg θ ht1 h2L
    hd.hP
  set N := nonAffine T g n θ qbar with hN
  set w : ZMod n → ℝ := fun j => wob T g L (θj n θ j) with hw
  set δ : ZMod n → ℝ := fun j => ‖tilt T g L (θj n θ j) - qbar‖ with hδ
  -- maxima of `|w|` and of `δ` on the orbit
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => |w j|) Finset.univ_nonempty
  obtain ⟨j₁, -, hj₁⟩ := Finset.exists_max_image Finset.univ δ Finset.univ_nonempty
  set W := |w j₀| with hW
  set D := δ j₁ with hD
  have hWj : ∀ j, |w j| ≤ W := fun j => hj₀ j (Finset.mem_univ j)
  have hDj : ∀ j, δ j ≤ D := fun j => hj₁ j (Finset.mem_univ j)
  -- Step 2
  have he : ∀ j, |w j - circ iA iB iC iD τ μ N j| ≤ η * D := by
    intro j
    calc _ ≤ 2 * L * T.r * ψ t * δ j := wob_sub_circ_le hR hg hs θ ht1 hLK hqbar j
      _ ≤ η * D := mul_le_mul_of_nonneg_left (hDj j) hη0
  have hCN : ∀ j, |circ iA iB iC iD τ μ N j| ≤ W + η * D := by
    intro j
    have h1 := he j
    have h2 := hWj j
    calc |circ iA iB iC iD τ μ N j| = |w j - (w j - circ iA iB iC iD τ μ N j)| := by
          rw [sub_sub_cancel]
      _ ≤ |w j| + |w j - circ iA iB iC iD τ μ N j| := abs_sub _ _
      _ ≤ W + η * D := add_le_add h2 h1
  have hNi : ∀ i, |N i| ≤ Real.sqrt n / σ * (W + η * D) :=
    abs_nonAffine_le hR hC hσ hr θ hfix hCN
  -- Step 3
  have hDle : D ≤ A * (W + η * D) := by
    have := norm_tilt_sub_qbar_le hR hg hs θ ht1 hLK hqbar hlam1 hNi j₁
    calc D ≤ 2 * T.K * (Real.sqrt n / σ * (W + η * D)) / (T.dmin * (1 - lam')) := this
      _ = A * (W + η * D) := by
          have h1 := hσ.ne'
          have h2 := hdm.ne'
          have h3 := hpos.ne'
          rw [hA]; field_simp
  -- Step 4: the orbit sum
  have hsum : |∑ j, w j| ≤ n * (η * D) := by
    have e : ∑ j, w j = ∑ j, (w j - circ iA iB iC iD τ μ N j) := by
      rw [Finset.sum_sub_distrib, sum_circ, sub_zero]
    rw [e]
    calc |∑ j, (w j - circ iA iB iC iD τ μ N j)|
        ≤ ∑ j, |w j - circ iA iB iC iD τ μ N j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ZMod n, η * D := Finset.sum_le_sum fun j _ => he j
      _ = n * (η * D) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_zmod_real]
  -- conclusion: `W (1 - (n+1) A η) ≤ 0`
  have hkey : W * (1 - (n + 1) * A * η) ≤ 0 → W ≤ 0 := by
    intro h
    have : 0 < 1 - (n + 1) * A * η := by linarith
    nlinarith
  have hD0 : 0 ≤ D := norm_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbound : ∀ S : ℝ, W ≤ S → S ≤ n * (η * D) → W ≤ 0 := by
    intro S h1 h2
    apply hkey
    -- `D (1 - A η) ≤ A W` and `W ≤ n η D`
    have hD' : D * (1 - A * η) ≤ A * W := by nlinarith
    have hAη : A * η ≤ 1 := by nlinarith [mul_nonneg hA0 hη0]
    have hWD : W ≤ n * (η * D) := h1.trans h2
    nlinarith [mul_nonneg (sub_nonneg.2 hWD) (sub_nonneg.2 hAη),
      mul_nonneg (mul_nonneg hn0 hη0) (sub_nonneg.2 hD')]
  constructor
  · intro hall
    have hsum_ge : W ≤ ∑ j, w j := by
      have hw0 : W = w j₀ := abs_of_pos (hall j₀)
      rw [hw0]
      exact Finset.single_le_sum (f := w) (fun j _ => (hall j).le) (Finset.mem_univ j₀)
    have := hbound (∑ j, w j) hsum_ge (le_trans (le_abs_self _) hsum)
    have hW0 : 0 < W := by rw [hW]; exact abs_pos.2 (hall j₀).ne'
    linarith
  · intro hall
    have hsum_ge : W ≤ -∑ j, w j := by
      have hw0 : W = -w j₀ := abs_of_neg (hall j₀)
      rw [hw0, ← Finset.sum_neg_distrib]
      exact Finset.single_le_sum (f := fun j => -w j) (fun j _ => by linarith [hall j])
        (Finset.mem_univ j₀)
    have := hbound (-∑ j, w j) hsum_ge (le_trans (neg_le_abs _) hsum)
    have hW0 : 0 < W := by rw [hW]; exact abs_pos.2 (hall j₀).ne
    linarith

/-- Theorem 5.11: a rational non-degenerate table can be stabilised by rotating it, on any terrain
with a small enough Lipschitz constant. -/
theorem exists_balanced (hR : IsRational T n iA iB iC iD τ μ) (hC : Coercive iA iB iC iD τ μ σ)
    (hg : IsLip g L) (hs : SmallL T L) (hd : OrbitData T L n σ) :
    ∃ θ, ∃ q c, ‖q‖ < 1 ∧ resid g θ q c T.A = 0 ∧ resid g θ q c T.B = 0 ∧
      resid g θ q c T.C = 0 ∧ resid g θ q c T.D = 0 := by
  -- On the orbit of `0`, the wobbling takes a non-positive and a non-negative value.
  obtain ⟨hpos, hneg⟩ := not_all_pos hR hC hg hs hd 0
  push Not at hpos hneg
  obtain ⟨j₁, hj₁⟩ := hpos
  obtain ⟨j₂, hj₂⟩ := hneg
  -- intermediate value theorem between the two angles
  have hcont := continuous_wob hg hs
  have : ∃ θ, wob T g L θ = 0 := by
    rcases le_total (θj n 0 j₁) (θj n 0 j₂) with h | h
    · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc h hcont.continuousOn ⟨hj₁, hj₂⟩
      exact ⟨θ, hθ⟩
    · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' h hcont.continuousOn ⟨hj₁, hj₂⟩
      exact ⟨θ, hθ⟩
  obtain ⟨θ, hθ⟩ := this
  exact ⟨θ, (four_feet_iff hg hs θ).2 hθ⟩

end Table

end Wobbly
