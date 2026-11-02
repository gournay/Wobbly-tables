import Wobbly.Modes

/-!
# Lemma 5.3 (f): the shape of the table when `4` or `5` is a degenerate mode

The feet `e_E` are the roots of `Q(z) = z⁴ - s₁ z³ + s₂ z² - s₃ z + s₄` (`Feet.Qp`). A table is an
*isosceles trapezoid* (rectangles included) if its feet are symmetric with respect to a line
through the centre, and no foot lies on this line: in complex notation, there is `u` with
`|u| = 1` such that the reflection `z ↦ u z̄` maps the set of feet to itself without fixed foot
(`Feet.IsoTrap`). (If a foot lay on the line, the table would be a kite.)

* `Feet.nonParallel`: the diagonals of a table are never parallel;
* `Feet.isoTrap_of_m_four`: if `4 ∈ 𝒦`, the table is an isosceles trapezoid;
* `Feet.isoTrap_of_diag_eq`: a table with diagonals of the same length is an isosceles trapezoid;
* `Feet.m_five_classification`: if `5 ∈ 𝒦`, the table is an isosceles trapezoid, or, up to a
  rotation and a reflection, its feet are at zeros of `G_χ` for some `χ ∈ ]0, π/4]`.
-/

open Complex ComplexConjugate

namespace Wobbly

namespace Feet

variable (F : Feet)

/-- The set of feet. -/
def feet : Set ℂ := {F.A, F.B, F.C, F.D}

/-- Isosceles trapezoid (or rectangle): the feet are invariant under a reflection `z ↦ u z̄`
which fixes no foot. -/
def IsoTrap : Prop :=
  ∃ u : ℂ, ‖u‖ = 1 ∧ (∀ z ∈ F.feet, u * conj z ∈ F.feet) ∧ ∀ z ∈ F.feet, u * conj z ≠ z

/-- The polynomial whose roots are the feet. -/
def Qp (z : ℂ) : ℂ := z ^ 4 - F.s₁ * z ^ 3 + F.s₂ * z ^ 2 - F.s₃ * z + F.s₄

lemma Qp_eq (z : ℂ) : F.Qp z = (z - F.A) * (z - F.B) * (z - F.C) * (z - F.D) := by
  simp only [Qp, s₁, s₂, s₃, s₄]; ring

lemma Qp_feet {z : ℂ} (hz : z ∈ F.feet) : F.Qp z = 0 := by
  rcases hz with rfl | rfl | rfl | rfl <;> rw [Qp_eq] <;> ring

lemma mem_feet_of_Qp {z : ℂ} (h : F.Qp z = 0) : z ∈ F.feet := by
  rw [Qp_eq] at h
  simp only [mul_eq_zero, sub_eq_zero] at h
  simp only [feet, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma norm_of_mem {z : ℂ} (hz : z ∈ F.feet) : ‖z‖ = 1 := by
  rcases hz with rfl | rfl | rfl | rfl
  exacts [F.nA, F.nB, F.nC, F.nD]

lemma norm_s₄ : ‖F.s₄‖ = 1 := by simp [s₄, F.nA, F.nB, F.nC, F.nD]

lemma s₄_ne : F.s₄ ≠ 0 := ne_zero_of_norm_eq_one F.norm_s₄

omit F in
lemma mul_conj_self {z : ℂ} (hz : ‖z‖ = 1) : conj z * z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

/-- If `u² = s₄` and `s₃ = u s₁`, the reflection `z ↦ u z̄` maps the feet to the feet. -/
lemma symm_of {u : ℂ} (h1 : u ^ 2 = F.s₄) (h2 : F.s₃ = u * F.s₁) :
    ∀ z ∈ F.feet, u * conj z ∈ F.feet := by
  intro z hz
  apply F.mem_feet_of_Qp
  have hz1 := F.norm_of_mem hz
  have hz0 := ne_zero_of_norm_eq_one hz1
  rw [← inv_eq_conj_of_norm_eq_one hz1]
  set w := u * z⁻¹
  have hw : w * z = u := by simp only [w]; field_simp
  have hQ := F.Qp_feet hz
  unfold Qp at hQ ⊢
  have key : z ^ 4 * (w ^ 4 - F.s₁ * w ^ 3 + F.s₂ * w ^ 2 - F.s₃ * w + F.s₄) =
      F.s₄ * (z ^ 4 - F.s₁ * z ^ 3 + F.s₂ * z ^ 2 - F.s₃ * z + F.s₄) := by
    linear_combination
      (((w * z) ^ 3 + (w * z) ^ 2 * u + (w * z) * u ^ 2 + u ^ 3)
        - F.s₁ * z * ((w * z) ^ 2 + (w * z) * u + u ^ 2) + F.s₂ * z ^ 2 * ((w * z) + u)
        - F.s₃ * z ^ 3) * hw
      + ((u ^ 2 + F.s₄) - z * F.s₁ * u + z ^ 2 * F.s₂ - z ^ 3 * F.s₁) * h1
      + (z * F.s₄ - z ^ 3 * u) * h2
  rw [hQ, mul_zero] at key
  exact (mul_eq_zero.1 key).resolve_left (pow_ne_zero _ hz0)

omit F in
lemma sq_of_fixed {u z : ℂ} (hz : ‖z‖ = 1) (h : u * conj z = z) : u = z ^ 2 := by
  have := congrArg (· * z) h
  rw [mul_assoc, mul_conj_self hz, mul_one] at this
  rw [this]; ring

/-- **Lemma 5.3 (f)**: if `4 ∈ 𝒦`, the table is an isosceles trapezoid (or a rectangle). -/
theorem isoTrap_of_m_four (h4 : F.m 4 = 0) : F.IsoTrap := by
  rw [m_four_iff] at h4
  have c1 := F.conj_s₁
  have c2 := F.conj_s₂
  have hs40 := F.s₄_ne
  by_cases hs1 : F.s₁ = 0
  · -- the square
    have hs2 : F.s₂ = 0 := by rw [h4, hs1]; ring
    have hs3 : F.s₃ = 0 := by rw [← c1, hs1]; simp
    set u := Complex.exp ((Complex.arg F.s₄ / 2 : ℝ) * I)
    have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hu2 : u ^ 2 = F.s₄ := by
      have := Complex.norm_mul_exp_arg_mul_I F.s₄
      rw [F.norm_s₄, Complex.ofReal_one, one_mul] at this
      rw [← this, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    refine ⟨u, hu, F.symm_of hu2 (by rw [hs3, hs1, mul_zero]), fun z hz hfix => ?_⟩
    have hz1 := F.norm_of_mem hz
    have huz := sq_of_fixed hz1 hfix
    have hQ := F.Qp_feet hz
    unfold Qp at hQ
    rw [hs1, hs2, hs3] at hQ
    apply hs40
    have : z ^ 4 = F.s₄ := by rw [← hu2, huz]; ring
    linear_combination (hQ - this) / 2
  · have hc0 : conj F.s₁ ≠ 0 := (map_ne_zero _).2 hs1
    set u := F.s₁ / conj F.s₁ with hudef
    have hu1 : ‖u‖ = 1 := by
      rw [hudef, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hs1)]
    have e : conj F.s₁ ^ 2 * F.s₄ = F.s₁ ^ 2 := by rw [← map_pow, ← h4, c2]
    have hu2 : u ^ 2 = F.s₄ := by
      rw [hudef, div_pow, div_eq_iff (pow_ne_zero _ hc0)]; linear_combination -e
    have hu3 : F.s₃ = u * F.s₁ := by
      rw [← c1, hudef]; field_simp; linear_combination e
    refine ⟨u, hu1, F.symm_of hu2 hu3, fun z hz hfix => ?_⟩
    have hz1 := F.norm_of_mem hz
    have hz0 := ne_zero_of_norm_eq_one hz1
    have huz := sq_of_fixed hz1 hfix
    have hQ := F.Qp_feet hz
    unfold Qp at hQ
    -- `2 z² - 2 s₁ z + s₁² = 0`
    have hq : z ^ 2 * (2 * z ^ 2 - 2 * F.s₁ * z + F.s₁ ^ 2) = 0 := by
      rw [h4, hu3, ← hu2, huz] at hQ; linear_combination hQ
    have hq' := (mul_eq_zero.1 hq).resolve_left (pow_ne_zero _ hz0)
    -- `t = s₁ / z` is real
    set t := F.s₁ / z
    have ht : t ^ 2 - 2 * t + 2 = 0 := by
      simp only [t]; field_simp; linear_combination hq'
    have hfix' : z ^ 2 * conj F.s₁ = F.s₁ := by
      rw [← huz, hudef]; field_simp
    have htc : conj t = t := by
      simp only [t, map_div₀, ← inv_eq_conj_of_norm_eq_one hz1]
      field_simp
      linear_combination hfix'
    have him : t.im = 0 := by
      have := congrArg Complex.im htc; simp at this; linarith
    have hre := congrArg Complex.re ht
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, pow_two, him, Complex.re_ofNat,
      Complex.im_ofNat, Complex.zero_re] at hre
    nlinarith [sq_nonneg (t.re - 1)]

/-- A table whose diagonals have the same length is an isosceles trapezoid (or a rectangle). -/
theorem isoTrap_of_diag_eq (hd : ‖F.A - F.C‖ = ‖F.B - F.D‖) : F.IsoTrap := by
  have hsq : ∀ z w : ℂ, ‖z‖ = 1 → ‖w‖ = 1 → ((‖z - w‖ ^ 2 : ℝ) : ℂ) = 2 - z / w - w / z := by
    intro z w hz hw
    have hz0 := ne_zero_of_norm_eq_one hz
    have hw0 := ne_zero_of_norm_eq_one hw
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sub, ← inv_eq_conj_of_norm_eq_one hz,
      ← inv_eq_conj_of_norm_eq_one hw]
    field_simp; ring
  have hA0 := F.A_ne; have hB0 := F.B_ne; have hC0 := F.C_ne; have hD0 := F.D_ne
  have e := hsq _ _ F.nA F.nC
  rw [hd, hsq _ _ F.nB F.nD] at e
  have hp : (F.A * F.B - F.C * F.D) * (F.A * F.D - F.B * F.C) = 0 := by
    field_simp at e; linear_combination e
  have cA : conj F.A = F.A⁻¹ := (inv_eq_conj_of_norm_eq_one F.nA).symm
  have cB : conj F.B = F.B⁻¹ := (inv_eq_conj_of_norm_eq_one F.nB).symm
  have cC : conj F.C = F.C⁻¹ := (inv_eq_conj_of_norm_eq_one F.nC).symm
  have cD : conj F.D = F.D⁻¹ := (inv_eq_conj_of_norm_eq_one F.nD).symm
  have mem : ∀ {z}, z = F.A ∨ z = F.B ∨ z = F.C ∨ z = F.D → z ∈ F.feet := fun h => by
    simp only [feet, Set.mem_insert_iff, Set.mem_singleton_iff]; exact h
  rcases mul_eq_zero.1 hp with h | h
  · -- `AB = CD`: the reflection swaps `A ↔ B` and `C ↔ D`
    have hAB : F.A * F.B = F.C * F.D := sub_eq_zero.1 h
    refine ⟨F.A * F.B, by rw [norm_mul, F.nA, F.nB, one_mul], ?_, ?_⟩
    · rintro z (rfl | rfl | rfl | rfl)
      · apply mem; right; left; rw [cA]; field_simp
      · apply mem; left; rw [cB]; field_simp
      · apply mem; right; right; right; rw [cC, hAB]; field_simp
      · apply mem; right; right; left; rw [cD, hAB]; field_simp
    · rintro z (rfl | rfl | rfl | rfl) hz
      · rw [cA] at hz; field_simp at hz; exact F.AB hz.symm
      · rw [cB] at hz; field_simp at hz; exact F.AB hz
      · rw [cC, hAB] at hz; field_simp at hz; exact F.CD hz.symm
      · rw [cD, hAB] at hz; field_simp at hz; exact F.CD hz
  · -- `AD = BC`: the reflection swaps `A ↔ D` and `B ↔ C`
    have hAD : F.A * F.D = F.B * F.C := sub_eq_zero.1 h
    refine ⟨F.A * F.D, by rw [norm_mul, F.nA, F.nD, one_mul], ?_, ?_⟩
    · rintro z (rfl | rfl | rfl | rfl)
      · apply mem; right; right; right; rw [cA]; field_simp
      · apply mem; right; right; left; rw [cB, hAD]; field_simp
      · apply mem; right; left; rw [cC, hAD]; field_simp
      · apply mem; left; rw [cD]; field_simp
    · rintro z (rfl | rfl | rfl | rfl) hz
      · rw [cA] at hz; field_simp at hz; exact F.AD hz.symm
      · rw [cB, hAD] at hz; field_simp at hz; exact F.BC hz.symm
      · rw [cC, hAD] at hz; field_simp at hz; exact F.BC hz
      · rw [cD] at hz; field_simp at hz; exact F.AD hz

/-! ### The family `G_χ` -/

/-- `Q_χ(z) = z⁴ - e^{iχ} z³ + cos(2χ) z² - e^{-iχ} z + 1`; for `z = e^{iθ}`,
`e^{-2iθ} Q_χ(z) = G_χ(θ)` (`G_eq`). -/
noncomputable def Qχ (χ : ℝ) (z : ℂ) : ℂ :=
  z ^ 4 - Complex.exp (χ * I) * z ^ 3 + (Real.cos (2 * χ) : ℂ) * z ^ 2
    - Complex.exp (-(χ * I)) * z + 1

lemma Qχ_rot (χ : ℝ) (n : ℤ) (z : ℂ) :
    Qχ (χ + n * (Real.pi / 2)) (Complex.exp ((n * (Real.pi / 2) : ℝ) * I) * z) = Qχ χ z := by
  set ω := Complex.exp ((n * (Real.pi / 2) : ℝ) * I)
  have h2 : ω ^ 2 = (-1) ^ n := by
    rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (((n * (Real.pi / 2) : ℝ) : ℂ) * I) =
      n * (Real.pi * I) by push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have h4 : ω ^ 4 = 1 := by
    rw [show ω ^ 4 = (ω ^ 2) ^ 2 by ring, h2, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul]; simp
  have hc : ((Real.cos (2 * (χ + n * (Real.pi / 2))) : ℝ) : ℂ) = (-1) ^ n * Real.cos (2 * χ) := by
    rw [show 2 * (χ + n * (Real.pi / 2)) = 2 * χ + n * Real.pi by ring, Real.cos_add_int_mul_pi]
    push_cast; ring
  have he1 : Complex.exp (((χ + n * (Real.pi / 2) : ℝ) : ℂ) * I) = Complex.exp (χ * I) * ω := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have he2 : Complex.exp (-(((χ + n * (Real.pi / 2) : ℝ) : ℂ) * I)) * ω = Complex.exp (-(χ * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  unfold Qχ
  rw [he1, hc]
  have hn2 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_zpow]; norm_num
  linear_combination (z ^ 4) * h4 - Complex.exp (χ * I) * z ^ 3 * h4
    + (z ^ 2 * Real.cos (2 * χ)) * ((-1) ^ n * h2 + hn2) - z * he2

lemma Qχ_conj (χ : ℝ) (z : ℂ) : Qχ (-χ) (conj z) = conj (Qχ χ z) := by
  unfold Qχ
  simp only [map_add, map_sub, map_mul, map_pow, map_one, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, map_neg, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, Real.cos_neg]

/-- **Lemma 5.3 (f)** for `k = 5`: if `5 ∈ 𝒦`, then the table is an isosceles trapezoid (or a
rectangle), or, up to a rotation and possibly a reflection, its feet are roots of `Q_χ`, i.e. at
zeros of `G_χ(θ) = 2 cos 2θ - 2 cos(θ + χ) + cos 2χ`, for some `χ ∈ ]0, π/4]`. -/
theorem m_five_classification (h : F.NonParallel) (h5 : F.m 5 = 0) :
    F.IsoTrap ∨ ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∃ refl : Bool, ∃ χ : ℝ, 0 < χ ∧ χ ≤ Real.pi / 4 ∧
      ∀ z ∈ F.feet, Qχ χ (ω * (if refl then conj z else z)) = 0 := by
  by_cases hd : ‖F.A - F.C‖ = ‖F.B - F.D‖
  · exact Or.inl (F.isoTrap_of_diag_eq hd)
  right
  obtain ⟨ω, hω, χ, hχ, hroots⟩ := F.m_five_family' h h5 hd
  have h0 : ∀ z ∈ F.feet, Qχ χ (ω * z) = 0 := by
    intro z hz
    apply hroots
    rcases hz with rfl | rfl | rfl | rfl <;> simp [rotate]
  -- reduce `χ` modulo `π/2`
  have hπ : 0 < Real.pi / 2 := by positivity
  set n : ℤ := -⌊χ / (Real.pi / 2)⌋
  set χ₁ := χ + n * (Real.pi / 2)
  have hfl := Int.floor_le (χ / (Real.pi / 2))
  have hfl' := Int.lt_floor_add_one (χ / (Real.pi / 2))
  have hx : χ / (Real.pi / 2) * (Real.pi / 2) = χ := div_mul_cancel₀ _ hπ.ne'
  have hχ₁0 : 0 ≤ χ₁ := by
    simp only [χ₁, n]; push_cast
    have := mul_le_mul_of_nonneg_right hfl hπ.le
    linarith
  have hχ₁1 : χ₁ < Real.pi / 2 := by
    simp only [χ₁, n]; push_cast
    have := mul_lt_mul_of_pos_right hfl' hπ
    linarith
  have hsin : Real.sin (2 * χ₁) ≠ 0 := by
    rw [show 2 * χ₁ = 2 * χ + n * Real.pi by simp only [χ₁]; ring, Real.sin_add_int_mul_pi]
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hχ
  have hχ₁pos : 0 < χ₁ := by
    rcases eq_or_lt_of_le hχ₁0 with h0' | h0'
    · exact absurd (by rw [← h0']; simp) hsin
    · exact h0'
  set ω₁ := Complex.exp ((n * (Real.pi / 2) : ℝ) * I) * ω
  have hω₁ : ‖ω₁‖ = 1 := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, hω, one_mul]
  have h1 : ∀ z ∈ F.feet, Qχ χ₁ (ω₁ * z) = 0 := fun z hz => by
    rw [mul_assoc, Qχ_rot]; exact h0 z hz
  rcases le_or_gt χ₁ (Real.pi / 4) with hle | hgt
  · exact ⟨ω₁, hω₁, false, χ₁, hχ₁pos, hle, fun z hz => by simpa using h1 z hz⟩
  · -- reflect: `χ₂ = π/2 - χ₁`
    refine ⟨Complex.exp (((1 : ℤ) * (Real.pi / 2) : ℝ) * I) * conj ω₁, ?_, true,
      -χ₁ + (1 : ℤ) * (Real.pi / 2), by push_cast; linarith, by push_cast; linarith,
      fun z hz => ?_⟩
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_conj, hω₁, one_mul]
    · simp only [ite_true]
      rw [mul_assoc, ← map_mul, Qχ_rot, Qχ_conj, h1 z hz, map_zero]

/-- The same statement with the zeros of `G_χ`: every (rotated and possibly reflected) foot is
`e^{iθ}` with `G_χ(θ) = 0`. -/
theorem m_five_classification_G (h : F.NonParallel) (h5 : F.m 5 = 0) :
    F.IsoTrap ∨ ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∃ refl : Bool, ∃ χ : ℝ, 0 < χ ∧ χ ≤ Real.pi / 4 ∧
      ∀ z ∈ F.feet, ∃ θ : ℝ, ω * (if refl then conj z else z) = Complex.exp (θ * I) ∧
        2 * Real.cos (2 * θ) - 2 * Real.cos (θ + χ) + Real.cos (2 * χ) = 0 := by
  rcases F.m_five_classification h h5 with h' | ⟨ω, hω, refl, χ, h1, h2, hz⟩
  · exact Or.inl h'
  refine Or.inr ⟨ω, hω, refl, χ, h1, h2, fun z hzf => ?_⟩
  set w := ω * (if refl then conj z else z)
  have hw : ‖w‖ = 1 := by
    simp only [w]; rw [norm_mul, hω, one_mul]
    split_ifs <;> simp [F.norm_of_mem hzf]
  refine ⟨Complex.arg w, ?_, ?_⟩
  · have := Complex.norm_mul_exp_arg_mul_I w
    rw [hw, Complex.ofReal_one, one_mul] at this; exact this.symm
  · have hQ := hz z hzf
    have e := G_eq χ (Complex.arg w)
    have hw' : Complex.exp ((Complex.arg w : ℝ) * I) = w := by
      have := Complex.norm_mul_exp_arg_mul_I w
      rw [hw, Complex.ofReal_one, one_mul] at this; exact this
    rw [hw'] at e
    unfold Qχ at hQ
    rw [hQ, mul_zero] at e
    exact_mod_cast e.symm

/-- The diagonals of a table are never parallel (they meet at `X`, and a line meets the circle in
at most two points). -/
theorem nonParallel : F.NonParallel := by
  intro h0
  have ha : F.A - F.C ≠ 0 := sub_ne_zero.2 F.AC
  have hN : 0 < Complex.normSq (F.A - F.C) := Complex.normSq_pos.2 ha
  set p := (F.B - F.D) * conj (F.A - F.C) with hpdef
  have hp : p.im = 0 := by
    have : p = conj ((F.A - F.C) * conj (F.B - F.D)) := by simp [hpdef, mul_comm]
    rw [this, Complex.conj_im, h0, neg_zero]
  set lam : ℝ := p.re / Complex.normSq (F.A - F.C)
  have hb : F.B - F.D = (lam : ℂ) * (F.A - F.C) := by
    have e : (F.B - F.D) * ((Complex.normSq (F.A - F.C) : ℝ) : ℂ) = p * (F.A - F.C) := by
      rw [← Complex.mul_conj, hpdef]; ring
    have hp' : p = (p.re : ℂ) := Complex.ext rfl (by simp [hp])
    rw [hp'] at e
    have hN' : ((Complex.normSq (F.A - F.C) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [lam]; push_cast
    field_simp
    linear_combination e
  set t : ℝ := F.τ - F.μ * lam
  have hX := F.hX
  push_cast at hX
  have hD : F.D = F.C + (t : ℂ) * (F.A - F.C) := by
    simp only [t]; push_cast; linear_combination -hX - (F.μ : ℂ) * hb
  -- `|C + t (A - C)|² = 1` forces `t ∈ {0, 1}`
  set K := F.C.re * (F.A - F.C).re + F.C.im * (F.A - F.C).im
  have nq : ∀ s : ℝ, Complex.normSq (F.C + (s : ℂ) * (F.A - F.C)) =
      Complex.normSq F.C + 2 * s * K + s ^ 2 * Complex.normSq (F.A - F.C) := by
    intro s
    simp only [K, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
    ring
  have n1 : Complex.normSq F.C = 1 := by rw [Complex.normSq_eq_norm_sq, F.nC]; norm_num
  have nA : Complex.normSq (F.C + ((1 : ℝ) : ℂ) * (F.A - F.C)) = 1 := by
    rw [show F.C + ((1 : ℝ) : ℂ) * (F.A - F.C) = F.A by push_cast; ring,
      Complex.normSq_eq_norm_sq, F.nA]; norm_num
  have nD : Complex.normSq (F.C + (t : ℂ) * (F.A - F.C)) = 1 := by
    rw [← hD, Complex.normSq_eq_norm_sq, F.nD]; norm_num
  rw [nq] at nA nD
  rw [n1] at nA nD
  have ht : t * (t - 1) * Complex.normSq (F.A - F.C) = 0 := by linear_combination nD - t * nA
  rcases mul_eq_zero.1 ht with ht | ht
  · rcases mul_eq_zero.1 ht with ht | ht
    · exact F.CD (show F.D = F.C by rw [hD, ht]; simp).symm
    · have : t = 1 := by linarith
      exact F.AD (by rw [hD, this]; push_cast; ring)
  · exact hN.ne' ht

theorem m_five_classification' (h5 : F.m 5 = 0) :
    F.IsoTrap ∨ ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∃ refl : Bool, ∃ χ : ℝ, 0 < χ ∧ χ ≤ Real.pi / 4 ∧
      ∀ z ∈ F.feet, ∃ θ : ℝ, ω * (if refl then conj z else z) = Complex.exp (θ * I) ∧
        2 * Real.cos (2 * θ) - 2 * Real.cos (θ + χ) + Real.cos (2 * χ) = 0 :=
  F.m_five_classification_G F.nonParallel h5

end Feet

end Wobbly
