import Wobbly.Remarks5

/-!
# Remark 5.14 (a): ergodic averages of the wobbling function

* `tendsto_avg_of_irrational`: Weyl's equidistribution theorem. Along an irrational rotation
  (`e^{ikα} ≠ 1` for `k ≠ 0`), the averages of a continuous `2π`-periodic function converge to its
  mean. The proof checks it on the Fourier modes (geometric sums, `tendsto_avg_geom`) and uses the
  density of the trigonometric polynomials (`span_fourier_closure_eq_top`).
* `wob_periodic`, `tendsto_avg_wob`: hence the ergodic averages of `w_AC` converge to the mean of
  `w_AC`, which is the mean of `w_AC - F₀` (`integral_wob`): it is of order `L³`, and not `0` in
  general (`integral_wob_trapezoid_pos`).
-/

noncomputable section

open Complex Filter Topology MeasureTheory

namespace Wobbly

/-- `rot (j x) = rot x ^ j`. -/
lemma rot_nat_mul (j : ℕ) (x : ℝ) : rot (j * x) = rot x ^ j := by
  rw [rot, rot, ← Complex.exp_nat_mul]
  push_cast; ring_nf

/-- The averages of a geometric sequence `z w^j` with `|w| = 1`, `w ≠ 1`, tend to `0`. -/
lemma tendsto_avg_geom {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (z : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, z * w ^ j) atTop (𝓝 0) := by
  have hb : ∀ N : ℕ, ‖∑ j ∈ Finset.range N, z * w ^ j‖ ≤ ‖z‖ * (2 / ‖w - 1‖) := by
    intro N
    rw [← Finset.mul_sum, geom_sum_eq hw1, norm_mul, norm_div]
    gcongr
    calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num
  refine squeeze_zero_norm (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (‖z‖ * (2 / ‖w - 1‖)))
  rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hb N) (by positivity)

/-- **Weyl's equidistribution theorem**: for a continuous `2π`-periodic `f` and an irrational
rotation by `α` (`e^{ikα} ≠ 1` for `k ≠ 0`), the averages of `f` along the orbit `θ₀ + jα` converge
to the mean of `f`. -/
theorem tendsto_avg_of_irrational {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) {α : ℝ} (hα : ∀ k : ℤ, k ≠ 0 → rot (k * α) ≠ 1)
    (θ₀ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (θ₀ + j * α)) atTop
      (𝓝 ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ)) := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hπ : 0 < 2 * Real.pi := by positivity
  -- the lift of `f` to the circle
  set ψ : ℝ → ℂ := fun θ => (f θ : ℂ) with hψ
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp hf
  have hψp : Function.Periodic ψ (2 * Real.pi) := fun θ => by simp only [hψ, hp θ]
  let F : C(AddCircle (2 * Real.pi), ℂ) := ⟨hψp.lift, continuous_quot_lift _ hψc⟩
  have hF : ∀ θ : ℝ, F (θ : AddCircle (2 * Real.pi)) = (f θ : ℂ) := fun θ => rfl
  -- the averaging functionals `A_N` and the mean `M`
  set A : ℕ → C(AddCircle (2 * Real.pi), ℂ) → ℂ := fun N G =>
    (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, G ((θ₀ + j * α : ℝ) : AddCircle (2 * Real.pi)) with hA
  set M : C(AddCircle (2 * Real.pi), ℂ) → ℂ := fun G =>
    (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..2 * Real.pi, G (θ : AddCircle (2 * Real.pi))
    with hM
  have hc : ∀ G : C(AddCircle (2 * Real.pi), ℂ), Continuous fun θ : ℝ => G (θ : AddCircle (2 * Real.pi)) :=
    fun G => G.continuous.comp (AddCircle.continuous_mk' _)
  have hA_add : ∀ N G H, A N (G + H) = A N G + A N H := by
    intro N G H
    simp only [hA, ContinuousMap.add_apply, Finset.sum_add_distrib]
    ring
  have hA_smul : ∀ N (a : ℂ) G, A N (a • G) = a * A N G := by
    intro N a G
    simp only [hA, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  have hM_add : ∀ G H, M (G + H) = M G + M H := by
    intro G H
    simp only [hM, ContinuousMap.add_apply]
    rw [intervalIntegral.integral_add ((hc G).intervalIntegrable _ _) ((hc H).intervalIntegrable _ _)]
    ring
  have hM_smul : ∀ (a : ℂ) G, M (a • G) = a * M G := by
    intro a G
    simp only [hM, ContinuousMap.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hA_sub : ∀ N G H, A N (G - H) = A N G - A N H := fun N G H => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ H, hA_add, hA_smul]; ring
  have hM_sub : ∀ G H, M (G - H) = M G - M H := fun G H => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ H, hM_add, hM_smul]; ring
  -- `|A_N G| ≤ ‖G‖` and `|M G| ≤ ‖G‖`
  have hA_le : ∀ N G, ‖A N G‖ ≤ ‖G‖ := by
    intro N G
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [hA]
    · simp only [hA, norm_mul, norm_inv, Complex.norm_natCast]
      have hs : ‖∑ j ∈ Finset.range N, G ((θ₀ + j * α : ℝ) : AddCircle (2 * Real.pi))‖ ≤ N * ‖G‖ := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun j _ => G.norm_coe_le_norm _).trans ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      calc (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.range N, G ((θ₀ + j * α : ℝ) : AddCircle (2 * Real.pi))‖
          ≤ (N : ℝ)⁻¹ * (N * ‖G‖) := by gcongr
        _ = ‖G‖ := by field_simp
  have hM_le : ∀ G, ‖M G‖ ≤ ‖G‖ := by
    intro G
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
      (C := ‖G‖) (f := fun θ : ℝ => G (θ : AddCircle (2 * Real.pi))) (fun θ _ => G.norm_coe_le_norm _)
    rw [sub_zero, abs_of_pos hπ] at hb
    simp only [hM, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hπ.le)]
    calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, G (θ : AddCircle (2 * Real.pi))‖
        ≤ (2 * Real.pi)⁻¹ * (‖G‖ * (2 * Real.pi)) := by gcongr
      _ = ‖G‖ := by field_simp
  -- the Fourier modes
  have hval : ∀ (n : ℤ) (θ : ℝ), fourier n (θ : AddCircle (2 * Real.pi)) = rot (n * θ) := by
    intro n θ
    rw [fourier_coe_apply, rot]
    congr 1
    push_cast
    field_simp
  have hfour : ∀ n : ℤ, Tendsto (fun N => A N (fourier n)) atTop (𝓝 (M (fourier n))) := by
    intro n
    have hM0 : M (fourier n) = if n = 0 then 1 else 0 := by
      simp only [hM, hval]
      rw [Axis.integral_rot_int]
      split_ifs
      · push_cast; field_simp
      · rw [mul_zero]
    by_cases hn : n = 0
    · subst hn
      rw [hM0]
      simp only [↓reduceIte]
      have e : ∀ N : ℕ, 1 ≤ N → A N (fourier 0) = 1 := fun N hN => by
        simp only [hA, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
        field_simp
      exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun N hN => (e N hN).symm⟩)
    · rw [hM0]
      simp only [hn, ↓reduceIte]
      have e : ∀ N, A N (fourier n) =
          (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, rot (n * θ₀) * rot (n * α) ^ j := fun N => by
        simp only [hA, hval]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (n : ℝ) * (θ₀ + j * α) = n * θ₀ + j * (n * α) by ring, Axis.rot_add', rot_nat_mul]
      simp only [e]
      exact tendsto_avg_geom (norm_rot _) (hα n hn) _
  -- the trigonometric polynomials
  have hspan : ∀ P ∈ Submodule.span ℂ (Set.range (@fourier (2 * Real.pi))),
      Tendsto (fun N => A N P) atTop (𝓝 (M P)) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact hfour n
    | zero =>
      have h0 : ∀ N, A N 0 = 0 := fun N => by simp [hA]
      have h0' : M 0 = 0 := by simp [hM]
      simp only [h0, h0']
      exact tendsto_const_nhds
    | add x y _ _ hx hy =>
      simp only [hA_add, hM_add]
      exact hx.add hy
    | smul a x _ hx =>
      simp only [hA_smul, hM_smul]
      exact hx.const_mul a
  -- density of the trigonometric polynomials
  have hdense : ∀ ε > 0, ∃ P ∈ Submodule.span ℂ (Set.range (@fourier (2 * Real.pi))), dist F P < ε := by
    intro ε hε
    have hmem : F ∈ closure ((Submodule.span ℂ (Set.range (@fourier (2 * Real.pi))) :
        Set C(AddCircle (2 * Real.pi), ℂ))) := by
      rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
      trivial
    exact Metric.mem_closure_iff.1 hmem ε hε
  have hFl : Tendsto (fun N => A N F) atTop (𝓝 (M F)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨P, hP, hFP⟩ := hdense (ε / 3) (by positivity)
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hspan P hP) (ε / 3) (by positivity)
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 := hA_le N (F - P)
    have h2 := hM_le (F - P)
    have h3 := hN₀ N hN
    rw [dist_eq_norm] at hFP h3 ⊢
    have e : A N F - M F = A N (F - P) + (A N P - M P) - M (F - P) := by
      rw [hA_sub, hM_sub]; ring
    rw [e]
    calc ‖A N (F - P) + (A N P - M P) - M (F - P)‖
        ≤ ‖A N (F - P)‖ + ‖A N P - M P‖ + ‖M (F - P)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ < ε := by linarith
  -- back to `f`
  have hAF : ∀ N, A N F = (((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (θ₀ + j * α) : ℝ) : ℂ) := by
    intro N
    simp only [hA, hF]
    push_cast
    rfl
  have hMF : M F = (((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ : ℝ) : ℂ) := by
    simp only [hM, hF]
    rw [intervalIntegral.integral_ofReal]
    push_cast
    ring
  have := (Complex.continuous_re.tendsto _).comp hFl
  simp only [Function.comp_def, hAF, hMF, Complex.ofReal_re] at this
  exact this

/-- `Q_θ` only depends on `θ` modulo `2π`. -/
lemma Q_periodic (T : Table) (g : ℂ → ℝ) (θ : ℝ) : T.Q g (θ + 2 * Real.pi) = T.Q g θ := by
  funext q
  simp only [Table.Q, rot_add_two_pi]

/-- `w_AC` is `2π`-periodic. -/
lemma wob_periodic (T : Table) (g : ℂ → ℝ) (L : ℝ) :
    Function.Periodic (T.wob g L) (2 * Real.pi) := by
  intro θ
  have htilt : T.tilt g L (θ + 2 * Real.pi) = T.tilt g L θ := by
    unfold Table.tilt
    rw [Q_periodic]
  unfold Table.wob Table.cAC resid
  rw [htilt, rot_add_two_pi]

/-- **Remark 5.14 (a)**: along an irrational rotation, the ergodic averages of `w_AC` converge to
the mean of `w_AC`, which is the mean of `w_AC - F₀` (`integral_wob`): of order `L³`, and not `0`
in general (`integral_wob_trapezoid_pos`). -/
theorem tendsto_avg_wob {T : Table} {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L) (hs : T.SmallL L)
    {α : ℝ} (hα : ∀ k : ℤ, k ≠ 0 → rot (k * α) ≠ 1) (θ₀ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, T.wob g L (θ₀ + j * α)) atTop
      (𝓝 ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, T.wob g L θ)) :=
  tendsto_avg_of_irrational (Table.continuous_wob hg hs) (wob_periodic T g L) hα θ₀

end Wobbly
