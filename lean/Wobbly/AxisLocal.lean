import Wobbly.Axis
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Topology.TietzeExtension

open Complex ComplexConjugate MeasureTheory Filter Topology
open scoped ContDiff

/-!
# Proposition 4.13 (a): the local version

If the axis only moves in an open disc `U`, the terrain is only seen on the region `Ω` swept by the
feet. For every table (including the square), `F₀^v ≡ 0` for all `v ∈ U` forces the terrain to be
a paraboloid `a + b·x + c|x|²` on `Ω`.

The proof follows the paper. For a smooth compactly supported `f`, write `Van U k f` for
"`G_k[f] = 0` on `U`" (`k ∈ Z(f)` in the paper). Since `∂ G_k[f] = G_k[∂f]`, `Van U k f` implies
`Van U k (∂f)` and `Van U k (∂̄f)`, and the recurrence `k G_k[f] = r (G_{k-1}[∂f] - G_{k+1}[∂̄f])`
holds for every `f`.

* Step 1 (isolated modes): `van_isolated`;
* Step 2 (blocks of modes, induction on `b - a`): `van_block`;
* Step 3 (the modes `|k| ≥ 2`, with the simultaneous approximation `exists_pow_near_one`):
  `van_all_ns`; for the square, whose non-degenerate modes are the `k ≡ 2 mod 4`, an eigenvalue
  argument for `∂∂̄` instead: `van_sq`; both cases: `van_all`;
* Step 4 (the modes `0, ±1`, with the symmetry of second derivatives `dz_dzb_comm`): `center`,
  `paraboloid_core`;
* reduction to smooth terrains: `interp_local` (continuous extension of `g` from a compact part
  of `Ω` by Tietze's theorem, mollification, and limit through the values at four points).

* `paraboloid_core`: the smooth case;
* `paraboloid_of_F₀v_local`: **Proposition 4.13 (a)**;
* `paraboloid_of_F₀v`: **Proposition 4.13 (b)** (continuous terrains), and `affine_of_F₀v_all`
  (Lipschitz terrains);
* `F₀v_of_paraboloid`: the converse.
-/

namespace Wobbly

namespace Axis

variable {r : ℝ}

/-! ### Smooth functions with compact support -/

/-- Smooth functions with compact support. -/
def Good (f : ℂ → ℂ) : Prop := ContDiff ℝ ∞ f ∧ HasCompactSupport f

lemma good_c1 {f : ℂ → ℂ} (hf : Good f) : ContDiff ℝ 1 f :=
  hf.1.of_le (by exact_mod_cast le_top)

lemma good_bound {f : ℂ → ℂ} (hf : Good f) : ∃ L, ∀ x, ‖fderiv ℝ f x‖ ≤ L :=
  ((good_c1 hf).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hf.2.fderiv (𝕜 := ℝ))

lemma good_fderiv {f : ℂ → ℂ} (hf : Good f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.1.fderiv_right (m := ∞) (by simp)

lemma good_dz {f : ℂ → ℂ} (hf : Good f) : Good (dz f) := by
  have h1 := good_fderiv hf
  refine ⟨?_, ?_⟩
  · unfold dz
    exact ((h1.clm_apply contDiff_const).sub
      (contDiff_const.mul (h1.clm_apply contDiff_const))).div_const _
  · refine (hf.2.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ fun h0 => hx ?_
    simp [dz, h0]

lemma good_dzb {f : ℂ → ℂ} (hf : Good f) : Good (dzb f) := by
  have h1 := good_fderiv hf
  refine ⟨?_, ?_⟩
  · unfold dzb
    exact ((h1.clm_apply contDiff_const).add
      (contDiff_const.mul (h1.clm_apply contDiff_const))).div_const _
  · refine (hf.2.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ fun h0 => hx ?_
    simp [dzb, h0]

lemma good_dz_γ {f : ℂ → ℂ} (hf : Good f) (k : ℤ) (v : ℂ) : dz (γ r k f) v = γ r k (dz f) v := by
  obtain ⟨L, hL⟩ := good_bound hf
  exact dz_γ (good_c1 hf) hL k v

lemma good_dzb_γ {f : ℂ → ℂ} (hf : Good f) (k : ℤ) (v : ℂ) : dzb (γ r k f) v = γ r k (dzb f) v := by
  obtain ⟨L, hL⟩ := good_bound hf
  exact dzb_γ (good_c1 hf) hL k v

/-! ### Vanishing of a coefficient on an open set -/

variable (r) in
/-- `G_k[f] = 0` on `U`. -/
def Van (U : Set ℂ) (k : ℤ) (f : ℂ → ℂ) : Prop := ∀ v ∈ U, γ r k f v = 0

lemma fderiv_eq_zero_of_van {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ} (h : ∀ v ∈ U, G v = 0)
    {v : ℂ} (hv : v ∈ U) : fderiv ℝ G v = 0 := by
  have he : G =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem (hU.mem_nhds hv) fun w hw => h w hw
  rw [he.fderiv_eq]; simp

lemma van_dz {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {k : ℤ} (h : Van r U k f) :
    Van r U k (dz f) := fun v hv => by
  rw [← good_dz_γ hf]; unfold dz; rw [fderiv_eq_zero_of_van hU h hv]; simp

lemma van_dzb {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {k : ℤ} (h : Van r U k f) :
    Van r U k (dzb f) := fun v hv => by
  rw [← good_dzb_γ hf]; unfold dzb; rw [fderiv_eq_zero_of_van hU h hv]; simp

/-- Blocks of modes: if `G_{a-1}`, `G_{b+1}` and `G_{b+2}` vanish on `U` and `0 ∉ [a, b]`, then
`G_k` vanishes on `U` for `a ≤ k ≤ b`. -/
theorem van_block {U : Set ℂ} (hU : IsOpen U) (hr : r ≠ 0) :
    ∀ (n : ℕ) (f : ℂ → ℂ) (a b : ℤ), b - a = n → Good f → Van r U (a - 1) f →
      Van r U (b + 1) f → Van r U (b + 2) f → (∀ k : ℤ, a ≤ k → k ≤ b → k ≠ 0) →
      ∀ k : ℤ, a ≤ k → k ≤ b → Van r U k f := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  -- `G_k = 0` from the recurrence at `k`
  have kill : ∀ (f : ℂ → ℂ) (k : ℤ), Good f → k ≠ 0 → Van r U (k - 1) (dz f) →
      Van r U (k + 1) (dzb f) → Van r U k f := by
    intro f k hf hk h1 h2 v hv
    have e := γ_recurrence (r := r) (good_c1 hf) k v
    rw [h1 v hv, h2 v hv, sub_self, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_left (by exact_mod_cast hk)
  intro n
  induction n with
  | zero =>
    intro f a b hab hf ha hb1 _ h0 k hk1 hk2
    have hk : k = b := by omega
    subst hk
    apply kill f k hf (h0 k hk1 hk2)
    · rw [show k - 1 = a - 1 by omega]; exact van_dz hU hf ha
    · exact van_dzb hU hf hb1
  | succ n ih =>
    intro f a b hab hf ha hb1 hb2 h0
    -- `∂f` vanishes at `b` (recurrence at `b + 1`)
    have hdzb : Van r U b (dz f) := by
      intro v hv
      have e := γ_recurrence (r := r) (good_c1 hf) (b + 1) v
      rw [hb1 v hv, show b + 1 - 1 = b by ring, show b + 1 + 1 = b + 2 by ring,
        van_dzb hU hf hb2 v hv, sub_zero, mul_zero] at e
      exact ((mul_eq_zero.1 e.symm).resolve_left hr')
    -- the block `[a, b - 1]` for `∂f`
    have hdf := ih (dz f) a (b - 1) (by omega) (good_dz hf) (van_dz hU hf ha)
      (by rw [show b - 1 + 1 = b by ring]; exact hdzb)
      (by rw [show b - 1 + 2 = b + 1 by ring]; exact van_dz hU hf hb1)
      (fun k h1 h2 => h0 k h1 (by omega))
    -- hence `G_b[f] = 0`
    have hb : Van r U b f := by
      apply kill f b hf (h0 b (by omega) le_rfl)
      · exact hdf (b - 1) (by omega) le_rfl
      · exact van_dzb hU hf hb1
    have hf' := ih f a (b - 1) (by omega) hf ha (by rw [show b - 1 + 1 = b by ring]; exact hb)
      (by rw [show b - 1 + 2 = b + 1 by ring]; exact hb1) (fun k h1 h2 => h0 k h1 (by omega))
    intro k hk1 hk2
    rcases eq_or_lt_of_le hk2 with rfl | hlt
    · exact hb
    · exact hf' k hk1 (by omega)

/-! ### Second derivatives and conjugation -/

lemma hasFDerivAt_fderiv_apply {f : ℂ → ℂ} (hf : Good f) (u x : ℂ) :
    HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) := (good_fderiv hf).differentiable (by simp)
  have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  simpa using this

lemma dz_of_hasFDerivAt {G : ℂ → ℂ} {D : ℂ →L[ℝ] ℂ} {v : ℂ} (h : HasFDerivAt G D v) :
    dz G v = (D 1 - I * D I) / 2 := by rw [dz, h.fderiv]

lemma dzb_of_hasFDerivAt {G : ℂ → ℂ} {D : ℂ →L[ℝ] ℂ} {v : ℂ} (h : HasFDerivAt G D v) :
    dzb G v = (D 1 + I * D I) / 2 := by rw [dzb, h.fderiv]

/-- `∂∂̄f = ∂̄∂f` (symmetry of second derivatives). -/
lemma dz_dzb_comm {f : ℂ → ℂ} (hf : Good f) (x : ℂ) : dz (dzb f) x = dzb (dz f) x := by
  set D2 := fderiv ℝ (fderiv ℝ f) x
  have h1 : HasFDerivAt (dzb f) ((2 : ℂ)⁻¹ • ((D2.flip 1) + I • (D2.flip I))) x := by
    have := ((hasFDerivAt_fderiv_apply hf 1 x).add
      ((hasFDerivAt_fderiv_apply hf I x).const_smul I)).const_smul ((2 : ℂ)⁻¹)
    unfold dzb
    convert this using 1
    ext y; simp [smul_eq_mul]; ring
  have h2 : HasFDerivAt (dz f) ((2 : ℂ)⁻¹ • ((D2.flip 1) - I • (D2.flip I))) x := by
    have := ((hasFDerivAt_fderiv_apply hf 1 x).sub
      ((hasFDerivAt_fderiv_apply hf I x).const_smul I)).const_smul ((2 : ℂ)⁻¹)
    unfold dz
    convert this using 1
    ext y; simp [smul_eq_mul]; ring
  have hs : D2 1 I = D2 I 1 :=
    ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) (hf.1.contDiffAt (x := x)) (by simp) 1 I
  rw [dz_of_hasFDerivAt h1, dzb_of_hasFDerivAt h2]
  simp only [add_apply,
    sub_apply, smul_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  rw [hs]; ring

lemma dzb_conj {h : ℂ → ℂ} {x : ℂ} (hd : DifferentiableAt ℝ h x) :
    dzb (fun y => conj (h y)) x = conj (dz h x) := by
  have : HasFDerivAt (fun y => conj (h y)) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x)) x :=
    (Complex.conjCLE.hasFDerivAt).comp x hd.hasFDerivAt
  rw [dzb_of_hasFDerivAt this, dz]
  simp [map_div₀, map_sub, map_mul, map_ofNat]

lemma fderiv_eq_zero_of_dz {G : ℂ → ℂ} {v : ℂ} (h1 : dz G v = 0) (h2 : dzb G v = 0) :
    fderiv ℝ G v = 0 := by
  ext1 h
  rw [clm_eq (fderiv ℝ G v) h]
  unfold dz at h1; unfold dzb at h2
  rw [h1, h2]; simp

lemma const_of_dz {U : Set ℂ} (hUc : Convex ℝ U) (hU : IsOpen U) {G : ℂ → ℂ}
    (hd : Differentiable ℝ G) (h1 : ∀ v ∈ U, dz G v = 0) (h2 : ∀ v ∈ U, dzb G v = 0)
    {v w : ℂ} (hv : v ∈ U) (hw : w ∈ U) : G v = G w :=
  hUc.is_const_of_fderivWithin_eq_zero hd.differentiableOn
    (fun x hx => by rw [fderivWithin_of_isOpen hU hx]; exact fderiv_eq_zero_of_dz (h1 x hx) (h2 x hx))
    hv hw

/-! ### The modes `0, ±1` -/

/-- If `G_{±2}` and `G_3` vanish on a convex open set `U`, then `G₀` is a paraboloid on `U`, and
`G_{±1}` are the corresponding coefficients. -/
theorem center (hr : 0 < r) {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) {v₀ : ℂ} (hv₀ : v₀ ∈ U)
    {f : ℂ → ℂ} (hf : Good f) (hreal : ∀ x, conj (f x) = f x)
    (h2 : Van r U 2 f) (h3 : Van r U 3 f) :
    ∃ (α β : ℂ) (c : ℝ), ∀ v ∈ U, γ r 0 f v = α + β * v + conj β * conj v + c * v * conj v ∧
      γ r 1 f v = r * (β + c * conj v) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc1 := good_c1 hf
  have hdf := good_dz hf
  have hdbf := good_dzb hf
  have hdiff : ∀ {g : ℂ → ℂ}, Good g → ∀ k, Differentiable ℝ (γ r k g) := fun hg k => by
    obtain ⟨L, hL⟩ := good_bound hg; exact differentiable_γ (good_c1 hg) hL k
  -- `G₁ = r ∂G₀`
  have hG1 : ∀ v ∈ U, γ r 1 f v = r * γ r 0 (dz f) v := fun v hv => by
    have e := γ_recurrence (r := r) hc1 1 v
    rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num,
      van_dzb hU hf h2 v hv] at e
    simpa using e
  -- `∂G₁ = 0`
  have hv1 : Van r U 1 (dz f) := fun v hv => by
    have e := γ_recurrence (r := r) hc1 2 v
    rw [h2 v hv, show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) + 1 = 3 by norm_num,
      van_dzb hU hf h3 v hv, sub_zero, mul_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left hr'
  -- `∂²G₀ = 0`
  have hv0 : Van r U 0 (dz (dz f)) := fun v hv => by
    have e := γ_recurrence (r := r) (good_c1 hdf) 1 v
    rw [hv1 v hv, show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num,
      van_dzb hU hdf (van_dz hU hf h2) v hv, sub_zero, mul_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left hr'
  -- `w = ∂̄∂f` is real
  set w := dzb (dz f) with hw
  have hdz_conj : dz f = fun y => conj (dzb f y) := funext fun y =>
    dz_eq_conj_dzb hreal ((hc1.differentiable one_ne_zero) y)
  have hwreal : ∀ x, conj (w x) = w x := fun x => by
    have e : w x = conj (dz (dzb f) x) := by
      rw [hw, hdz_conj, dzb_conj ((good_c1 hdbf).differentiable one_ne_zero x)]
    calc conj (w x) = conj (conj (dz (dzb f) x)) := by rw [e]
      _ = dz (dzb f) x := Complex.conj_conj _
      _ = w x := by rw [dz_dzb_comm hf]
  -- `C = ∂̄∂G₀ = G₀[w]` is a real constant on `U`
  set C := γ r 0 w with hC
  have hCreal : ∀ v, conj (C v) = C v := fun v => by
    have := γ_neg (r := r) hwreal 0 v; simp only [neg_zero] at this; rw [hC, ← this]
  have hgw : Good w := good_dzb hdf
  have hdzC : ∀ v ∈ U, dz C v = 0 := fun v hv => by
    rw [hC, good_dz_γ hgw, hw, funext (dz_dzb_comm hdf)]
    exact van_dzb hU (good_dz hdf) hv0 v hv
  have hdzbC : ∀ v ∈ U, dzb C v = 0 := fun v hv => by
    have := dz_eq_conj_dzb hCreal ((hdiff hgw 0) v)
    rw [hdzC v hv] at this
    have := congrArg conj this; rw [Complex.conj_conj, map_zero] at this; exact this.symm
  set c : ℝ := (C v₀).re
  have hCc : ∀ v ∈ U, C v = c := fun v hv => by
    rw [show C v = C v₀ from const_of_dz (G := C) hUc hU (hdiff hgw 0) hdzC hdzbC hv hv₀]
    exact (Complex.conj_eq_iff_re.1 (hCreal v₀)).symm
  -- `A = ∂G₀ = β + c v̄` on `U`
  set A := γ r 0 (dz f) with hA
  have hAd : Differentiable ℝ A := hdiff hdf 0
  set B : ℂ → ℂ := fun v => A v - c * conj v
  have hB : ∀ v, HasFDerivAt B (fderiv ℝ A v - (c : ℂ) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) v :=
    fun v => by
      have := (hAd v).hasFDerivAt.sub ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_smul (c : ℂ))
      convert this using 1
      funext y; simp [B]
  have hBc : ∀ v ∈ U, B v = B v₀ := fun v hv => by
    refine const_of_dz hUc hU (fun x => (hB x).differentiableAt) ?_ ?_ hv hv₀
    · intro x hx
      rw [dz_of_hasFDerivAt (hB x)]
      have := hdzC x hx
      rw [hC, good_dz_γ hgw, hw] at this
      have e : dz A x = 0 := by rw [hA, good_dz_γ hdf]; exact hv0 x hx
      unfold dz at e
      simp only [sub_apply, smul_apply,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul]
      linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring_nf)) e
    · intro x hx
      rw [dzb_of_hasFDerivAt (hB x)]
      have e : dzb A x = c := by rw [hA, good_dzb_γ hdf, ← hw]; exact hCc x hx
      unfold dzb at e
      simp only [sub_apply, smul_apply,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul]
      linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring_nf)) e
  set β := B v₀
  have hAβ : ∀ v ∈ U, A v = β + c * conj v := fun v hv => by
    have := hBc v hv; simp only [B] at this; linear_combination this
  -- `G₀ - q` is constant on `U`
  set Φ := γ r 0 f with hΦ
  have hΦd : Differentiable ℝ Φ := hdiff hf 0
  have hΦreal : ∀ v, conj (Φ v) = Φ v := fun v => by
    have := γ_neg (r := r) hreal 0 v; simp only [neg_zero] at this; rw [hΦ, ← this]
  set q : ℂ → ℂ := fun v => β * v + conj β * conj v + c * v * conj v
  have hq : ∀ v, HasFDerivAt q (β • ContinuousLinearMap.id ℝ ℂ
      + conj β • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      + (c : ℂ) • (v • (Complex.conjCLE : ℂ →L[ℝ] ℂ) + conj v • ContinuousLinearMap.id ℝ ℂ)) v :=
    fun v => by
      have hid := hasFDerivAt_id (𝕜 := ℝ) v
      have hcj := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := v)
      have := ((hid.const_smul β).add (hcj.const_smul (conj β))).add
        ((hid.mul hcj).const_smul (c : ℂ))
      convert this using 1
      · funext x; simp [q, smul_eq_mul]; ring
      · simp
  set E : ℂ → ℂ := fun v => Φ v - q v
  have hE : ∀ v, HasFDerivAt E (fderiv ℝ Φ v - _) v := fun v => (hΦd v).hasFDerivAt.sub (hq v)
  have hEc : ∀ v ∈ U, E v = E v₀ := fun v hv => by
    refine const_of_dz hUc hU (fun x => (hE x).differentiableAt) ?_ ?_ hv hv₀
    · intro x hx
      rw [dz_of_hasFDerivAt (hE x)]
      have e : dz Φ x = β + c * conj x := by rw [hΦ, good_dz_γ hf, ← hA]; exact hAβ x hx
      unfold dz at e
      simp only [sub_apply, add_apply,
        smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
        Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul]
      linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring_nf)) e
    · intro x hx
      rw [dzb_of_hasFDerivAt (hE x)]
      have e0 : dz Φ x = β + c * conj x := by rw [hΦ, good_dz_γ hf, ← hA]; exact hAβ x hx
      have e1 := dz_eq_conj_dzb hΦreal (hΦd x)
      have e : dzb Φ x = conj β + c * x := by
        have := congrArg conj e1
        rw [Complex.conj_conj, e0] at this
        rw [← this]; simp [map_add, map_mul, Complex.conj_ofReal]
      unfold dzb at e
      simp only [sub_apply, add_apply,
        smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
        Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul]
      linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring_nf)) e
  refine ⟨E v₀, β, c, fun v hv => ⟨?_, ?_⟩⟩
  · have := hEc v hv; simp only [E, q] at this; linear_combination this
  · rw [hG1 v hv, hAβ v hv]

/-! ### Paraboloids -/

/-- The paraboloid `a + b x + b' x̄ + c x x̄`. -/
def parab (a b b' c : ℂ) (x : ℂ) : ℂ := a + b * x + b' * conj x + c * x * conj x

lemma continuous_parab (a b b' c : ℂ) : Continuous (parab a b b' c) := by
  unfold parab
  have hc := Complex.continuous_conj
  fun_prop

lemma rot_mul_rot_neg (φ : ℝ) : rot φ * rot (-φ) = 1 := by
  rw [← rot_add', add_neg_cancel, rot_zero']

/-- The Fourier coefficients of a paraboloid on the circle of radius `r` centred at `v`. -/
lemma γ_parab (a b b' c : ℂ) (k : ℤ) (v : ℂ) :
    γ r k (parab a b b' c) v =
      (if k = 0 then (2 * Real.pi : ℂ) * (a + b * v + b' * conj v + c * (v * conj v + r ^ 2)) else 0)
      + (if k = 1 then (2 * Real.pi : ℂ) * (r * (b + c * conj v)) else 0)
      + (if k = -1 then (2 * Real.pi : ℂ) * (r * (b' + c * v)) else 0) := by
  have e : ∀ φ : ℝ, rot (-(k : ℝ) * φ) * parab a b b' c (v + r * rot φ) =
      (a + b * v + b' * conj v + c * (v * conj v + r ^ 2)) * rot (((-k : ℤ) : ℝ) * φ)
        + r * (b + c * conj v) * rot (((1 - k : ℤ) : ℝ) * φ)
        + r * (b' + c * v) * rot (((-1 - k : ℤ) : ℝ) * φ) := by
    intro φ
    have r1 : rot (((1 - k : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) * rot φ := by
      rw [← rot_add']; congr 1; push_cast; ring
    have r2 : rot (((-1 - k : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) * rot (-φ) := by
      rw [← rot_add']; congr 1; push_cast; ring
    have r0 : rot (((-k : ℤ) : ℝ) * φ) = rot (-(k : ℝ) * φ) := by congr 1; push_cast; ring
    have h1 := rot_mul_rot_neg φ
    rw [r1, r2, r0]
    simp only [parab, map_add, map_mul, Complex.conj_ofReal, conj_rot]
    linear_combination (c * r ^ 2 * rot (-(k : ℝ) * φ)) * h1
  have ci : ∀ j : ℤ, IntervalIntegrable (fun φ : ℝ => rot ((j : ℝ) * φ)) volume 0 (2 * Real.pi) :=
    fun j => (continuous_rot.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  unfold γ
  simp_rw [e]
  rw [intervalIntegral.integral_add (((ci _).const_mul _).add ((ci _).const_mul _)) ((ci _).const_mul _),
    intervalIntegral.integral_add ((ci _).const_mul _) ((ci _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_rot_int, integral_rot_int, integral_rot_int]
  by_cases k0 : k = 0
  · subst k0; simp; ring
  by_cases k1 : k = 1
  · subst k1; simp; ring
  by_cases km : k = -1
  · subst km; simp; ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right k0,
      ite_eq_right k1, ite_eq_right km]
    simp

/-- **Proposition 4.13, smooth core**: if `f` is real, smooth with compact support, and its
coefficients `G_k`, `|k| ≥ 2`, vanish on a convex open set `U`, then `f` is a paraboloid on every
circle of radius `r` centred in `U`. -/
theorem paraboloid_core (hr : 0 < r) {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) {v₀ : ℂ}
    (hv₀ : v₀ ∈ U) {f : ℂ → ℂ} (hf : Good f) (hreal : ∀ x, conj (f x) = f x)
    (hvan : ∀ k : ℤ, 2 ≤ |k| → Van r U k f) :
    ∃ (a b : ℂ) (c : ℝ), ∀ v ∈ U, ∀ θ : ℝ,
      f (v + r * rot θ) = parab a b (conj b) c (v + r * rot θ) := by
  obtain ⟨α, β, c, h⟩ := center hr hU hUc hv₀ hf hreal (hvan 2 (by norm_num)) (hvan 3 (by norm_num))
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  set c0 : ℝ := c / (2 * Real.pi)
  set b0 : ℂ := β / (2 * Real.pi)
  set a0 : ℂ := α / (2 * Real.pi) - c0 * r ^ 2
  have hcb : conj b0 = conj β / (2 * Real.pi) := by
    simp only [b0, map_div₀]; congr 1; simp [Complex.conj_ofReal, map_ofNat]
  set P := parab a0 b0 (conj b0) c0
  have hc0 : ((c0 : ℝ) : ℂ) = (c : ℂ) / (2 * Real.pi) := by simp [c0]
  refine ⟨a0, b0, c0, fun v hv θ => ?_⟩
  have hcoef : ∀ n : ℤ, γ r n f v = γ r n P v := by
    intro n
    rw [γ_parab]
    by_cases n0 : n = 0
    · subst n0; simp only [ite_true, show (0 : ℤ) ≠ 1 by norm_num, show (0 : ℤ) ≠ -1 by norm_num,
        ite_false, add_zero]
      rw [(h v hv).1, hcb, hc0]; simp only [a0, b0, hc0]; field_simp; ring
    by_cases n1 : n = 1
    · subst n1; simp only [show (1 : ℤ) ≠ 0 by norm_num, show (1 : ℤ) ≠ -1 by norm_num, ite_true,
        ite_false, zero_add, add_zero]
      rw [(h v hv).2, hc0]; simp only [b0]; field_simp
    by_cases nm : n = -1
    · subst nm; simp only [show (-1 : ℤ) ≠ 0 by norm_num, show (-1 : ℤ) ≠ 1 by norm_num, ite_true,
        ite_false, zero_add]
      have e := γ_neg (r := r) hreal 1 v
      rw [e, (h v hv).2, hcb, hc0]
      simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
    · rw [ite_eq_right n0, ite_eq_right n1, ite_eq_right nm, hvan n (by rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩ <;> omega) v hv]; simp
  set ψ : ℝ → ℂ := fun φ => f (v + r * rot φ) - P (v + r * rot φ)
  have hψc : Continuous ψ :=
    (continuous_circle (good_c1 hf).continuous v).sub (continuous_circle (continuous_parab _ _ _ _) v)
  have hψp : Function.Periodic ψ (2 * Real.pi) := fun φ => by
    simp only [ψ]
    rw [rot_add', show (2 * Real.pi : ℝ) = ((1 : ℤ) : ℝ) * (2 * Real.pi) by simp, rot_int_two_pi,
      mul_one]
  have hc : ∀ n : ℤ, ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = 0 := by
    intro n
    have e : ∫ φ in (0 : ℝ)..2 * Real.pi, ψ φ * rot (-(n : ℝ) * φ) = γ r n f v - γ r n P v := by
      unfold γ
      rw [← intervalIntegral.integral_sub]
      · congr 1; ext φ; simp only [ψ]; ring
      · exact ((continuous_rotk n).mul (continuous_circle (good_c1 hf).continuous v)).intervalIntegrable _ _
      · exact ((continuous_rotk n).mul (continuous_circle (continuous_parab _ _ _ _) v)).intervalIntegrable _ _
    rw [e, hcoef]; exact sub_self _
  have := eq_zero_of_fourier hψc hψp hc θ
  simp only [ψ] at this
  exact sub_eq_zero.1 this

/-! ### Non-degenerate modes -/

lemma van_isolated {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {k : ℤ}
    (hk : k ≠ 0) (h1 : Van r U (k - 1) f) (h2 : Van r U (k + 1) f) : Van r U k f := by
  intro v hv
  have e := γ_recurrence (r := r) (good_c1 hf) k v
  rw [van_dz hU hf h1 v hv, van_dzb hU hf h2 v hv, sub_self, mul_zero] at e
  exact (mul_eq_zero.1 e).resolve_left (by exact_mod_cast hk)

lemma van_neg {U : Set ℂ} {f : ℂ → ℂ} (hreal : ∀ x, conj (f x) = f x) {k : ℤ} (h : Van r U k f) :
    Van r U (-k) f := fun v hv => by rw [γ_neg hreal k v, h v hv, map_zero]

/-- Simultaneous recurrence: some arbitrarily large power of four unit complex numbers is close
to `1`. -/
lemma exists_pow_near_one {A B C D : ℂ} (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hD : ‖D‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n ≥ N, ‖A ^ n - 1‖ < ε ∧ ‖B ^ n - 1‖ < ε ∧ ‖C ^ n - 1‖ < ε ∧ ‖D ^ n - 1‖ < ε := by
  set x : ℕ → ℂ × ℂ × ℂ × ℂ := fun n => (A ^ n, B ^ n, C ^ n, D ^ n)
  have hx : ∀ n, x n ∈ Metric.closedBall (0 : ℂ × ℂ × ℂ × ℂ) 1 := fun n => by
    simp [x, norm_pow, hA, hB, hC, hD]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ × ℂ × ℂ × ℂ) 1).tendsto_subseq hx
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (by positivity)
  have h1 := hJ J le_rfl
  have h2 := hJ (N + 1 + J) (by omega)
  have hd : dist (x (φ (N + 1 + J))) (x (φ J)) < ε := by
    have := dist_triangle_right (x (φ (N + 1 + J))) (x (φ J)) a
    simp only [Function.comp] at h1 h2
    linarith
  have hgrow := hφ.add_le_nat (N + 1) J
  obtain ⟨n, hjn⟩ : ∃ n, φ (N + 1 + J) = φ J + n := ⟨φ (N + 1 + J) - φ J, by omega⟩
  have key : ∀ E : ℂ, ‖E‖ = 1 → ‖E ^ n - 1‖ = dist (E ^ φ (N + 1 + J)) (E ^ φ J) := fun E hE => by
    rw [dist_eq_norm, hjn, pow_add, ← mul_sub_one, norm_mul, norm_pow, hE, one_pow, one_mul]
  have d1 : dist (A ^ φ (N + 1 + J)) (A ^ φ J) ≤ dist (x (φ (N + 1 + J))) (x (φ J)) := by
    simp only [x, Prod.dist_eq]; exact le_max_left _ _
  have d2 : dist (B ^ φ (N + 1 + J)) (B ^ φ J) ≤ dist (x (φ (N + 1 + J))) (x (φ J)) := by
    simp only [x, Prod.dist_eq]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have d3 : dist (C ^ φ (N + 1 + J)) (C ^ φ J) ≤ dist (x (φ (N + 1 + J))) (x (φ J)) := by
    simp only [x, Prod.dist_eq]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have d4 : dist (D ^ φ (N + 1 + J)) (D ^ φ J) ≤ dist (x (φ (N + 1 + J))) (x (φ J)) := by
    simp only [x, Prod.dist_eq]
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨n, by omega, ?_, ?_, ?_, ?_⟩
  · rw [key A hA]; linarith
  · rw [key B hB]; linarith
  · rw [key C hC]; linarith
  · rw [key D hD]; linarith

lemma m_shift (F : Feet) {n : ℕ} {ε : ℝ} (hA : ‖F.A ^ n - 1‖ < ε) (hB : ‖F.B ^ n - 1‖ < ε)
    (hC : ‖F.C ^ n - 1‖ < ε) (hD : ‖F.D ^ n - 1‖ < ε) (k : ℕ) :
    ‖F.m (n + k) - F.m k‖ < 2 * ε := by
  have e : F.m (n + k) - F.m k = -((F.τ : ℂ) * F.A ^ k * (F.A ^ n - 1)
      - (F.μ : ℂ) * F.B ^ k * (F.B ^ n - 1) + ((1 - F.τ : ℝ) : ℂ) * F.C ^ k * (F.C ^ n - 1)
      - ((1 - F.μ : ℝ) : ℂ) * F.D ^ k * (F.D ^ n - 1)) := by
    simp only [Feet.m, pow_add]; ring
  have nt : ‖(F.τ : ℂ)‖ = F.τ := by rw [Complex.norm_real, Real.norm_of_nonneg F.τ0.le]
  have nm : ‖(F.μ : ℂ)‖ = F.μ := by rw [Complex.norm_real, Real.norm_of_nonneg F.μ0.le]
  have nt' : ‖((1 - F.τ : ℝ) : ℂ)‖ = 1 - F.τ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [F.τ1])]
  have nm' : ‖((1 - F.μ : ℝ) : ℂ)‖ = 1 - F.μ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [F.μ1])]
  have b : ∀ (c : ℂ) (E : ℂ), ‖E‖ = 1 → ‖E ^ n - 1‖ < ε → 0 < ‖c‖ →
      ‖c * E ^ k * (E ^ n - 1)‖ < ‖c‖ * ε := fun c E hE h hc => by
    rw [norm_mul, norm_mul, norm_pow, hE, one_pow, mul_one]
    exact mul_lt_mul_of_pos_left h hc
  have t1 := b _ _ F.nA hA (by rw [nt]; exact F.τ0)
  have t2 := b _ _ F.nB hB (by rw [nm]; exact F.μ0)
  have t3 := b _ _ F.nC hC (by rw [nt']; linarith [F.τ1])
  have t4 := b _ _ F.nD hD (by rw [nm']; linarith [F.μ1])
  rw [nt] at t1; rw [nm] at t2; rw [nt'] at t3; rw [nm'] at t4
  rw [e, norm_neg]
  set X1 := (F.τ : ℂ) * F.A ^ k * (F.A ^ n - 1)
  set X2 := (F.μ : ℂ) * F.B ^ k * (F.B ^ n - 1)
  set X3 := ((1 - F.τ : ℝ) : ℂ) * F.C ^ k * (F.C ^ n - 1)
  set X4 := ((1 - F.μ : ℝ) : ℂ) * F.D ^ k * (F.D ^ n - 1)
  have n1 := norm_sub_le (X1 - X2 + X3) X4
  have n2 := norm_add_le (X1 - X2) X3
  have n3 := norm_sub_le X1 X2
  nlinarith

/-! ### The square

For the square, `m(k) ≠ 0` exactly for `k ≡ 2 mod 4` (`m_sq`), so `Z(f)` contains no two
consecutive modes and Step 3 does not apply. Instead: if `m - 2, m + 2 ∈ Z(f)`, the recurrence at
`m - 1`, `m`, `m + 1` gives `(m² - 1) G_m[f] = -2r² G_m[∂∂̄f]` (`sq_eig`), so `G_m[f]` is an
eigenfunction of `∂∂̄`, with an eigenvalue which depends on `m`; comparing `m` and `m + 4` gives
`G_m[∂²f] = 0` (`sq_dz_dz`), then `G_m[f] = 0` (`sq_van`), and all the modes `k ≥ 2` vanish
(`van_sq`). -/

/-- The recurrence at `k` when `k + 1 ∈ Z(f)`. -/
lemma rec_up {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {k : ℤ}
    (h : Van r U (k + 1) f) {v : ℂ} (hv : v ∈ U) :
    (k : ℂ) * γ r k f v = r * γ r (k - 1) (dz f) v := by
  have e := γ_recurrence (r := r) (good_c1 hf) k v
  rwa [van_dzb hU hf h v hv, sub_zero] at e

/-- The recurrence at `k` when `k - 1 ∈ Z(f)`. -/
lemma rec_down {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {k : ℤ}
    (h : Van r U (k - 1) f) {v : ℂ} (hv : v ∈ U) :
    (k : ℂ) * γ r k f v = -(r * γ r (k + 1) (dzb f) v) := by
  have e := γ_recurrence (r := r) (good_c1 hf) k v
  rwa [van_dz hU hf h v hv, zero_sub, mul_neg] at e

/-- The recurrence at `k` when `k ∈ Z(f)`. -/
lemma rec_mid (hr : r ≠ 0) {U : Set ℂ} {f : ℂ → ℂ} (hf : Good f) {k : ℤ} (h : Van r U k f)
    {v : ℂ} (hv : v ∈ U) : γ r (k - 1) (dz f) v = γ r (k + 1) (dzb f) v := by
  have e := γ_recurrence (r := r) (good_c1 hf) k v
  rw [h v hv, mul_zero] at e
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  exact sub_eq_zero.1 ((mul_eq_zero.1 e.symm).resolve_left hr')

lemma dzb_dz {f : ℂ → ℂ} (hf : Good f) : dzb (dz f) = dz (dzb f) :=
  funext fun x => (dz_dzb_comm hf x).symm

/-- If `m - 2, m + 2 ∈ Z(f)`, then `G_m[f]` is an eigenfunction of `∂∂̄`:
`(m² - 1) G_m[f] = -2r² G_m[∂∂̄f]`. -/
lemma sq_eig {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {m : ℤ}
    (hm : m ≠ 0) (h1 : Van r U (m - 2) f) (h2 : Van r U (m + 2) f) {v : ℂ} (hv : v ∈ U) :
    ((m : ℂ) ^ 2 - 1) * γ r m f v = -(2 * (r : ℂ) ^ 2 * γ r m (dz (dzb f)) v) := by
  have e1 := γ_recurrence (r := r) (good_c1 hf) m v
  have e2 := rec_down hU (good_dz hf) (k := m - 1)
    (by rw [show m - 1 - 1 = m - 2 by ring]; exact van_dz hU hf h1) hv
  have e3 := rec_up hU (good_dzb hf) (k := m + 1)
    (by rw [show m + 1 + 1 = m + 2 by ring]; exact van_dzb hU hf h2) hv
  rw [show m - 1 + 1 = m by ring, dzb_dz hf] at e2
  rw [show m + 1 - 1 = m by ring] at e3
  push_cast at e2 e3
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  apply mul_left_cancel₀ hm'
  linear_combination ((m : ℂ) ^ 2 - 1) * e1 + r * ((m : ℂ) + 1) * e2 - r * ((m : ℂ) - 1) * e3

/-- If `m + 2 ∈ Z(f)`, then `(m + 3) G_m[∂²f] = -(m + 1) G_{m+4}[∂̄²f]`. -/
lemma sq_shift (hr : r ≠ 0) {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {m : ℤ}
    (h : Van r U (m + 2) f) {v : ℂ} (hv : v ∈ U) :
    ((m : ℂ) + 3) * γ r m (dz (dz f)) v = -(((m : ℂ) + 1) * γ r (m + 4) (dzb (dzb f)) v) := by
  have e1 := rec_up hU (good_dz hf) (k := m + 1)
    (by rw [show m + 1 + 1 = m + 2 by ring]; exact van_dz hU hf h) hv
  have e2 := rec_down hU (good_dzb hf) (k := m + 3)
    (by rw [show m + 3 - 1 = m + 2 by ring]; exact van_dzb hU hf h) hv
  have e3 := rec_mid hr hf h hv
  rw [show m + 1 - 1 = m by ring] at e1
  rw [show m + 3 + 1 = m + 4 by ring] at e2
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at e3
  push_cast at e1 e2
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  apply mul_left_cancel₀ hr'
  linear_combination -((m : ℂ) + 3) * e1 + ((m : ℂ) + 1) * e2
    + ((m : ℂ) + 1) * ((m : ℂ) + 3) * e3

/-- If `m ≥ 1` and `m - 2, m + 2, m + 6 ∈ Z(f)`, then `G_m[∂²f] = 0`: the eigenvalues of `∂∂̄`
for `m` and `m + 4` differ. -/
lemma sq_dz_dz (hr : r ≠ 0) {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {m : ℤ}
    (hm : 1 ≤ m) (h1 : Van r U (m - 2) f) (h2 : Van r U (m + 2) f) (h3 : Van r U (m + 6) f)
    {v : ℂ} (hv : v ∈ U) : γ r m (dz (dz f)) v = 0 := by
  have hb := good_dzb hf
  have hΔ := good_dz hb
  have c1 := sq_shift hr hU hf h2 hv
  have c2 := sq_shift hr hU hΔ (van_dz hU hb (van_dzb hU hf h2)) hv
  have k1 : dz (dz (dz (dzb f))) = dz (dzb (dz (dz f))) := by
    rw [dzb_dz (good_dz hf), dzb_dz hf]
  have k2 : dzb (dzb (dz (dzb f))) = dz (dzb (dzb (dzb f))) := by
    rw [dzb_dz hb, dzb_dz (good_dzb hb)]
  rw [k1, k2] at c2
  have d1 := sq_eig hU (good_dz (good_dz hf)) (m := m) (by omega)
    (van_dz hU (good_dz hf) (van_dz hU hf h1)) (van_dz hU (good_dz hf) (van_dz hU hf h2)) hv
  have d2 := sq_eig hU (good_dzb hb) (m := m + 4) (by omega)
    (by rw [show m + 4 - 2 = m + 2 by ring]; exact van_dzb hU hb (van_dzb hU hf h2))
    (by rw [show m + 4 + 2 = m + 6 by ring]; exact van_dzb hU hb (van_dzb hU hf h3)) hv
  push_cast at d2
  set a := γ r m (dz (dz f)) v
  set b := γ r (m + 4) (dzb (dzb f)) v
  have k3 : ((m : ℂ) + 1) * ((m : ℂ) + 3) * (((m : ℂ) - 1) * a + ((m : ℂ) + 5) * b) = 0 := by
    linear_combination ((m : ℂ) + 3) * d1 + ((m : ℂ) + 1) * d2 - 2 * (r : ℂ) ^ 2 * c2
  have h13 : ((m : ℂ) + 1) * ((m : ℂ) + 3) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show m + 1 ≠ 0 by omega))
      (by exact_mod_cast (show m + 3 ≠ 0 by omega))
  have k4 := (mul_eq_zero.1 k3).resolve_left h13
  have k5 : (8 * ((m : ℂ) + 2)) * a = 0 := by
    linear_combination ((m : ℂ) + 5) * c1 - ((m : ℂ) + 1) * k4
  exact (mul_eq_zero.1 k5).resolve_left
    (mul_ne_zero (by norm_num) (by exact_mod_cast (show m + 2 ≠ 0 by omega)))

/-- If `m ≥ 2` and `m - 2, m + 2, m + 6 ∈ Z(f)`, then `m ∈ Z(f)`. -/
lemma sq_van (hr : r ≠ 0) {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) {m : ℤ}
    (hm : 2 ≤ m) (h1 : Van r U (m - 2) f) (h2 : Van r U (m + 2) f) (h3 : Van r U (m + 6) f) :
    Van r U m f := by
  intro v hv
  have hb := good_dzb hf
  have d1 := sq_eig hU hf (m := m) (by omega) h1 h2 hv
  have d2 := sq_eig hU (good_dz hb) (m := m) (by omega) (van_dz hU hb (van_dzb hU hf h1))
    (van_dz hU hb (van_dzb hU hf h2)) hv
  have e := sq_dz_dz hr hU (good_dzb hb) (m := m) (by omega) (van_dzb hU hb (van_dzb hU hf h1))
    (van_dzb hU hb (van_dzb hU hf h2)) (van_dzb hU hb (van_dzb hU hf h3)) hv
  rw [dzb_dz hb, e, mul_zero, neg_zero] at d2
  have hm2 : (m : ℂ) ^ 2 - 1 ≠ 0 := by
    have : m ^ 2 - 1 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hΔ := (mul_eq_zero.1 d2).resolve_left hm2
  rw [hΔ, mul_zero, neg_zero] at d1
  exact (mul_eq_zero.1 d1).resolve_left hm2

/-- **The square**: if `G_{4j+2}[f] = 0` on `U` for every `j ≥ 0`, then `G_k[f] = 0` on `U` for
every `k ≥ 2`. -/
theorem van_sq (hr : r ≠ 0) {U : Set ℂ} (hU : IsOpen U) (f : ℂ → ℂ) (hf : Good f)
    (h : ∀ j : ℕ, Van r U (4 * j + 2) f) : ∀ k : ℤ, 2 ≤ k → Van r U k f := by
  -- `G_{4i+4} = 0` for every function of the class
  have h4 : ∀ (f : ℂ → ℂ), Good f → (∀ j : ℕ, Van r U (4 * j + 2) f) →
      ∀ i : ℕ, Van r U (4 * i + 4) f := by
    intro f hf h i
    have e : ∀ (j : ℕ) (n : ℤ), 4 * (j : ℤ) + 2 = n → Van r U n f := fun j n hn => hn ▸ h j
    exact sq_van hr hU hf (by omega) (e i _ (by ring)) (e (i + 1) _ (by push_cast; ring))
      (e (i + 2) _ (by push_cast; ring))
  have hd : ∀ j : ℕ, Van r U (4 * j + 2) (dz f) := fun j => van_dz hU hf (h j)
  have hdb : ∀ j : ℕ, Van r U (4 * j + 2) (dzb f) := fun j => van_dzb hU hf (h j)
  intro k hk
  obtain ⟨i, hi⟩ : ∃ i : ℕ, k = 4 * i + 2 ∨ k = 4 * i + 3 ∨ k = 4 * i + 4 ∨ k = 4 * i + 5 := by
    refine ⟨((k - 2) / 4).toNat, ?_⟩
    have h0 : 0 ≤ (k - 2) / 4 := Int.ediv_nonneg (by omega) (by norm_num)
    rw [Int.toNat_of_nonneg h0]
    omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact h i
  · intro v hv
    have e := rec_down hU hf (k := 4 * i + 3)
      (by rw [show (4 * (i : ℤ) + 3 - 1) = 4 * i + 2 by ring]; exact h i) hv
    rw [show (4 * (i : ℤ) + 3 + 1) = 4 * i + 4 by ring, h4 _ (good_dzb hf) hdb i v hv, mul_zero,
      neg_zero] at e
    exact (mul_eq_zero.1 e).resolve_left (by exact_mod_cast (show 4 * (i : ℤ) + 3 ≠ 0 by omega))
  · exact h4 f hf h i
  · intro v hv
    have e := rec_up hU hf (k := 4 * i + 5)
      (by rw [show (4 * (i : ℤ) + 5 + 1) = 4 * ((i + 1 : ℕ) : ℤ) + 2 by push_cast; ring]
          exact h (i + 1)) hv
    rw [show (4 * (i : ℤ) + 5 - 1) = 4 * i + 4 by ring, h4 _ (good_dz hf) hd i v hv,
      mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_left (by exact_mod_cast (show 4 * (i : ℤ) + 5 ≠ 0 by omega))

/-- For the square (`m(3) = m(4) = 0`), `m(4j + k) = (e_A⁴)^j m(k)`. -/
lemma m_sq (F : Feet) (h3 : F.m 3 = 0) (h4 : F.m 4 = 0) (j k : ℕ) :
    F.m (4 * j + k) = (F.A ^ 4) ^ j * F.m k := by
  obtain ⟨hB, hC, hD⟩ := square_of_m3_m4 F h3 h4
  have e : ∀ E : ℂ, E ^ (4 * j + k) = (E ^ 4) ^ j * E ^ k := fun E => by rw [pow_add, pow_mul]
  simp only [Feet.m, e, ← hB, ← hC, ← hD]
  ring

/-- For the square, the modes `4j + 2` are non-degenerate. -/
lemma m_sq_ne_zero (F : Feet) (h3 : F.m 3 = 0) (h4 : F.m 4 = 0) (j : ℕ) :
    F.m (4 * j + 2) ≠ 0 := by
  rw [m_sq F h3 h4]
  have hA : F.A ≠ 0 := fun h => by
    have := F.nA; rw [h, norm_zero] at this; exact zero_ne_one this
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hA)) F.m_two_ne_zero

/-- **Step 3**: for every table but the square, the vanishing of the non-degenerate coefficients on
`U` forces the vanishing of all `G_k`, `|k| ≥ 2`, on `U`. -/
theorem van_all_ns (F : Feet) (hns : F.m 3 ≠ 0 ∨ F.m 4 ≠ 0) (hr : 0 < r) {U : Set ℂ}
    (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f) (hreal : ∀ x, conj (f x) = f x)
    (hN : ∀ k : ℕ, F.m k ≠ 0 → Van r U k f) : ∀ k : ℤ, 2 ≤ |k| → Van r U k f := by
  have hr0 := hr.ne'
  -- `G₂ = G₃ = 0`
  have h2 : Van r U 2 f := by exact_mod_cast hN 2 F.m_two_ne_zero
  have h3 : Van r U 3 f := by
    rcases hns with h | h
    · exact_mod_cast hN 3 h
    · exact van_isolated hU hf (by norm_num) (by simpa using h2) (by exact_mod_cast hN 4 h)
  -- pairs of vanishing coefficients arbitrarily far
  have hpair : ∀ N : ℕ, ∃ n ≥ N, Van r U ((n : ℤ) + 2) f ∧ Van r U ((n : ℤ) + 3) f := by
    intro N
    set δ := min ‖F.m 2‖ (max ‖F.m 3‖ ‖F.m 4‖) / 2
    have hδ : 0 < δ := by
      have : 0 < max ‖F.m 3‖ ‖F.m 4‖ := by
        rcases hns with h | h
        · exact lt_max_of_lt_left (norm_pos_iff.2 h)
        · exact lt_max_of_lt_right (norm_pos_iff.2 h)
      have := lt_min (norm_pos_iff.2 F.m_two_ne_zero) this
      positivity
    obtain ⟨n, hn, hA, hB, hC, hD⟩ := exists_pow_near_one F.nA F.nB F.nC F.nD hδ N
    have ne : ∀ k : ℕ, 2 * δ ≤ ‖F.m k‖ → F.m (n + k) ≠ 0 := fun k hk h0 => by
      have := m_shift F hA hB hC hD k
      rw [h0, zero_sub, norm_neg] at this; linarith
    have hd2 : 2 * δ ≤ ‖F.m 2‖ := by simp only [δ]; linarith [min_le_left ‖F.m 2‖ (max ‖F.m 3‖ ‖F.m 4‖)]
    have v2 : Van r U ((n : ℤ) + 2) f := by exact_mod_cast hN (n + 2) (ne 2 hd2)
    refine ⟨n, hn, v2, ?_⟩
    have hmax : 2 * δ ≤ max ‖F.m 3‖ ‖F.m 4‖ := by
      simp only [δ]; linarith [min_le_right ‖F.m 2‖ (max ‖F.m 3‖ ‖F.m 4‖)]
    rcases le_max_iff.1 hmax with h | h
    · exact_mod_cast hN (n + 3) (ne 3 h)
    · apply van_isolated hU hf (by omega)
      · rw [show (n : ℤ) + 3 - 1 = n + 2 by ring]; exact v2
      · rw [show (n : ℤ) + 3 + 1 = ((n + 4 : ℕ) : ℤ) by push_cast; ring]; exact hN (n + 4) (ne 4 h)
  -- blocks `[4, n + 1]`
  have hpos : ∀ k : ℤ, 2 ≤ k → Van r U k f := by
    intro k hk
    rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | hk4
    · exact h2
    · exact h3
    obtain ⟨n, hn, hn2, hn3⟩ := hpair k.toNat
    exact van_block hU hr0 (n - 3) f 4 (n + 1) (by omega) hf (by simpa using h3)
      (by rw [show (n : ℤ) + 1 + 1 = n + 2 by ring]; exact hn2)
      (by rw [show (n : ℤ) + 1 + 2 = n + 3 by ring]; exact hn3) (fun j h _ => by omega) k hk4
      (by omega)
  intro k hk
  rcases le_or_gt 0 k with h0 | h0
  · exact hpos k (by rw [abs_of_nonneg h0] at hk; exact hk)
  · have := van_neg hreal (hpos (-k) (by rw [abs_of_neg h0] at hk; exact hk))
    rwa [neg_neg] at this

/-- For every table (including the square), the vanishing of the non-degenerate coefficients on
`U` forces the vanishing of all `G_k`, `|k| ≥ 2`, on `U`. -/
theorem van_all (F : Feet) (hr : 0 < r) {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : Good f)
    (hreal : ∀ x, conj (f x) = f x) (hN : ∀ k : ℕ, F.m k ≠ 0 → Van r U k f) :
    ∀ k : ℤ, 2 ≤ |k| → Van r U k f := by
  by_cases hns : F.m 3 ≠ 0 ∨ F.m 4 ≠ 0
  · exact van_all_ns F hns hr hU hf hreal hN
  have h3 : F.m 3 = 0 := not_not.1 fun h => hns (Or.inl h)
  have h4 : F.m 4 = 0 := not_not.1 fun h => hns (Or.inr h)
  have hpos := van_sq hr.ne' hU f hf fun j => by
    exact_mod_cast hN (4 * j + 2) (m_sq_ne_zero F h3 h4 j)
  intro k hk
  rcases le_or_gt 0 k with h0 | h0
  · exact hpos k (by rw [abs_of_nonneg h0] at hk; exact hk)
  · have := van_neg hreal (hpos (-k) (by rw [abs_of_neg h0] at hk; exact hk))
    rwa [neg_neg] at this

/-! ### Real paraboloids and interpolation -/

/-- The real paraboloid `a + b·x + c|x|²`. -/
def rpar (a c : ℝ) (b : ℂ) (x : ℂ) : ℝ := a + dot b x + c * Complex.normSq x

lemma re_parab (a b : ℂ) (c : ℝ) (x : ℂ) :
    (parab a b (conj b) c x).re = rpar a.re c (2 * conj b) x := by
  simp only [parab, rpar, dot, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.normSq_apply, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- Interpolation of a paraboloid from its values at `x₀`, `x₀ ± h` and `x₀ + ih`. -/
noncomputable def interp (x₀ : ℂ) (h q₀ qp qm qi : ℝ) (x : ℂ) : ℝ :=
  q₀ + (qp - qm) / (2 * h) * (x - x₀).re + (qi - (qp + qm) / 2) / h * (x - x₀).im
    + (qp + qm - 2 * q₀) / (2 * h ^ 2) * Complex.normSq (x - x₀)

lemma rpar_eq_interp (a c : ℝ) (b x₀ : ℂ) {h : ℝ} (hh : h ≠ 0) (x : ℂ) :
    rpar a c b x = interp x₀ h (rpar a c b x₀) (rpar a c b (x₀ + h)) (rpar a c b (x₀ - h))
      (rpar a c b (x₀ + h * I)) x := by
  simp only [interp, rpar, dot, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

lemma interp_eq_rpar (x₀ : ℂ) (h q₀ qp qm qi : ℝ) : ∃ (a c : ℝ) (b : ℂ),
    ∀ x, interp x₀ h q₀ qp qm qi x = rpar a c b x := by
  set wr := (qp - qm) / (2 * h)
  set wi := (qi - (qp + qm) / 2) / h
  set cc := (qp + qm - 2 * q₀) / (2 * h ^ 2)
  refine ⟨q₀ - wr * x₀.re - wi * x₀.im + cc * Complex.normSq x₀, cc,
    ⟨wr - 2 * cc * x₀.re, wi - 2 * cc * x₀.im⟩, fun x => ?_⟩
  simp only [interp, rpar, dot, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

lemma tendsto_interp {ι : Type*} {l : Filter ι} (x₀ : ℂ) (h : ℝ) {q₀ qp qm qi : ι → ℝ}
    {Q₀ Qp Qm Qi : ℝ} (t₀ : Tendsto q₀ l (𝓝 Q₀)) (tp : Tendsto qp l (𝓝 Qp))
    (tm : Tendsto qm l (𝓝 Qm)) (ti : Tendsto qi l (𝓝 Qi)) (x : ℂ) :
    Tendsto (fun j => interp x₀ h (q₀ j) (qp j) (qm j) (qi j) x) l
      (𝓝 (interp x₀ h Q₀ Qp Qm Qi x)) := by
  unfold interp
  exact ((t₀.add (((tp.sub tm).div_const _).mul_const _)).add
    (((ti.sub ((tp.add tm).div_const _)).div_const _).mul_const _)).add
    (((((tp.add tm).sub (t₀.const_mul _)).div_const _)).mul_const _)

/-! ### The region swept by the feet -/

variable (r) in
/-- The region swept by the feet (at distance `r` from the axis) when the axis passes through a
point of the disc `B(v₀, R)`. -/
def Ω (v₀ : ℂ) (R : ℝ) : Set ℂ := {x | ∃ v ∈ Metric.ball v₀ R, ‖x - v‖ = r}

lemma exists_rot_of_norm {w : ℂ} (hw : ‖w‖ = r) : ∃ θ : ℝ, w = r * rot θ := by
  refine ⟨Complex.arg w, ?_⟩
  have := Complex.norm_mul_exp_arg_mul_I w
  rw [hw] at this
  rw [rot]; exact this.symm

lemma norm_feet {E : ℂ} (hE : ‖E‖ = 1) (hr : 0 ≤ r) (θ : ℝ) : ‖(r : ℂ) * (rot θ * E)‖ = r := by
  rw [norm_mul, norm_mul, norm_rot', hE, Complex.norm_real, Real.norm_of_nonneg hr]; ring

/-! ### Reduction to smooth terrains -/

/-- On `Ω(v₀, R₁)`, `g` coincides with the paraboloid interpolating it at four points of
`Ω(v₀, R₁)`; this uses the smooth case for mollifications of a continuous extension of `g`. -/
theorem interp_local (F : Feet) (hr : 0 < r) {v₀ : ℂ}
    {R₀ R₁ R₂ : ℝ} (h01 : 0 < R₁) (h12 : R₁ < R₂) (h20 : R₂ < R₀) {g : ℂ → ℝ}
    (hg : ContinuousOn g (Ω r v₀ R₀))
    (h : ∀ v ∈ Metric.ball v₀ R₀, ∀ θ, F₀v F r g v θ = 0)
    {x₀ : ℂ} {hh : ℝ} (hh0 : hh ≠ 0)
    (hp : ∀ w ∈ ({x₀, x₀ + hh, x₀ - hh, x₀ + hh * I} : Set ℂ), w ∈ Ω r v₀ R₁) :
    ∀ x ∈ Ω r v₀ R₁, g x = interp x₀ hh (g x₀) (g (x₀ + hh)) (g (x₀ - hh)) (g (x₀ + hh * I)) x := by
  -- the compact set `K` seen from the axes through `closedBall v₀ R₂`
  set K := (fun p : ℂ × ℂ => p.1 + p.2) '' (Metric.closedBall v₀ R₂ ×ˢ Metric.sphere (0 : ℂ) r)
  have hKc : IsCompact K := ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).image
    (continuous_fst.add continuous_snd)
  have hmemK : ∀ v ∈ Metric.closedBall v₀ R₂, ∀ y, ‖y - v‖ = r → y ∈ K := fun v hv y hy =>
    ⟨(v, y - v), ⟨hv, by simpa using hy⟩, by simp⟩
  have hKΩ : K ⊆ Ω r v₀ R₀ := by
    rintro _ ⟨⟨v, w⟩, ⟨hv, hw⟩, rfl⟩
    refine ⟨v, Metric.closedBall_subset_ball h20 hv, ?_⟩
    simpa using hw
  -- a continuous extension `g₁` with compact support
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hKc.isClosed
    ⟨K.domRestrict g, (hg.mono hKΩ).domRestrict⟩
  have hGK : ∀ y ∈ K, G y = g y := fun y hy => by
    have := congrArg (fun φ : C(K, ℝ) => φ ⟨y, hy⟩) hG
    exact this
  obtain ⟨M, hM⟩ : ∃ M, K ⊆ Metric.closedBall 0 M := hKc.isBounded.subset_closedBall 0
  let ψ : ContDiffBump (0 : ℂ) := ⟨max M 1, max M 1 + 1, by positivity, by linarith⟩
  set g₁ : ℂ → ℝ := fun y => ψ y * G y
  have hg₁c : Continuous g₁ := ψ.continuous.mul G.continuous
  have hg₁s : HasCompactSupport g₁ := ψ.hasCompactSupport.mul_right
  have hg₁K : ∀ y ∈ K, g₁ y = g y := fun y hy => by
    have : ψ y = 1 := ψ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall
      (le_max_left M 1) (hM hy))
    simp [g₁, this, hGK y hy]
  -- `G_k[g₁] = 0` on `closedBall v₀ R₂` for the non-degenerate modes
  have hγ₁ : ∀ k : ℕ, F.m k ≠ 0 → ∀ w ∈ Metric.closedBall v₀ R₂, γR r k g₁ w = 0 := by
    intro k hk w hw
    have h0 : ∀ θ, F₀v F r g₁ w θ = 0 := fun θ => by
      have e : ∀ E : ℂ, ‖E‖ = 1 → g₁ (w + r * (rot θ * E)) = g (w + r * (rot θ * E)) :=
        fun E hE => hg₁K _ (hmemK w hw _ (by rw [add_sub_cancel_left, norm_feet hE hr.le]))
      have := h w (Metric.closedBall_subset_ball h20 hw) θ
      unfold F₀v at this ⊢
      rw [e _ F.nA, e _ F.nB, e _ F.nC, e _ F.nD]; exact this
    exact (mul_eq_zero.1 (m_mul_γR_eq_zero F hg₁c h0 k)).resolve_left hk
  -- mollifications
  set d := R₂ - R₁
  have hd : 0 < d := by linarith
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun j =>
    ⟨d / (j + 2) / 2, d / (j + 2), by positivity, half_lt_self (by positivity)⟩
  have hφ0 : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    show Tendsto (fun j : ℕ => d / ((j : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hφd : ∀ j, (φ j).rOut ≤ d := fun j => by
    show d / ((j : ℝ) + 2) ≤ d
    rw [div_le_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- each mollification is a paraboloid on `Ω(v₀, R₁)`
  have hpar : ∀ j, ∃ (a c : ℝ) (b : ℂ), ∀ y ∈ Ω r v₀ R₁, moll (φ j) g₁ y = rpar a c b y := by
    intro j
    set f : ℂ → ℂ := fun y => ((moll (φ j) g₁ y : ℝ) : ℂ)
    have hm : ContDiff ℝ ∞ (moll (φ j) g₁) :=
      (φ j).hasCompactSupport_normed.contDiff_convolution_left _
        ((φ j).contDiff_normed (n := ⊤)) hg₁c.locallyIntegrable
    have hms : HasCompactSupport (moll (φ j) g₁) :=
      HasCompactSupport.convolution _ (φ j).hasCompactSupport_normed hg₁s
    have hf : Good f := ⟨Complex.ofRealCLM.contDiff.comp hm, hms.comp_left Complex.ofReal_zero⟩
    have hreal : ∀ y, conj (f y) = f y := fun y => Complex.conj_ofReal _
    have hU := (Metric.isOpen_ball : IsOpen (Metric.ball v₀ R₁))
    have hN : ∀ k : ℕ, F.m k ≠ 0 → Van r (Metric.ball v₀ R₁) k f := by
      intro k hk v hv
      have := γR_moll (r := r) (φ j) hg₁c k v
      simp only [γR] at this
      rw [show γ r k f v = γ r k (fun x => ((moll (φ j) g₁ x : ℝ) : ℂ)) v from rfl, this]
      have hz : ∀ t : ℂ, ((φ j).normed volume t : ℂ) * γ r k (fun x => ((g₁ x : ℝ) : ℂ)) (v - t)
          = 0 := by
        intro t
        by_cases ht : (φ j).normed volume t = 0
        · simp [ht]
        · have ht' : t ∈ Metric.ball (0 : ℂ) (φ j).rOut := by
            rw [← (φ j).support_normed_eq (μ := volume)]; exact ht
          have hvt : v - t ∈ Metric.closedBall v₀ R₂ := by
            rw [Metric.mem_closedBall, dist_eq_norm, show v - t - v₀ = (v - v₀) - t by ring]
            rw [Metric.mem_ball, dist_eq_norm] at hv
            rw [Metric.mem_ball, dist_zero_right] at ht'
            have := norm_sub_le (v - v₀) t
            have := hφd j
            have hdd : d = R₂ - R₁ := rfl
            linarith
          have := hγ₁ k hk (v - t) hvt
          simp only [γR] at this
          rw [this, mul_zero]
      simp only [hz]; exact integral_zero ℂ ℂ
    obtain ⟨a, b, c, habc⟩ := paraboloid_core hr hU (convex_ball v₀ R₁)
      (Metric.mem_ball_self h01) hf hreal (van_all F hr hU hf hreal hN)
    refine ⟨a.re, c, 2 * conj b, fun y hy => ?_⟩
    obtain ⟨v, hv, hyv⟩ := hy
    obtain ⟨θ, hθ⟩ := exists_rot_of_norm hyv
    have hy' : y = v + r * rot θ := by rw [← hθ]; ring
    have := congrArg Complex.re (habc v hv θ)
    rw [← hy', re_parab] at this
    simpa [f] using this
  -- pass to the limit
  have hlim : ∀ y, Tendsto (fun j => moll (φ j) g₁ y) atTop (𝓝 (g₁ y)) := fun y =>
    ContDiffBump.convolution_tendsto_right_of_continuous hφ0 hg₁c y
  have hK1 : ∀ y ∈ Ω r v₀ R₁, y ∈ K := fun y ⟨v, hv, hyv⟩ =>
    hmemK v (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall h12.le) hv)
      y hyv
  intro x hx
  have hjx : ∀ j, moll (φ j) g₁ x = interp x₀ hh (moll (φ j) g₁ x₀) (moll (φ j) g₁ (x₀ + hh))
      (moll (φ j) g₁ (x₀ - hh)) (moll (φ j) g₁ (x₀ + hh * I)) x := fun j => by
    obtain ⟨a, c, b, hab⟩ := hpar j
    rw [hab x hx, hab x₀ (hp _ (by simp)), hab _ (hp _ (by simp)), hab _ (hp _ (by simp)),
      hab _ (hp _ (by simp))]
    exact rpar_eq_interp a c b x₀ hh0 x
  have t := tendsto_interp x₀ hh (hlim x₀) (hlim (x₀ + hh)) (hlim (x₀ - hh)) (hlim (x₀ + hh * I)) x
  simp_rw [← hjx] at t
  have e := tendsto_nhds_unique (hlim x) t
  rw [hg₁K x (hK1 x hx), hg₁K _ (hK1 _ (hp _ (by simp))), hg₁K _ (hK1 _ (hp _ (by simp))),
    hg₁K _ (hK1 _ (hp _ (by simp))), hg₁K _ (hK1 _ (hp _ (by simp)))] at e
  exact e

/-! ### Proposition 4.13 -/

/-- **Proposition 4.13 (a)**: for every table (including the square), if `F₀^v ≡ 0` for every `v`
in an open disc `B(v₀, R₀)`, then the terrain is a paraboloid `a + b·x + c|x|²` on the region `Ω`
swept by the feet. Only the values of `g` on `Ω` matter. -/
theorem paraboloid_of_F₀v_local (F : Feet) (hr : 0 < r) {v₀ : ℂ}
    {R₀ : ℝ} (hR₀ : 0 < R₀) {g : ℂ → ℝ} (hg : ContinuousOn g (Ω r v₀ R₀))
    (h : ∀ v ∈ Metric.ball v₀ R₀, ∀ θ, F₀v F r g v θ = 0) :
    ∃ (a c : ℝ) (b : ℂ), ∀ x ∈ Ω r v₀ R₀, g x = rpar a c b x := by
  set x₀ := v₀ + r
  set hh := R₀ / 4
  have hh0 : hh ≠ 0 := by positivity
  obtain ⟨a, c, b, hab⟩ := interp_eq_rpar x₀ hh (g x₀) (g (x₀ + hh)) (g (x₀ - hh)) (g (x₀ + hh * I))
  refine ⟨a, c, b, fun x ⟨v, hv, hxv⟩ => ?_⟩
  rw [← hab]
  rw [Metric.mem_ball, dist_eq_norm] at hv
  set R₁ := max (‖v - v₀‖) (R₀ / 2) + (R₀ - max (‖v - v₀‖) (R₀ / 2)) / 3
  have hm : max (‖v - v₀‖) (R₀ / 2) < R₀ := max_lt hv (by linarith)
  have h1 : max (‖v - v₀‖) (R₀ / 2) < R₁ := by simp only [R₁]; linarith
  have h2 : R₁ < R₁ + (R₀ - max (‖v - v₀‖) (R₀ / 2)) / 3 := by linarith
  have h3 : R₁ + (R₀ - max (‖v - v₀‖) (R₀ / 2)) / 3 < R₀ := by simp only [R₁]; linarith
  have hR1 : R₀ / 2 < R₁ := lt_of_le_of_lt (le_max_right _ _) h1
  apply interp_local F hr (by linarith) h2 h3 hg h hh0
  · intro w hw
    have hpt : ∀ u : ℂ, ‖u‖ ≤ R₀ / 4 → x₀ + u ∈ Ω r v₀ R₁ := fun u hu => by
      refine ⟨v₀ + u, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith
      · rw [show x₀ + u - (v₀ + u) = (r : ℂ) by simp only [x₀]; ring, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
    have hn : ‖(hh : ℂ)‖ = R₀ / 4 := by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rcases hw with rfl | rfl | rfl | rfl
    · simpa using hpt 0 (by simp; positivity)
    · exact hpt _ hn.le
    · rw [sub_eq_add_neg]; exact hpt _ (by rw [norm_neg, hn])
    · exact hpt _ (by rw [norm_mul, Complex.norm_I, mul_one, hn])
  · refine ⟨v, ?_, hxv⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt (le_max_left _ _) h1

/-- **Proposition 4.13 (b)** (for every table): if `F₀^v ≡ 0` for every `v ∈ ℂ`, then the
continuous terrain is a paraboloid. -/
theorem paraboloid_of_F₀v (F : Feet) (hr : 0 < r) {g : ℂ → ℝ}
    (hg : Continuous g) (h : ∀ v θ, F₀v F r g v θ = 0) :
    ∃ (a c : ℝ) (b : ℂ), ∀ x, g x = rpar a c b x := by
  set x₀ : ℂ := (r : ℂ)
  obtain ⟨a, c, b, hab⟩ := interp_eq_rpar x₀ 1 (g x₀) (g (x₀ + 1)) (g (x₀ - 1)) (g (x₀ + 1 * I))
  refine ⟨a, c, b, fun x => ?_⟩
  set R := ‖x - r‖ + 4
  obtain ⟨a', c', b', h'⟩ := paraboloid_of_F₀v_local F hr (v₀ := 0) (R₀ := R) (by positivity)
    hg.continuousOn (fun v _ θ => h v θ)
  have hΩ : ∀ u : ℂ, ‖u‖ ≤ 1 → x₀ + u ∈ Ω r 0 R := fun u hu => by
    refine ⟨u, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]; linarith [norm_nonneg (x - r)]
    · rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hx : x ∈ Ω r 0 R := ⟨x - r, by rw [Metric.mem_ball, dist_zero_right]; linarith, by
    rw [sub_sub_cancel, Complex.norm_real, Real.norm_of_nonneg hr.le]⟩
  rw [← hab, h' x hx, h' x₀ (by simpa using hΩ 0 (by simp)), h' _ (hΩ 1 (by simp)),
    h' _ (by rw [sub_eq_add_neg]; exact hΩ (-1) (by simp)), h' _ (hΩ (1 * I) (by simp))]
  exact rpar_eq_interp a' c' b' x₀ one_ne_zero x

/-- **Proposition 4.13 (b)**, Lipschitz terrains (for every table): if `F₀^v ≡ 0` for every
`v ∈ ℂ` and `g` is Lipschitz on `ℂ`, then `g` is affine. (`Axis.affine_of_F₀v` is an independent
proof, by a Liouville argument, for the tables other than the square.) -/
theorem affine_of_F₀v_all (F : Feet) (hr : 0 < r) {g : ℂ → ℝ} {L : ℝ} (hg : IsLip g L)
    (h : ∀ v θ, F₀v F r g v θ = 0) : ∃ (a : ℝ) (b : ℂ), ∀ x, g x = a + dot b x := by
  obtain ⟨a, c, b, hab⟩ := paraboloid_of_F₀v F hr hg.continuous h
  -- `c = 0`: `g(t) + g(-t) - 2 g(0) = 2 c t²`, while `|g(±t) - g(0)| ≤ L t`
  have key : ∀ t : ℝ, 0 < t → |c| * t ≤ L := by
    intro t ht
    have e : g (t : ℂ) + g (-(t : ℂ)) - 2 * g 0 = 2 * c * t ^ 2 := by
      rw [hab, hab, hab]
      simp only [rpar, dot, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.zero_re, Complex.zero_im]
      ring
    have l1 := hg (t : ℂ) 0
    have l2 := hg (-(t : ℂ)) 0
    rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg ht.le] at l1
    rw [sub_zero, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht.le] at l2
    have l3 : |2 * c * t ^ 2| ≤ 2 * (L * t) := by
      rw [← e]
      calc |g (t : ℂ) + g (-(t : ℂ)) - 2 * g 0| = |(g t - g 0) + (g (-(t : ℂ)) - g 0)| := by
            congr 1; ring
        _ ≤ |g t - g 0| + |g (-(t : ℂ)) - g 0| := abs_add_le _ _
        _ ≤ 2 * (L * t) := by linarith
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (by positivity : 0 < t ^ 2)] at l3
    nlinarith
  have hc : c = 0 := by
    by_contra hc0
    have hc' : 0 < |c| := abs_pos.2 hc0
    have := key ((|L| + 1) / |c|) (by positivity)
    rw [mul_div_cancel₀ _ hc'.ne'] at this
    linarith [le_abs_self L]
  refine ⟨a, b, fun x => ?_⟩
  rw [hab x]; simp [rpar, hc]

/-- Converse: on a paraboloid, `F₀^v ≡ 0` for every position `v` of the axis. -/
theorem F₀v_of_paraboloid (F : Feet) (r a c : ℝ) (b v : ℂ) (θ : ℝ) :
    F₀v F r (rpar a c b) v θ = 0 := by
  have e : ∀ E : ℂ, ‖E‖ = 1 → rpar a c b (v + r * (rot θ * E)) =
      (a + c * (r ^ 2 - Complex.normSq v)) + dot (b + 2 * c * v) (v + r * (rot θ * E)) := by
    intro E hE
    have hn : Complex.normSq (r * (rot θ * E)) = r ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_mul, norm_rot', hE, Complex.norm_real,
        Real.norm_eq_abs, mul_one, mul_one, sq_abs]
    set w : ℂ := r * (rot θ * E)
    have hw : w.re ^ 2 + w.im ^ 2 = r ^ 2 := by rw [← hn, Complex.normSq_apply]; ring
    simp only [rpar, dot, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    linear_combination c * hw
  have := F₀v_of_affine F r (a + c * (r ^ 2 - Complex.normSq v)) (b + 2 * c * v) v θ
  unfold F₀v at this ⊢
  rw [e _ F.nA, e _ F.nB, e _ F.nC, e _ F.nD]; exact this

end Axis

end Wobbly
