import Wobbly.Rational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Complements

* `Table.idealised_balance`: the theorem of §2 in the idealised model of Remark 2.3 (b), with the
  argument of Remark 2.3 (a): for every cyclic table and every continuous terrain, the idealised
  wobbling function `F₀` vanishes at some angle (`∫ F₀ = 0` and the intermediate value theorem).
* `trapezoid_m_eq_zero_iff_chebyshev`: the Chebyshev form of Lemma 5.3 (c).
-/

open Complex

namespace Wobbly

namespace Table

variable {T : Table}

/-- **§2, idealised model** (Theorem 2.2 with Remark 2.3): for every cyclic table and every
continuous terrain, there is an angle at which `F₀ = τ h_A + (1-τ) h_C - μ h_B - (1-μ) h_D`
vanishes, i.e. the feet put down vertically are coplanar. -/
theorem idealised_balance (hc : T.Cyclic) {g : ℂ → ℝ} (hg : Continuous g) (τ μ : ℝ) :
    ∃ θ, F₀ T g τ μ θ = 0 := by
  by_contra hne
  simp only [not_exists] at hne
  obtain ⟨⟨θ₁, h₁⟩, ⟨θ₂, h₂⟩⟩ := exists_pos_neg_of_integral_zero (continuous_F₀ hg τ μ)
    (periodic_F₀ g τ μ) (integral_F₀ hc hg τ μ) (hne 0)
  have hivt := intermediate_value_uIcc (a := θ₂) (b := θ₁)
    (continuous_F₀ (T := T) hg τ μ).continuousOn
  obtain ⟨θ, -, hθ⟩ := hivt (Set.mem_uIcc.2 (Or.inl ⟨h₂.le, h₁.le⟩))
  exact hne θ hθ

end Table

/-- **Lemma 5.3 (c), Chebyshev form**: for `0 < α, β < π` and `k ≥ 1`,
`sin α sin kβ = sin β sin kα` iff `U_{k-1}(cos α) = U_{k-1}(cos β)`. -/
theorem trapezoid_m_eq_zero_iff_chebyshev {α β : ℝ} (hα : 0 < α) (hα' : α < Real.pi)
    (hβ : 0 < β) (hβ' : β < Real.pi) (k : ℕ) :
    Real.sin α * Real.sin (k * β) - Real.sin β * Real.sin (k * α) = 0 ↔
      (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos α) =
        (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos β) := by
  have e : ∀ x : ℝ, Real.sin (k * x) =
      (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos x) * Real.sin x := fun x => by
    rw [Polynomial.Chebyshev.U_real_cos]; push_cast; ring_nf
  have sa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hα'
  have sb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ hβ'
  rw [e α, e β]
  constructor
  · intro h
    have : Real.sin α * Real.sin β *
        ((Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos β) -
          (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos α)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · nlinarith [mul_pos sa sb]
    · linarith
  · intro h; rw [h]; ring

end Wobbly
