import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The Riemann hypothesis implies the Lindelöf hypothesis

Littlewood's argument (Titchmarsh, *The Theory of the Riemann Zeta-Function*, §14.2), stated for
Mathlib's `RiemannHypothesis`.

Outline:
1. `norm_riemannZeta_le_linear`: `‖ζ(σ + it)‖ ≪ |t|` on `1/2 ≤ σ ≤ 6`.
2. `exists_log_riemannZeta`: under RH, `ζ` has a holomorphic logarithm on the ball of radius
   `5/2` about `3 + it`, of bounded size at the centre.
3. `norm_log_riemannZeta_le`: Borel–Carathéodory gives `‖log ζ‖ ≪ log |t| / δ` on the ball of
   radius `5/2 - δ`.
4. `norm_le_of_three_circles`: Hadamard's three-circle theorem.
5. `norm_riemannZeta_le_rpow_right`: under RH, `ζ(σ + it) = O(|t|^ε)` for `σ > 1/2`.
6. `norm_riemannZeta_le_rpow_left`: the functional equation moves this to `σ = 1/2 - η`, with an
   extra factor `|t|^η`.
7. `norm_le_of_phragmenLindelof_convexity`: convexity in the strip `[1/2 - η, 1/2 + η]`.
8. `lindelof_of_riemannHypothesis`: let `η → 0`.
-/

open Complex Metric Set

noncomputable section

namespace RHLindelof

/-- The **Lindelöf hypothesis**: `ζ(1/2 + it) = O(|t|^ε)` for every `ε > 0`. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

/-! ### Step 1: unconditional size bounds -/

/-- `ζ` grows at most linearly in `|t|` on `1/2 ≤ σ ≤ 6`. -/
theorem norm_riemannZeta_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 6 → 2 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| := by
  sorry

/-- On `σ ≥ 2`, `ζ` is bounded above and away from zero. -/
theorem norm_riemannZeta_bounds_of_two_le :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ σ t : ℝ, 2 ≤ σ →
      K⁻¹ ≤ ‖riemannZeta (σ + t * I)‖ ∧ ‖riemannZeta (σ + t * I)‖ ≤ K := by
  sorry

/-! ### Step 2: a logarithm of `ζ` under RH -/

/-- The ball on which we take `log ζ`. It lies in `re > 1/2` and, for `|t| ≥ 4`, misses `s = 1`. -/
abbrev logBall (t : ℝ) : Set ℂ := ball (3 + t * I) (5 / 2)

theorem exists_log_riemannZeta (hRH : RiemannHypothesis) :
    ∃ K₀ : ℝ, ∀ t : ℝ, 4 ≤ |t| → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (logBall t) ∧
      (∀ z ∈ logBall t, exp (g z) = riemannZeta z) ∧ ‖g (3 + t * I)‖ ≤ K₀ := by
  sorry

/-! ### Step 3: Borel–Carathéodory -/

theorem norm_log_riemannZeta_le (hRH : RiemannHypothesis) :
    ∃ A : ℝ, 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t : ℝ, 4 ≤ |t| → ∀ g : ℂ → ℂ,
      DifferentiableOn ℂ g (logBall t) → (∀ z ∈ logBall t, exp (g z) = riemannZeta z) →
      ∀ z ∈ closedBall (3 + t * I) (5 / 2 - δ), ‖g z‖ ≤ A * Real.log |t| / δ := by
  sorry

/-! ### Step 4: Hadamard's three-circle theorem -/

/-- **Hadamard's three-circle theorem**, in the form needed here. -/
theorem norm_le_of_three_circles {f : ℂ → ℂ} {c : ℂ} {r₁ r₂ r₃ R M₁ M₃ : ℝ}
    (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) (h₃ : r₃ < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hM₁ : ∀ z ∈ closedBall c r₁, ‖f z‖ ≤ M₁) (hM₃ : ∀ z ∈ closedBall c r₃, ‖f z‖ ≤ M₃)
    {z : ℂ} (hz : ‖z - c‖ = r₂) :
    ‖f z‖ ≤ M₁ ^ (1 - Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) *
      M₃ ^ (Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) := by
  sorry

/-! ### Step 5: Lindelöf to the right of the critical line, under RH -/

theorem norm_riemannZeta_le_rpow_right (hRH : RiemannHypothesis) :
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε := by
  sorry

/-! ### Step 6: the functional equation -/

/-- `Γ(s) cos(πs/2)` grows like `|t|^(σ - 1/2)` on vertical lines. -/
theorem norm_gamma_mul_cos_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖Gamma (σ + t * I) * cos (π * (σ + t * I) / 2)‖ ≤ C * |t| ^ (σ - 1 / 2) := by
  sorry

theorem norm_riemannZeta_le_rpow_left {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1 / 2 + η + t * I)‖ ≤ C * |t| ^ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1 / 2 - η + t * I)‖ ≤ C * |t| ^ (η + ε) := by
  sorry

/-! ### Step 7: Phragmén–Lindelöf convexity -/

/-- **Phragmén–Lindelöf convexity** in a vertical strip, for functions of polynomial growth. -/
theorem norm_le_of_phragmenLindelof_convexity {f : ℂ → ℂ} {a b α β K A B D : ℝ} (hab : a < b)
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hgrowth : ∀ z ∈ re ⁻¹' Icc a b, ‖f z‖ ≤ D * (1 + |z.im|) ^ K)
    (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ A * (1 + |t|) ^ α)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ B * (1 + |t|) ^ β) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ ∈ Icc a b →
      ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ ((α * (b - σ) + β * (σ - a)) / (b - a)) := by
  sorry

/-- `ζ` has polynomial growth in the strip `[1/2 - η, 1/2 + η]`. -/
theorem norm_riemannZeta_le_poly_strip {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    ∃ D K : ℝ, ∀ z ∈ re ⁻¹' Icc (1 / 2 - η) (1 / 2 + η),
      ‖riemannZeta z‖ ≤ D * (1 + |z.im|) ^ K := by
  sorry

/-! ### Step 8: the theorem -/

/-- **The Riemann hypothesis implies the Lindelöf hypothesis.** -/
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) : LindelofHypothesis := by
  sorry

end RHLindelof
