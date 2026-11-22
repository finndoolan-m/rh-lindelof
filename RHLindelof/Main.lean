import RHLindelof.RightOfLine
import RHLindelof.FunctionalEquation

/-!
# The Riemann hypothesis implies the Lindelöf hypothesis

Littlewood's argument (Titchmarsh, *The Theory of the Riemann Zeta-Function*, §14.2), stated for
Mathlib's `RiemannHypothesis`.

Outline:
1. `norm_riemannZeta_le_linear`: `‖ζ(σ + it)‖ ≪ |t|` on `1/2 ≤ σ ≤ 6`;
   `norm_riemannZeta_bounds_of_two_le`: `ζ` is bounded above and below on `σ ≥ 2`.
2. `exists_log_riemannZeta`: under RH, `ζ` has a holomorphic logarithm on the ball of radius
   `5/2` about `3 + it`, of bounded size at the centre.
3. `norm_log_riemannZeta_le`: Borel–Carathéodory gives `‖log ζ‖ ≪ log |t| / δ` on the ball of
   radius `5/2 - δ`.
4. `norm_le_of_three_circles`: Hadamard's three-circle theorem, from the three-lines theorem.
5. `norm_riemannZeta_le_rpow_right`: under RH, `ζ(σ + it) = O(|t|^ε)` for `σ > 1/2`.
6. `norm_le_of_phragmenLindelof_convexity`: convexity in a vertical strip, for functions of
   exponential growth (a Gaussian weight and the three-lines theorem).
7. `norm_gamma_mul_cos_le`: `Γ(s) cos(πs/2) ≪ |t|^(σ - 1/2)`, by convexity between the lines
   `σ = 1/2` and `σ = 3/2`; `norm_riemannZeta_le_rpow_left`: the functional equation moves step 5
   to `σ = 1/2 - η`, with an extra factor `|t|^η`; `norm_riemannZeta_le_poly_strip`: an a priori
   growth bound in the strip.
8. `lindelof_of_riemannHypothesis`: convexity in `[1/2 - η, 1/2 + η]`, and let `η → 0`.
-/

open Complex Metric Set
open scoped Real

noncomputable section

namespace RHLindelof

/-- The **Lindelöf hypothesis**: `ζ(1/2 + it) = O(|t|^ε)` for every `ε > 0`. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

/-- A bound for `|t| ≥ 1` and continuity give a bound for all `t`. -/
theorem bound_all_of_bound_large {f : ℝ → ℂ} (hf : Continuous f) {C x : ℝ} (hx : 0 ≤ x)
    (h : ∀ t : ℝ, 1 ≤ |t| → ‖f t‖ ≤ C * |t| ^ x) :
    ∃ A : ℝ, ∀ t : ℝ, ‖f t‖ ≤ A * (1 + |t|) ^ x := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.norm.continuousOn
  refine ⟨max M 0 + max C 0, fun t => ?_⟩
  have h1 : 1 ≤ (1 + |t|) ^ x := Real.one_le_rpow (by linarith [abs_nonneg t]) hx
  have hpos : 0 ≤ (1 + |t|) ^ x := by positivity
  rcases le_or_gt 1 |t| with ht | ht
  · have := h t ht
    have h2 : |t| ^ x ≤ (1 + |t|) ^ x :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) hx
    calc ‖f t‖ ≤ C * |t| ^ x := this
      _ ≤ max C 0 * (1 + |t|) ^ x := by
          rcases le_total 0 C with hC | hC
          · rw [max_eq_left hC]; exact mul_le_mul_of_nonneg_left h2 hC
          · rw [max_eq_right hC]; simp
            exact mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
      _ ≤ (max M 0 + max C 0) * (1 + |t|) ^ x := by
          nlinarith [le_max_right M 0]
  · have hm : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := hM t hm
    simp only [norm_norm] at this
    calc ‖f t‖ ≤ max M 0 := this.trans (le_max_left _ _)
      _ ≤ max M 0 * (1 + |t|) ^ x := le_mul_of_one_le_right (le_max_right _ _) h1
      _ ≤ (max M 0 + max C 0) * (1 + |t|) ^ x := by nlinarith [le_max_right C 0]

/-- `ζ` is continuous on vertical lines other than `re = 1`. -/
theorem continuous_riemannZeta_vline {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (σ : ℂ) + t * I ≠ 1 := by
    intro h; apply hσ; simpa using congrArg Complex.re h
  exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
    (by fun_prop)

/-- **The Riemann hypothesis implies the Lindelöf hypothesis.** -/
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) : LindelofHypothesis := by
  intro ε hε
  set ε₀ := min ε (1 / 2) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  have hε₀half : ε₀ ≤ 1 / 2 := min_le_right _ _
  set η := ε₀ / 2 with hηdef
  have hη : 0 < η := by positivity
  have hη' : η < 1 / 2 := by linarith
  set ε' := ε₀ / 4 with hε'def
  have hε' : 0 < ε' := by positivity
  -- the line `1/2 + η`
  have hRline : ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1 / 2 + η + t * I)‖ ≤ C * |t| ^ e := by
    intro e he
    obtain ⟨C, hC⟩ := norm_riemannZeta_le_rpow_right hRH η hη e he
    refine ⟨C, fun t ht => ?_⟩
    have := hC (1 / 2 + η) t le_rfl (by linarith) ht
    simpa using this
  obtain ⟨C₁, hC₁⟩ := hRline ε' hε'
  obtain ⟨C₂, hC₂⟩ := norm_riemannZeta_le_rpow_left hη hη' hRline ε' hε'
  -- bounds for all `t`
  obtain ⟨B, hB⟩ := bound_all_of_bound_large (f := fun t : ℝ => riemannZeta
      (((1 / 2 + η : ℝ) : ℂ) + t * I)) (continuous_riemannZeta_vline (by linarith))
      hε'.le (C := C₁) (fun t ht => by simpa using hC₁ t ht)
  obtain ⟨A, hA⟩ := bound_all_of_bound_large (f := fun t : ℝ => riemannZeta
      (((1 / 2 - η : ℝ) : ℂ) + t * I)) (continuous_riemannZeta_vline (by linarith))
      (by positivity : (0 : ℝ) ≤ η + ε') (C := C₂) (fun t ht => by simpa using hC₂ t ht)
  -- convexity
  have hab : 1 / 2 - η < 1 / 2 + η := by linarith
  have hdiff : DiffContOnCl ℂ riemannZeta (re ⁻¹' Ioo (1 / 2 - η) (1 / 2 + η)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hz' : z ∈ re ⁻¹' Icc (1 / 2 - η) (1 / 2 + η) :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re) hz
    have hne : z ≠ 1 := by
      rintro rfl; simp at hz'; linarith [hz'.2]
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  obtain ⟨D, K, hDK⟩ := norm_riemannZeta_le_poly_strip hη hη'
  obtain ⟨C, hC⟩ := norm_le_of_phragmenLindelof_convexity hab hdiff hDK hA hB
  have hexp : ((η + ε') * (1 / 2 + η - 1 / 2) + ε' * (1 / 2 - (1 / 2 - η))) /
      (1 / 2 + η - (1 / 2 - η)) = ε₀ / 2 := by
    have h0 : ε₀ ≠ 0 := hε₀.ne'
    rw [hηdef, hε'def]; field_simp; ring_nf; simp [h0]
  refine ⟨max C 0 * 2 ^ (ε₀ / 2), fun t ht => ?_⟩
  have h := hC (1 / 2) t ⟨by linarith, by linarith⟩
  rw [hexp] at h
  have h1 : (1 + |t|) ^ (ε₀ / 2) ≤ 2 ^ (ε₀ / 2) * |t| ^ ε := by
    calc (1 + |t|) ^ (ε₀ / 2) ≤ (2 * |t|) ^ (ε₀ / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = 2 ^ (ε₀ / 2) * |t| ^ (ε₀ / 2) := Real.mul_rpow (by norm_num) (abs_nonneg t)
      _ ≤ 2 ^ (ε₀ / 2) * |t| ^ ε := by
          gcongr
          · linarith
  have hpos : 0 ≤ (1 + |t|) ^ (ε₀ / 2) := by positivity
  calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (1 + |t|) ^ (ε₀ / 2) := by simpa using h
    _ ≤ max C 0 * (1 + |t|) ^ (ε₀ / 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ ≤ max C 0 * (2 ^ (ε₀ / 2) * |t| ^ ε) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = max C 0 * 2 ^ (ε₀ / 2) * |t| ^ ε := by ring

end RHLindelof
