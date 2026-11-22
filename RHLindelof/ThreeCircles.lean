import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Hadamard's three-circle theorem

Derived from Mathlib's three-lines theorem by composing with `w ↦ c + exp w`.
-/

open Complex Metric Set Complex.HadamardThreeLines
open scoped Real

noncomputable section

namespace RHLindelof

/-- **Hadamard's three-circle theorem**, in the form needed here. -/
theorem norm_le_of_three_circles {f : ℂ → ℂ} {c : ℂ} {r₁ r₂ r₃ R M₁ M₃ : ℝ}
    (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) (h₃ : r₃ < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hM₁ : ∀ z ∈ closedBall c r₁, ‖f z‖ ≤ M₁) (hM₃ : ∀ z ∈ closedBall c r₃, ‖f z‖ ≤ M₃)
    {z : ℂ} (hz : ‖z - c‖ = r₂) :
    ‖f z‖ ≤ M₁ ^ (1 - Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) *
      M₃ ^ (Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) := by
  have hr₂ : 0 < r₂ := h₁.trans h₁₂
  have hr₃ : 0 < r₃ := hr₂.trans h₂₃
  set l := Real.log r₁
  set u := Real.log r₃
  have hlu : l < u := Real.log_lt_log h₁ (h₁₂.trans h₂₃)
  set F : ℂ → ℂ := fun w => f (c + exp w) with hF
  have hmem : ∀ w ∈ verticalClosedStrip l u, c + exp w ∈ closedBall c r₃ := by
    intro w hw
    simp only [verticalClosedStrip, mem_preimage, mem_Icc] at hw
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_exp]
    calc Real.exp w.re ≤ Real.exp u := Real.exp_le_exp.mpr hw.2
      _ = r₃ := Real.exp_log hr₃
  have hdiff : DifferentiableOn ℂ F (verticalClosedStrip l u) := by
    intro w hw
    have hb : c + exp w ∈ ball c R := closedBall_subset_ball h₃ (hmem w hw)
    have h1 : DifferentiableAt ℂ f (c + exp w) := hf.differentiableAt (isOpen_ball.mem_nhds hb)
    exact (h1.comp w ((differentiableAt_id.cexp).const_add c)).differentiableWithinAt
  have hcl : closure (verticalStrip l u) ⊆ verticalClosedStrip l u :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
  have hd : DiffContOnCl ℂ F (verticalStrip l u) :=
    ⟨hdiff.mono (subset_closure.trans hcl), hdiff.continuousOn.mono hcl⟩
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip l u) := by
    refine ⟨M₃, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hM₃ _ (hmem w hw)
  have ha : ∀ w ∈ re ⁻¹' {l}, ‖F w‖ ≤ M₁ := by
    intro w hw
    simp only [mem_preimage, mem_singleton_iff] at hw
    apply hM₁
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_exp, hw, Real.exp_log h₁]
  have hb : ∀ w ∈ re ⁻¹' {u}, ‖F w‖ ≤ M₃ := by
    intro w hw
    simp only [mem_preimage, mem_singleton_iff] at hw
    apply hM₃
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_exp, hw, Real.exp_log hr₃]
  have hzc : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  set w₀ := log (z - c)
  have hw₀re : w₀.re = Real.log r₂ := by
    simp only [w₀, log_re, hz]
  have hw₀ : w₀ ∈ verticalClosedStrip l u := by
    simp only [verticalClosedStrip, mem_preimage, mem_Icc, hw₀re]
    exact ⟨Real.log_le_log h₁ h₁₂.le, Real.log_le_log hr₂ h₂₃.le⟩
  have key := norm_le_interp_of_mem_verticalClosedStrip' hlu hw₀ hd hB ha hb
  have hFz : F w₀ = f z := by
    simp only [hF, w₀, exp_log hzc]; ring_nf
  rw [hFz, hw₀re] at key
  have he : (Real.log r₂ - l) / (u - l) = Real.log (r₂ / r₁) / Real.log (r₃ / r₁) := by
    rw [Real.log_div hr₂.ne' h₁.ne', Real.log_div hr₃.ne' h₁.ne']
  rwa [he] at key

end RHLindelof
