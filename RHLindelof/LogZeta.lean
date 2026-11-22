import RHLindelof.ZetaBounds
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# A logarithm of `ζ` under RH

Under RH, `ζ` has no zeros in `re s > 1/2`. On the ball of radius `5/2` about `3 + it` it
therefore has a holomorphic logarithm. Borel–Carathéodory bounds it by `log |t| / δ` on the
ball of radius `5/2 - δ`.
-/

open Complex Metric Set
open scoped Real

noncomputable section

namespace RHLindelof

/-- The ball on which we take `log ζ`. It lies in `re > 1/2` and, for `|t| ≥ 4`, misses `s = 1`. -/
abbrev logBall (t : ℝ) : Set ℂ := ball (3 + t * I) (5 / 2)

lemma mem_logBall {t : ℝ} {z : ℂ} (hz : z ∈ logBall t) :
    1 / 2 < z.re ∧ z.re < 11 / 2 ∧ |z.im - t| < 5 / 2 := by
  rw [mem_ball, dist_eq_norm] at hz
  have h1 := abs_re_le_norm (z - (3 + t * I))
  have h2 := abs_im_le_norm (z - (3 + t * I))
  simp at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · linarith [neg_abs_le (z.re - 3)]
  · linarith [le_abs_self (z.re - 3)]
  · linarith

lemma riemannZeta_ne_zero_of_RH (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) :
    riemannZeta z ≠ 0 := by
  intro h0
  by_cases h1 : z = 1
  · subst h1; exact riemannZeta_one_ne_zero h0
  have := hRH z h0 ?_ h1
  · linarith
  · rintro ⟨n, rfl⟩
    simp at hz
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

lemma ne_one_of_mem_logBall {t : ℝ} (ht : 4 ≤ |t|) {z : ℂ} (hz : z ∈ logBall t) : z ≠ 1 := by
  rintro rfl
  have := (mem_logBall hz).2.2
  simp at this
  have := abs_sub_abs_le_abs_sub t 0
  rw [abs_sub_comm] at this
  simp at this
  linarith [abs_sub_abs_le_abs_sub 0 t, abs_sub_comm 0 t]

/-- A nonvanishing holomorphic function on a ball has a holomorphic logarithm. -/
lemma exists_log_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hc : c ∈ ball c r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hf0 : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧ (∀ z ∈ ball c r, exp (g z) = f z) ∧
      g c = log (f c) := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    (hf.deriv isOpen_ball).div hf hf0
  obtain ⟨g, hgc, hg⟩ := (hd.isExactOn_ball).with_val_at c (log (f c))
  have hgd : DifferentiableOn ℂ g (ball c r) := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  refine ⟨g, hgd, ?_, hgc⟩
  -- `exp g / f` is constant
  set h : ℂ → ℂ := fun z => exp (g z) / f z
  have hfa : ∀ z ∈ ball c r, HasDerivAt f (deriv f z) z := fun z hz =>
    (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hh : ∀ z ∈ ball c r, HasDerivAt h 0 z := by
    intro z hz
    have := ((hg z hz).cexp).div (hfa z hz) (hf0 z hz)
    convert this using 1
    field_simp [hf0 z hz]
    ring
  have hhd : DifferentiableOn ℂ h (ball c r) := fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ ball c r, h z = h c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hhd
      (fun w hw => (hh w hw).deriv) hz hc
  have hc1 : h c = 1 := by
    simp only [h, hgc, exp_log (hf0 c hc)]; exact div_self (hf0 c hc)
  intro z hz
  have := hconst z hz
  rw [hc1] at this
  simp only [h] at this
  exact (div_eq_one_iff_eq (hf0 z hz)).mp this

lemma norm_log_le_of_bounds {w : ℂ} {K : ℝ} (hK : 1 ≤ K) (h1 : K⁻¹ ≤ ‖w‖) (h2 : ‖w‖ ≤ K) :
    ‖log w‖ ≤ Real.log K + Real.pi := by
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) h1
  calc ‖log w‖ ≤ |(log w).re| + |(log w).im| := norm_le_abs_re_add_abs_im _
    _ ≤ Real.log K + Real.pi := by
      gcongr
      · rw [log_re, abs_le]
        constructor
        · have := Real.log_le_log (by positivity) h1
          rw [Real.log_inv] at this; linarith
        · exact Real.log_le_log hpos h2
      · rw [log_im, abs_le]; exact ⟨(neg_pi_lt_arg w).le, arg_le_pi w⟩

theorem exists_log_riemannZeta (hRH : RiemannHypothesis) :
    ∃ K₀ : ℝ, ∀ t : ℝ, 4 ≤ |t| → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (logBall t) ∧
      (∀ z ∈ logBall t, exp (g z) = riemannZeta z) ∧ ‖g (3 + t * I)‖ ≤ K₀ := by
  obtain ⟨K, hK, hKb⟩ := norm_riemannZeta_bounds_of_two_le
  refine ⟨Real.log K + Real.pi, fun t ht => ?_⟩
  have hc : (3 + t * I) ∈ logBall t := mem_ball_self (by norm_num)
  have hf : DifferentiableOn ℂ riemannZeta (logBall t) := fun z hz =>
    (differentiableAt_riemannZeta (ne_one_of_mem_logBall ht hz)).differentiableWithinAt
  have hf0 : ∀ z ∈ logBall t, riemannZeta z ≠ 0 := fun z hz =>
    riemannZeta_ne_zero_of_RH hRH (mem_logBall hz).1
  obtain ⟨g, hgd, hge, hgc⟩ := exists_log_of_ne_zero hc hf hf0
  refine ⟨g, hgd, hge, ?_⟩
  rw [hgc]
  have := hKb 3 t (by norm_num)
  push_cast at this
  exact norm_log_le_of_bounds hK this.1 this.2

/-- Borel–Carathéodory about a general centre, with a uniform radius. -/
lemma norm_le_borelCaratheodory {g : ℂ → ℂ} {c : ℂ} {R r M : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hrR : r < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hre : ∀ z ∈ ball c R, (g z).re ≤ M) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ (2 * M * r + ‖g c‖ * (R + r)) / (R - r) := by
  have hR : 0 < R := hr.trans_lt hrR
  set G : ℂ → ℂ := fun w => g (c + w)
  have hG : DifferentiableOn ℂ G (ball 0 R) := by
    refine hg.comp (differentiableOn_const c |>.add differentiableOn_id) ?_
    intro w hw; simpa [mem_ball, dist_eq_norm] using hw
  have hG₁ : MapsTo G (ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    exact hre _ (by simpa [mem_ball, dist_eq_norm] using hw)
  have hzr : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hw : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]; linarith
  have key := Complex.borelCaratheodory hM hG hG₁ hR hw
  simp only [G, add_sub_cancel, add_zero] at key
  have hd : 0 < R - r := by linarith
  have hd' : 0 < R - ‖z - c‖ := by linarith
  calc ‖g z‖ ≤ _ := key
    _ ≤ 2 * M * r / (R - r) + ‖g c‖ * (R + r) / (R - r) := by
      gcongr
    _ = _ := by rw [add_div]

lemma re_eq_log_norm {g : ℂ → ℂ} {f : ℂ → ℂ} {z : ℂ} (h : exp (g z) = f z) :
    (g z).re = Real.log ‖f z‖ := by
  rw [← h, norm_exp, Real.log_exp]

theorem norm_log_riemannZeta_le (K₀ : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t : ℝ, 4 ≤ |t| → ∀ g : ℂ → ℂ,
      DifferentiableOn ℂ g (logBall t) → (∀ z ∈ logBall t, exp (g z) = riemannZeta z) →
      ‖g (3 + t * I)‖ ≤ K₀ →
      ∀ z ∈ closedBall (3 + t * I) (5 / 2 - δ), ‖g z‖ ≤ A * Real.log |t| / δ := by
  obtain ⟨C, hC, hCb⟩ := norm_riemannZeta_le_linear
  refine ⟨5 * |Real.log (2 * C)| + 5 + 5 * max K₀ 0, by positivity, ?_⟩
  intro δ hδ hδ1 t ht g hg hge hgc z hz
  have hlogt : 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  set M := |Real.log (2 * C)| + Real.log |t| with hMdef
  have hM : 0 < M := by linarith [abs_nonneg (Real.log (2 * C))]
  have hre : ∀ w ∈ logBall t, (g w).re ≤ M := by
    intro w hw
    rw [re_eq_log_norm (hge w hw)]
    obtain ⟨h1, h2, h3⟩ := mem_logBall hw
    have e1 := abs_sub_abs_le_abs_sub t w.im
    have e2 := abs_sub_abs_le_abs_sub w.im t
    rw [abs_sub_comm] at e1
    have him1 : 1 ≤ |w.im| := by linarith
    have him2 : |w.im| ≤ 2 * |t| := by linarith
    have hzb := hCb w.re w.im h1.le (by linarith) him1
    rw [re_add_im] at hzb
    have hpos : 0 < ‖riemannZeta w‖ :=
      norm_pos_iff.mpr (by rw [← hge w hw]; exact exp_ne_zero _)
    have ht0 : 0 < |t| := by linarith
    calc Real.log ‖riemannZeta w‖ ≤ Real.log (2 * C * |t|) :=
          Real.log_le_log hpos (by nlinarith)
      _ = Real.log (2 * C) + Real.log |t| := Real.log_mul (by positivity) (by positivity)
      _ ≤ M := by linarith [le_abs_self (Real.log (2 * C))]
  have key := norm_le_borelCaratheodory hM (r := 5 / 2 - δ) (R := 5 / 2) (by linarith)
    (by linarith) hg hre hz
  have hgc' : ‖g (3 + t * I)‖ ≤ max K₀ 0 := hgc.trans (le_max_left _ _)
  have hK0 : 0 ≤ max K₀ 0 := le_max_right _ _
  rw [show (5 / 2 : ℝ) - (5 / 2 - δ) = δ by ring] at key
  refine key.trans ?_
  gcongr ?_ / δ
  have hgn := norm_nonneg (g (3 + t * I))
  have ha := abs_nonneg (Real.log (2 * C))
  nlinarith

end RHLindelof
