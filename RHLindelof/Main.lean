import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.PhragmenLindelof
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.CriticalLineDecay
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds

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

open Complex Metric Set Complex.HadamardThreeLines
open scoped Real

noncomputable section

namespace RHLindelof

/-- The **Lindelöf hypothesis**: `ζ(1/2 + it) = O(|t|^ε)` for every `ε > 0`. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

/-! ### Step 1: unconditional size bounds -/
lemma hasSum_inv_succ_sq :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simpa [Finset.sum_range_succ, add_assoc, one_add_one_eq_two] using this

lemma norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have h1 : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℕ) : ℂ) := by push_cast; ring
    rw [hf]; simp only
    rw [norm_div, norm_one, this, norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    push_cast
    gcongr
    rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have hsum2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
    simpa using this
  have hfs : Summable f := Summable.of_norm_bounded hsum2 hnorm
  rw [hfs.tsum_eq_zero_add]
  have h0 : f 0 = 1 := by simp [hf]
  rw [h0, add_sub_cancel_left]
  apply tsum_of_norm_bounded hasSum_inv_succ_sq
  intro n
  have := hnorm (n + 1)
  push_cast at this
  convert this using 2; ring

lemma pi_sq_div_six_lt : Real.pi ^ 2 / 6 < 7 / 4 := by
  have := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

theorem norm_riemannZeta_bounds_of_two_le :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ σ t : ℝ, 2 ≤ σ →
      K⁻¹ ≤ ‖riemannZeta (σ + t * I)‖ ∧ ‖riemannZeta (σ + t * I)‖ ≤ K := by
  refine ⟨4, by norm_num, fun σ t hσ => ?_⟩
  have h := norm_riemannZeta_sub_one_le (s := σ + t * I) (by simpa using hσ)
  have hp := pi_sq_div_six_lt
  have a1 := norm_sub_norm_le (riemannZeta (σ + t * I)) 1
  have a2 := norm_sub_norm_le 1 (riemannZeta (σ + t * I))
  rw [norm_sub_rev] at a2
  simp only [norm_one] at a1 a2
  constructor <;> linarith

theorem norm_riemannZeta_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 6 → 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| := by
  refine ⟨10, by norm_num, fun σ t hσ hσ' ht => ?_⟩
  rcases lt_or_ge σ 3 with h3 | h3
  · have := norm_riemannZeta_lt_linear_im_on_strip (σ + t * I) (by simp only [Set.mem_Ico]; simp; constructor <;> linarith)
      (by simpa using ht)
    simp at this
    linarith
  · have h := norm_riemannZeta_sub_one_le (s := σ + t * I) (by simp; linarith)
    have hp := pi_sq_div_six_lt
    have a1 := norm_sub_norm_le (riemannZeta (σ + t * I)) 1
    simp only [norm_one] at a1
    linarith

/-! ### Steps 2–3: a logarithm of `ζ` under RH, and Borel–Carathéodory -/

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

/-! ### Step 4: Hadamard's three-circle theorem -/

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

/-! ### Step 5: Lindelöf to the right of the critical line, under RH -/

/-- `Q x^θ = o(x)` for `θ < 1`, in an explicit form. -/
lemma mul_rpow_le_eps_mul_add {Q θ ε : ℝ} (_hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → Q * x ^ θ ≤ ε * x + C' := by
  set X := max 1 ((|Q| / ε) ^ (1 - θ)⁻¹) with hX
  have hX1 : 1 ≤ X := le_max_left _ _
  refine ⟨|Q| * X, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hQ : Q * x ^ θ ≤ |Q| * x ^ θ :=
    mul_le_mul_of_nonneg_right (le_abs_self Q) (by positivity)
  have hεx : 0 ≤ ε * x := by positivity
  rcases le_total x X with hxX | hxX
  · have : x ^ θ ≤ x := by
      calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1.le
        _ = x := Real.rpow_one x
    have : |Q| * x ^ θ ≤ |Q| * X :=
      mul_le_mul_of_nonneg_left (this.trans hxX) (abs_nonneg Q)
    linarith
  · have h1θ : 0 < 1 - θ := by linarith
    have hge : |Q| / ε ≤ x ^ (1 - θ) := by
      calc |Q| / ε = ((|Q| / ε) ^ (1 - θ)⁻¹) ^ (1 - θ) :=
            (Real.rpow_inv_rpow (by positivity) h1θ.ne').symm
        _ ≤ X ^ (1 - θ) := Real.rpow_le_rpow (by positivity) (le_max_right _ _) h1θ.le
        _ ≤ x ^ (1 - θ) := Real.rpow_le_rpow (by linarith) hxX h1θ.le
    have hsplit : x = x ^ (1 - θ) * x ^ θ := by
      rw [← Real.rpow_add hx0]; simp
    have : |Q| * x ^ θ ≤ ε * x := by
      have h2 : |Q| ≤ ε * x ^ (1 - θ) := by
        rwa [div_le_iff₀ hε, mul_comm] at hge
      calc |Q| * x ^ θ ≤ ε * x ^ (1 - θ) * x ^ θ :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ε * x := by rw [mul_assoc, ← hsplit]
    have : 0 ≤ |Q| * X := by positivity
    linarith

/-- On the ball of radius `1/2` about `3 + it`, the logarithm is bounded (Borel–Carathéodory on
the ball of radius `1`, which lies in `re > 2`). -/
lemma norm_log_riemannZeta_le_inner {K K₀ t : ℝ} (hK : 1 ≤ K)
    (hKb : ∀ σ t : ℝ, 2 ≤ σ →
      K⁻¹ ≤ ‖riemannZeta (σ + t * I)‖ ∧ ‖riemannZeta (σ + t * I)‖ ≤ K)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (logBall t))
    (hge : ∀ z ∈ logBall t, exp (g z) = riemannZeta z) (hgc : ‖g (3 + t * I)‖ ≤ K₀) :
    ∀ w ∈ closedBall (3 + t * I) (1 / 2), ‖g w‖ ≤ 2 * K + 3 * max K₀ 0 := by
  set c : ℂ := 3 + t * I with hc
  intro w hw
  have hsub : ball c 1 ⊆ logBall t := ball_subset_ball (by norm_num)
  have hre : ∀ w ∈ ball c 1, (g w).re ≤ K := by
    intro w hw
    rw [re_eq_log_norm (hge w (hsub hw))]
    have hwre : 2 ≤ w.re := by
      rw [mem_ball, dist_eq_norm] at hw
      have := abs_re_le_norm (w - c)
      simp [hc] at this
      linarith [neg_abs_le (w.re - 3)]
    have hb := (hKb w.re w.im hwre).2
    rw [re_add_im] at hb
    have hpos : 0 < ‖riemannZeta w‖ :=
      norm_pos_iff.mpr (by rw [← hge w (hsub hw)]; exact exp_ne_zero _)
    exact (Real.log_le_log hpos hb).trans (Real.log_le_self (by linarith))
  have key := norm_le_borelCaratheodory (by linarith : (0 : ℝ) < K)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) (hg.mono hsub) hre hw
  have hgc' : ‖g c‖ ≤ max K₀ 0 := hgc.trans (le_max_left _ _)
  refine key.trans ?_
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [norm_nonneg (g c)]

theorem norm_riemannZeta_le_rpow_right (hRH : RiemannHypothesis) :
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 3 → 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε := by
  intro δ₀ hδ₀ ε hε
  set δ := min δ₀ (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδle : δ ≤ δ₀ := min_le_left _ _
  obtain ⟨K₀, hK₀⟩ := exists_log_riemannZeta hRH
  obtain ⟨A, hA, hAb⟩ := norm_log_riemannZeta_le K₀
  obtain ⟨K, hK, hKb⟩ := norm_riemannZeta_bounds_of_two_le
  obtain ⟨C₁, hC₁, hC₁b⟩ := norm_riemannZeta_le_linear
  set B := max (2 * K + 3 * max K₀ 0) 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  set P := 1 + 2 * A / δ with hPdef
  have hP1 : 1 ≤ P := by have : 0 ≤ 2 * A / δ := by positivity
                         linarith
  set r₃ := 5 / 2 - δ / 2 with hr₃
  set θ₀ := Real.log ((5 / 2 - δ) / (1 / 2)) / Real.log (r₃ / (1 / 2)) with hθ₀def
  have hlog3 : 0 < Real.log (r₃ / (1 / 2)) := Real.log_pos (by rw [hr₃]; linarith)
  have hθ₀0 : 0 ≤ θ₀ := div_nonneg (Real.log_nonneg (by linarith)) hlog3.le
  have hθ₀1 : θ₀ < 1 := by
    rw [div_lt_one hlog3]
    exact Real.log_lt_log (by linarith) (by rw [hr₃]; linarith)
  obtain ⟨C', hC'⟩ := mul_rpow_le_eps_mul_add (Q := B * P) hθ₀0 hθ₀1 hε
  refine ⟨4 * C₁ + Real.exp B + Real.exp C', ?_⟩
  intro σ t hσ hσ3 ht
  have hσ' : 1 / 2 + δ ≤ σ := le_trans (by linarith) hσ
  have ht0 : 0 < |t| := by linarith
  have htε : 1 ≤ |t| ^ ε := Real.one_le_rpow ht hε.le
  have hC₁0 : 0 ≤ 4 * C₁ := by positivity
  have heB := Real.exp_pos B
  have heC := Real.exp_pos C'
  -- bounded `t`
  rcases lt_or_ge |t| 4 with ht4 | ht4
  · have h := hC₁b σ t (by linarith) (by linarith) ht
    have : ‖riemannZeta (σ + t * I)‖ ≤ 4 * C₁ := by nlinarith
    nlinarith
  -- large `t`
  obtain ⟨g, hg, hge, hgc⟩ := hK₀ t ht4
  set c : ℂ := 3 + t * I with hc
  set z : ℂ := σ + t * I with hz
  have hzc : ‖z - c‖ = 3 - σ := by
    have : z - c = ((σ - 3 : ℝ) : ℂ) := by simp [hz, hc]
    rw [this, norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  have hzball : z ∈ logBall t := by
    rw [mem_ball, dist_eq_norm, hzc]; linarith
  have hζz : ‖riemannZeta z‖ ≤ Real.exp ‖g z‖ := by
    rw [← hge z hzball, norm_exp]; exact Real.exp_le_exp.mpr (re_le_norm _)
  have hlogt : 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le ht0]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  -- the inner circle
  have hinner : ∀ w ∈ closedBall c (1 / 2), ‖g w‖ ≤ B := fun w hw =>
    (norm_log_riemannZeta_le_inner hK hKb hg hge hgc w hw).trans (le_max_left _ _)
  -- the bound on `g z`
  have hgz : ‖g z‖ ≤ max B (ε * Real.log |t| + C') := by
    rcases le_or_gt (3 - σ) (1 / 2) with h12 | h12
    · exact (hinner z (by rw [mem_closedBall, dist_eq_norm, hzc]; exact h12)).trans
        (le_max_left _ _)
    set M₃ := max 1 (A * Real.log |t| / (δ / 2)) with hM₃
    have hM₃1 : 1 ≤ M₃ := le_max_left _ _
    have hM₃b : ∀ w ∈ closedBall c r₃, ‖g w‖ ≤ M₃ := fun w hw =>
      (hAb (δ / 2) (by positivity) (by linarith) t ht4 g hg hge hgc w hw).trans
        (le_max_right _ _)
    have h3c := norm_le_of_three_circles (f := g) (c := c) (r₁ := 1 / 2) (r₂ := 3 - σ)
      (r₃ := r₃) (R := 5 / 2) (by norm_num) h12 (by rw [hr₃]; linarith) (by rw [hr₃]; linarith)
      hg hinner hM₃b hzc
    set θ := Real.log ((3 - σ) / (1 / 2)) / Real.log (r₃ / (1 / 2)) with hθdef
    have hθ0 : 0 ≤ θ := div_nonneg (Real.log_nonneg (by linarith)) hlog3.le
    have hθ1 : θ ≤ θ₀ := by
      apply div_le_div_of_nonneg_right _ hlog3.le
      exact Real.log_le_log (by linarith) (by linarith)
    have hM₃P : M₃ ≤ P * Real.log |t| := by
      rw [hM₃, max_le_iff]
      constructor
      · nlinarith
      · rw [hPdef]
        have : A * Real.log |t| / (δ / 2) = 2 * A / δ * Real.log |t| := by
          field_simp
        rw [this]; nlinarith
    have hlog0 : 0 ≤ Real.log |t| := by linarith
    calc ‖g z‖ ≤ B ^ (1 - θ) * M₃ ^ θ := h3c
      _ ≤ B ^ (1 : ℝ) * M₃ ^ θ₀ :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith))
            (Real.rpow_le_rpow_of_exponent_le hM₃1 hθ1) (by positivity) (by positivity)
      _ ≤ B * (P * Real.log |t|) ^ θ₀ := by
          rw [Real.rpow_one]
          gcongr
      _ = B * (P ^ θ₀ * Real.log |t| ^ θ₀) := by
          rw [Real.mul_rpow (by linarith) hlog0]
      _ ≤ B * (P ^ (1 : ℝ) * Real.log |t| ^ θ₀) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hP1 hθ₀1.le) (by positivity)) (by linarith)
      _ = B * P * Real.log |t| ^ θ₀ := by rw [Real.rpow_one]; ring
      _ ≤ ε * Real.log |t| + C' := hC' _ hlogt
      _ ≤ _ := le_max_right _ _
  have hpow : Real.exp (ε * Real.log |t|) = |t| ^ ε := by
    rw [Real.rpow_def_of_pos ht0, mul_comm]
  calc ‖riemannZeta (σ + t * I)‖ = ‖riemannZeta z‖ := rfl
    _ ≤ Real.exp (max B (ε * Real.log |t| + C')) := hζz.trans (Real.exp_le_exp.mpr hgz)
    _ ≤ Real.exp B + Real.exp C' * |t| ^ ε := by
        rcases le_total B (ε * Real.log |t| + C') with h | h
        · rw [max_eq_right h, Real.exp_add, hpow, mul_comm (|t| ^ ε)]
          exact le_add_of_nonneg_left heB.le
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (by positivity)
    _ ≤ (4 * C₁ + Real.exp B + Real.exp C') * |t| ^ ε := by
        have h1 := mul_le_mul_of_nonneg_left htε heB.le
        have h2 : 0 ≤ 4 * C₁ * |t| ^ ε := by positivity
        linarith

/-! ### Step 6: Phragmén–Lindelöf convexity -/

lemma log_one_add_abs_sub_le (y T : ℝ) :
    Real.log (1 + |y|) - Real.log (1 + |T|) ≤ |y - T| := by
  have h1 : 0 < 1 + |y| := by positivity
  have h2 : 0 < 1 + |T| := by positivity
  rw [← Real.log_div h1.ne' h2.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos h1 h2)).trans ?_
  rw [div_sub_one h2.ne', div_le_iff₀ h2]
  have := abs_sub_abs_le_abs_sub y T
  nlinarith [abs_nonneg (y - T), abs_nonneg T]

lemma abs_log_one_add_abs_sub_le (y T : ℝ) :
    |Real.log (1 + |y|) - Real.log (1 + |T|)| ≤ |y - T| := by
  rw [abs_le]
  constructor
  · have := log_one_add_abs_sub_le T y
    rw [abs_sub_comm] at this; linarith
  · exact log_one_add_abs_sub_le y T

lemma mul_sub_sq_le (k u : ℝ) : k * u - u ^ 2 ≤ k ^ 2 / 4 := by
  nlinarith [sq_nonneg (u - k / 2)]

/-- The boundary estimate in the convexity argument. -/
lemma convexity_boundary_aux {A α a y T v : ℝ} (hv : v ≤ A * (1 + |y|) ^ α) (_hv0 : 0 ≤ v)
    (hA : 0 ≤ A) :
    v * Real.exp (-α * Real.log (1 + |T|)) * Real.exp (a ^ 2 - (y - T) ^ 2) ≤
      A * Real.exp (α ^ 2 / 4 + a ^ 2) := by
  have hy : 0 < 1 + |y| := by positivity
  rw [Real.rpow_def_of_pos hy] at hv
  have hl := abs_log_one_add_abs_sub_le y T
  have h1 : α * (Real.log (1 + |y|) - Real.log (1 + |T|)) ≤ |α| * |y - T| := by
    calc _ ≤ |α * (Real.log (1 + |y|) - Real.log (1 + |T|))| := le_abs_self _
      _ = |α| * |Real.log (1 + |y|) - Real.log (1 + |T|)| := abs_mul _ _
      _ ≤ |α| * |y - T| := mul_le_mul_of_nonneg_left hl (abs_nonneg α)
  have h2 := mul_sub_sq_le |α| |y - T|
  rw [sq_abs, sq_abs] at h2
  calc v * Real.exp (-α * Real.log (1 + |T|)) * Real.exp (a ^ 2 - (y - T) ^ 2)
      ≤ A * Real.exp (Real.log (1 + |y|) * α) * Real.exp (-α * Real.log (1 + |T|)) *
          Real.exp (a ^ 2 - (y - T) ^ 2) := by gcongr
    _ = A * Real.exp (α * (Real.log (1 + |y|) - Real.log (1 + |T|)) + a ^ 2 - (y - T) ^ 2) := by
        rw [mul_assoc A, mul_assoc A, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ A * Real.exp (α ^ 2 / 4 + a ^ 2) := by
        gcongr; linarith

lemma abs_convex_comb_le {α β a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    |(α * b - β * a) / (b - a) + (β - α) / (b - a) * x| ≤ |α| + |β| := by
  have hba : 0 < b - a := by linarith
  have e : (α * b - β * a) / (b - a) + (β - α) / (b - a) * x =
      α * ((b - x) / (b - a)) + β * ((x - a) / (b - a)) := by field_simp; ring
  have l1 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith [hx.2]) hba.le
  have l2 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) hba.le
  have u1 : (b - x) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith [hx.1])
  have u2 : (x - a) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith [hx.2])
  rw [e]
  calc _ ≤ |α * ((b - x) / (b - a))| + |β * ((x - a) / (b - a))| := abs_add_le _ _
    _ = |α| * ((b - x) / (b - a)) + |β| * ((x - a) / (b - a)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg l1, abs_of_nonneg l2]
    _ ≤ |α| * 1 + |β| * 1 := by gcongr
    _ = _ := by ring

/-- **Phragmén–Lindelöf convexity** in a vertical strip, for functions of exponential growth. -/
theorem norm_le_of_phragmenLindelof_convexity {f : ℂ → ℂ} {a b α β K A B D : ℝ} (hab : a < b)
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hgrowth : ∀ z ∈ re ⁻¹' Icc a b, ‖f z‖ ≤ D * Real.exp (K * |z.im|))
    (ha : ∀ t : ℝ, ‖f (a + t * I)‖ ≤ A * (1 + |t|) ^ α)
    (hb : ∀ t : ℝ, ‖f (b + t * I)‖ ≤ B * (1 + |t|) ^ β) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ ∈ Icc a b →
      ‖f (σ + t * I)‖ ≤ C * (1 + |t|) ^ ((α * (b - σ) + β * (σ - a)) / (b - a)) := by
  have hba : 0 < b - a := by linarith
  have hA0 : 0 ≤ A := by
    have := ha 0; simp at this; exact (norm_nonneg _).trans this
  have hB0 : 0 ≤ B := by
    have := hb 0; simp at this; exact (norm_nonneg _).trans this
  set c₀ := (α * b - β * a) / (b - a) with hc₀
  set c₁ := (β - α) / (b - a) with hc₁
  have hpa : c₀ + c₁ * a = α := by rw [hc₀, hc₁]; field_simp; ring
  have hpb : c₀ + c₁ * b = β := by rw [hc₀, hc₁]; field_simp; ring
  set M := max (A * Real.exp (α ^ 2 / 4 + a ^ 2)) (B * Real.exp (β ^ 2 / 4 + b ^ 2)) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (by positivity)
  refine ⟨M, fun σ T hσ => ?_⟩
  set L := Real.log (1 + |T|) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg T])
  set F : ℂ → ℂ := fun z => f z * (exp (-((c₀ : ℂ) + c₁ * z) * L) * exp ((z - T * I) ^ 2))
    with hF
  have hnF : ∀ z, ‖F z‖ = ‖f z‖ * Real.exp (-(c₀ + c₁ * z.re) * L) *
      Real.exp (z.re ^ 2 - (z.im - T) ^ 2) := by
    intro z
    simp only [hF, norm_mul, norm_exp, mul_assoc]
    congr 3
    · simp
    · simp [sq]
  have hd : DiffContOnCl ℂ F (re ⁻¹' Ioo a b) := by
    have h2 : Differentiable ℂ
        (fun z : ℂ => exp (-((c₀ : ℂ) + c₁ * z) * L) * exp ((z - T * I) ^ 2)) := by fun_prop
    exact ⟨hf.1.mul h2.differentiableOn, hf.2.mul h2.continuous.continuousOn⟩
  have hBdd : BddAbove ((norm ∘ F) '' re ⁻¹' Icc a b) := by
    refine ⟨max D 0 * Real.exp (|K| * |T| + K ^ 2 / 4 + (|α| + |β|) * L + (a ^ 2 + b ^ 2)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Function.comp, hnF]
    have hfz := hgrowth z hz
    have hz' : z.re ∈ Icc a b := hz
    have hy : |z.im| ≤ |T| + |z.im - T| := by
      have := abs_sub_abs_le_abs_sub z.im T; linarith
    have e1 : K * |z.im| ≤ |K| * |T| + |K| * |z.im - T| := by
      have := le_abs_self K
      nlinarith [abs_nonneg K, abs_nonneg z.im, abs_nonneg (z.im - T)]
    have e2 : -(c₀ + c₁ * z.re) * L ≤ (|α| + |β|) * L := by
      have := abs_convex_comb_le (α := α) (β := β) hab hz'
      have := neg_abs_le (c₀ + c₁ * z.re)
      nlinarith
    have e3 : z.re ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have h0 := mul_nonneg (sub_nonneg.2 hz'.1) (sub_nonneg.2 hz'.2)
      rcases le_total 0 (a + b) with h | h
      · nlinarith [mul_le_mul_of_nonneg_left hz'.2 h, sq_nonneg a]
      · nlinarith [mul_le_mul_of_nonpos_left hz'.1 h, sq_nonneg b]
    have e4 := mul_sub_sq_le |K| |z.im - T|
    rw [sq_abs, sq_abs] at e4
    calc ‖f z‖ * Real.exp (-(c₀ + c₁ * z.re) * L) * Real.exp (z.re ^ 2 - (z.im - T) ^ 2)
        ≤ max D 0 * Real.exp (K * |z.im|) * Real.exp (-(c₀ + c₁ * z.re) * L) *
            Real.exp (z.re ^ 2 - (z.im - T) ^ 2) := by
          gcongr
          exact hfz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      _ = max D 0 * Real.exp (K * |z.im| + -(c₀ + c₁ * z.re) * L +
            (z.re ^ 2 - (z.im - T) ^ 2)) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (le_max_right _ _)
  have hFa : ∀ z ∈ re ⁻¹' {a}, ‖F z‖ ≤ M := by
    intro z hz
    simp only [mem_preimage, mem_singleton_iff] at hz
    have hzeq : (a : ℂ) + z.im * I = z := by rw [← hz]; exact re_add_im z
    have hfa := ha z.im
    rw [hzeq] at hfa
    rw [hnF, hz, hpa]
    exact (convexity_boundary_aux hfa (norm_nonneg _) hA0).trans (le_max_left _ _)
  have hFb : ∀ z ∈ re ⁻¹' {b}, ‖F z‖ ≤ M := by
    intro z hz
    simp only [mem_preimage, mem_singleton_iff] at hz
    have hzeq : (b : ℂ) + z.im * I = z := by rw [← hz]; exact re_add_im z
    have hfb := hb z.im
    rw [hzeq] at hfb
    rw [hnF, hz, hpb]
    exact (convexity_boundary_aux hfb (norm_nonneg _) hB0).trans (le_max_right _ _)
  have hzmem : (σ : ℂ) + T * I ∈ verticalClosedStrip a b := by
    simpa [verticalClosedStrip] using hσ
  have key := norm_le_interp_of_mem_verticalClosedStrip' hab hzmem hd hBdd hFa hFb
  rw [← Real.rpow_add' hM0 (by ring_nf; norm_num), show (1 : ℝ) - _ + _ = 1 by ring,
    Real.rpow_one, hnF] at key
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at key
  have hp : c₀ + c₁ * σ = (α * (b - σ) + β * (σ - a)) / (b - a) := by
    rw [hc₀, hc₁]; field_simp; ring
  rw [hp] at key
  set p := (α * (b - σ) + β * (σ - a)) / (b - a)
  have hT : 0 < 1 + |T| := by positivity
  rw [Real.rpow_def_of_pos hT, ← hL]
  have e1 : Real.exp (-p * L) * Real.exp (L * p) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have e2 : 1 ≤ Real.exp (σ ^ 2 - 0 ^ 2) := Real.one_le_exp (by nlinarith [sq_nonneg σ])
  have hfn := norm_nonneg (f (σ + T * I))
  have hX : ‖f (σ + T * I)‖ * Real.exp (-p * L) ≤ M :=
    (le_mul_of_one_le_right (by positivity) e2).trans key
  calc ‖f (σ + T * I)‖ = ‖f (σ + T * I)‖ * Real.exp (-p * L) * Real.exp (L * p) := by
        rw [mul_assoc, e1, mul_one]
    _ ≤ M * Real.exp (L * p) := by gcongr

/-! ### Step 7: the functional equation -/

lemma norm_cos_le_exp (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  rw [norm_div, RCLike.norm_ofNat]
  have h1 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; simp; exact neg_le_abs w.im
  have h2 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; simp; exact le_abs_self w.im
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

lemma Gamma_re_le_two {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 3 / 2) : Real.Gamma x ≤ 2 := by
  rcases le_total 1 x with hx | hx
  · linarith [Real.Gamma.le_one_of_mem_Icc hx (by linarith)]
  · have hx0 : 0 < x := by linarith
    have hg := Real.Gamma.le_one_of_mem_Icc (x := x + 1) (by linarith) (by linarith)
    rw [Real.Gamma_add_one hx0.ne'] at hg
    have := Real.Gamma_pos_of_pos hx0
    nlinarith

lemma norm_Gamma_le_two {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) : ‖Gamma s‖ ≤ 2 :=
  (Complex.Gamma.norm_le_Gamma_re (by linarith)).trans (Gamma_re_le_two h1 h2)

lemma norm_two_pi_cpow_neg_le {s : ℂ} (hs : 0 ≤ s.re) : ‖(2 * (π : ℂ)) ^ (-s)‖ ≤ 1 := by
  have : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)

lemma abs_im_pi_mul_div_two (w : ℂ) : |(π * w / 2).im| = π / 2 * |w.im| := by
  have : (π * w / 2).im = π / 2 * w.im := by simp; ring
  rw [this, abs_mul, abs_of_pos (by positivity)]

lemma im_pi_mul_div_two (σ t : ℝ) : (π * ((σ : ℂ) + t * I) / 2).im = π * t / 2 := by
  simp

/-- `Γ(s) cos(πs/2)` grows like `|t|^(σ - 1/2)` on vertical lines with `1/2 ≤ σ ≤ 3/2`. -/
theorem norm_gamma_mul_cos_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖Gamma (σ + t * I) * cos (π * (σ + t * I) / 2)‖ ≤ C * |t| ^ (σ - 1 / 2) := by
  set f : ℂ → ℂ := fun s => Gamma s * cos (π * s / 2) with hf
  have hstrip : ∀ z ∈ re ⁻¹' Icc (1 / 2 : ℝ) (3 / 2), DifferentiableAt ℂ f z := by
    intro z hz
    have hz' : (1 / 2 : ℝ) ≤ z.re := hz.1
    have hG : DifferentiableAt ℂ Gamma z := by
      apply differentiableAt_Gamma
      intro m hm
      have := congrArg re hm; simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact hG.mul (by fun_prop)
  have hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (3 / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
  have hd : DiffContOnCl ℂ f (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) := by
    have hon : DifferentiableOn ℂ f (re ⁻¹' Icc (1 / 2 : ℝ) (3 / 2)) := fun z hz =>
      (hstrip z hz).differentiableWithinAt
    exact ⟨hon.mono (subset_closure.trans hcl), hon.continuousOn.mono hcl⟩
  have hgrowth : ∀ z ∈ re ⁻¹' Icc (1 / 2 : ℝ) (3 / 2),
      ‖f z‖ ≤ 2 * Real.exp (π / 2 * |z.im|) := by
    intro z hz
    simp only [hf, norm_mul]
    have hc := norm_cos_le_exp (π * z / 2)
    rw [abs_im_pi_mul_div_two] at hc
    exact mul_le_mul (norm_Gamma_le_two hz.1 hz.2) hc (norm_nonneg _) (by norm_num)
  have hcos : ∀ σ t : ℝ, ‖cos (π * ((σ : ℂ) + t * I) / 2)‖ ≤ Real.exp (π * |t| / 2) := by
    intro σ t
    have := norm_cos_le_exp (π * ((σ : ℂ) + t * I) / 2)
    rwa [im_pi_mul_div_two, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two] at this
  have hhalf : ∀ t : ℝ, ‖Gamma (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Real.exp (π * |t| / 2) ≤ 3 := by
    intro t
    have := Complex.gamma_half_vertical_norm_le_exp t
    have hs : Real.sqrt (2 * π) < 3 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith [Real.pi_lt_d2]
    calc _ ≤ Real.sqrt (2 * π) * Real.exp (-(π * |t| / 2)) * Real.exp (π * |t| / 2) := by
          gcongr
      _ = Real.sqrt (2 * π) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ 3 := hs.le
  have ha : ∀ t : ℝ, ‖f ((1 / 2 : ℝ) + t * I)‖ ≤ 3 * (1 + |t|) ^ (0 : ℝ) := by
    intro t
    simp only [hf, norm_mul, Real.rpow_zero, mul_one]
    calc _ ≤ ‖Gamma (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Real.exp (π * |t| / 2) := by
          gcongr; exact hcos _ t
      _ ≤ 3 := hhalf t
  have hb : ∀ t : ℝ, ‖f ((3 / 2 : ℝ) + t * I)‖ ≤ 3 * (1 + |t|) ^ (1 : ℝ) := by
    intro t
    simp only [hf, norm_mul, Real.rpow_one]
    have hne : ((1 / 2 : ℝ) : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg re h; simp at this
    have hG : Gamma (((3 / 2 : ℝ) : ℂ) + t * I) =
        (((1 / 2 : ℝ) : ℂ) + t * I) * Gamma (((1 / 2 : ℝ) : ℂ) + t * I) := by
      rw [← Complex.Gamma_add_one _ hne]; congr 1; push_cast; ring
    have hn : ‖((1 / 2 : ℝ) : ℂ) + t * I‖ ≤ 1 + |t| := by
      refine (norm_add_le _ _).trans ?_
      simp; norm_num [abs_of_pos]
    rw [hG, norm_mul]
    calc _ ≤ (1 + |t|) * ‖Gamma (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Real.exp (π * |t| / 2) := by
          gcongr; exact hcos _ t
      _ ≤ (1 + |t|) * 3 := by rw [mul_assoc]; gcongr; exact hhalf t
      _ = _ := by ring
  obtain ⟨C, hC⟩ := norm_le_of_phragmenLindelof_convexity (by norm_num) hd hgrowth ha hb
  refine ⟨2 * max C 0, fun t ht => ?_⟩
  have h := hC σ t ⟨hσ, hσ'⟩
  have he : ((0 : ℝ) * (3 / 2 - σ) + 1 * (σ - 1 / 2)) / (3 / 2 - 1 / 2) = σ - 1 / 2 := by ring
  rw [he] at h
  have hx0 : 0 ≤ σ - 1 / 2 := by linarith
  have hx1 : σ - 1 / 2 ≤ 1 := by linarith
  have hp : (1 + |t|) ^ (σ - 1 / 2) ≤ 2 * |t| ^ (σ - 1 / 2) := by
    calc (1 + |t|) ^ (σ - 1 / 2) ≤ (2 * |t|) ^ (σ - 1 / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) hx0
      _ = 2 ^ (σ - 1 / 2) * |t| ^ (σ - 1 / 2) := Real.mul_rpow (by norm_num) (abs_nonneg t)
      _ ≤ 2 ^ (1 : ℝ) * |t| ^ (σ - 1 / 2) := by
          gcongr
          · norm_num
      _ = 2 * |t| ^ (σ - 1 / 2) := by rw [Real.rpow_one]
  have hpos : 0 ≤ (1 + |t|) ^ (σ - 1 / 2) := by positivity
  calc ‖Gamma (σ + t * I) * cos (π * (σ + t * I) / 2)‖ ≤ C * (1 + |t|) ^ (σ - 1 / 2) := h
    _ ≤ max C 0 * (1 + |t|) ^ (σ - 1 / 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ ≤ max C 0 * (2 * |t| ^ (σ - 1 / 2)) := mul_le_mul_of_nonneg_left hp (le_max_right _ _)
    _ = _ := by ring

/-- The functional equation in the form used below. -/
lemma riemannZeta_one_sub' {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * (Gamma s * cos (π * s / 2)) * riemannZeta s := by
  rw [riemannZeta_one_sub]
  · ring
  · intro n hn
    have := congrArg re hn; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h] at h1; simp at h1

theorem norm_riemannZeta_le_rpow_left {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1 / 2 + η + t * I)‖ ≤ C * |t| ^ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (1 / 2 - η + t * I)‖ ≤ C * |t| ^ (η + ε) := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := h ε hε
  obtain ⟨C₂, hC₂⟩ := norm_gamma_mul_cos_le (σ := 1 / 2 + η) (by linarith) (by linarith)
  refine ⟨2 * max C₂ 0 * max C₁ 0, fun t ht => ?_⟩
  set s : ℂ := ((1 / 2 + η : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + η := by simp [hs]
  have hfe := riemannZeta_one_sub' (s := s) (by rw [hsre]; linarith) (by rw [hsre]; linarith)
  have h1s : 1 - s = 1 / 2 - η + t * I := by rw [hs]; push_cast; ring
  rw [h1s] at hfe
  have ht' : 1 ≤ |-t| := by rwa [abs_neg]
  have hg := hC₂ (-t) ht'
  have hz := hC₁ (-t) ht'
  rw [abs_neg] at hg hz
  have hz' : ‖riemannZeta s‖ ≤ C₁ * |t| ^ ε := by
    rw [hs]; convert hz using 3; push_cast; ring
  have hg' : ‖Gamma s * cos (π * s / 2)‖ ≤ C₂ * |t| ^ (1 / 2 + η - 1 / 2) := hg
  rw [show (1 / 2 + η - 1 / 2 : ℝ) = η by ring] at hg'
  have hpi := norm_two_pi_cpow_neg_le (s := s) (by rw [hsre]; linarith)
  have hpow : |t| ^ (η + ε) = |t| ^ η * |t| ^ ε := Real.rpow_add (by linarith) _ _
  have e1 : 0 ≤ |t| ^ η := by positivity
  have e2 : 0 ≤ |t| ^ ε := by positivity
  have hg'' : ‖Gamma s * cos (π * s / 2)‖ ≤ max C₂ 0 * |t| ^ η :=
    hg'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) e1)
  have hz'' : ‖riemannZeta s‖ ≤ max C₁ 0 * |t| ^ ε :=
    hz'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) e2)
  rw [hfe, norm_mul, norm_mul, norm_mul, RCLike.norm_ofNat, hpow]
  calc 2 * ‖(2 * (π : ℂ)) ^ (-s)‖ * ‖Gamma s * cos (π * s / 2)‖ * ‖riemannZeta s‖
      ≤ 2 * 1 * (max C₂ 0 * |t| ^ η) * (max C₁ 0 * |t| ^ ε) := by
        gcongr
    _ = _ := by ring

/-- `ζ` has at most exponential growth in the strip `[1/2 - η, 1/2 + η]`. -/
theorem norm_riemannZeta_le_poly_strip {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    ∃ D K : ℝ, ∀ z ∈ re ⁻¹' Icc (1 / 2 - η) (1 / 2 + η),
      ‖riemannZeta z‖ ≤ D * Real.exp (K * |z.im|) := by
  -- the compact part
  set S := re ⁻¹' Icc (1 / 2 - η) (1 / 2 + η) ∩ im ⁻¹' Icc (-1 : ℝ) 1 with hS
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn riemannZeta S := by
    intro z hz
    have hne : z ≠ 1 := by
      rintro rfl; have := hz.1.2; simp at this; linarith
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hSc.exists_bound_of_continuousOn hcont
  -- the linear bound off the compact part
  have hlin : ∀ w : ℂ, 1 / 2 ≤ w.re → w.re < 3 → 1 ≤ |w.im| →
      ‖riemannZeta w‖ ≤ 10 * Real.exp |w.im| := by
    intro w h1 h2 h3
    have := norm_riemannZeta_lt_linear_im_on_strip w ⟨h1, h2⟩ h3
    have := Real.add_one_le_exp |w.im|
    linarith
  refine ⟨max M₀ 40, π / 2 + 1, fun z hz => ?_⟩
  have hK : 0 ≤ (π / 2 + 1) * |z.im| := by positivity
  have hE1 : 1 ≤ Real.exp ((π / 2 + 1) * |z.im|) := Real.one_le_exp hK
  have hz1 : 1 / 2 - η ≤ z.re := hz.1
  have hz2 : z.re ≤ 1 / 2 + η := hz.2
  have hmax : 0 ≤ max M₀ 40 := le_max_of_le_right (by norm_num)
  rcases lt_or_ge |z.im| 1 with him | him
  · have hzS : z ∈ S := ⟨hz, abs_le.mp him.le⟩
    calc ‖riemannZeta z‖ ≤ M₀ := hM₀ z hzS
      _ ≤ max M₀ 40 := le_max_left _ _
      _ ≤ _ := le_mul_of_one_le_right hmax hE1
  have hexp : Real.exp |z.im| ≤ Real.exp ((π / 2 + 1) * |z.im|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, abs_nonneg z.im]
  rcases le_or_gt (1 / 2) z.re with hre | hre
  · calc ‖riemannZeta z‖ ≤ 10 * Real.exp |z.im| := hlin z hre (by linarith) him
      _ ≤ 40 * Real.exp ((π / 2 + 1) * |z.im|) := by nlinarith [Real.exp_pos |z.im|]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · set s := 1 - z with hs
    have hsre : s.re = 1 - z.re := by simp [hs]
    have hsim : |s.im| = |z.im| := by simp [hs]
    have hfe := riemannZeta_one_sub' (s := s) (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    rw [show 1 - s = z by rw [hs]; ring] at hfe
    have hpi := norm_two_pi_cpow_neg_le (s := s) (by rw [hsre]; linarith)
    have hG := norm_Gamma_le_two (s := s) (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    have hc := norm_cos_le_exp (π * s / 2)
    rw [abs_im_pi_mul_div_two, hsim] at hc
    have hzs := hlin s (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [hsim]; exact him)
    rw [hsim] at hzs
    rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_ofNat]
    calc 2 * ‖(2 * (π : ℂ)) ^ (-s)‖ * (‖Gamma s‖ * ‖cos (π * s / 2)‖) * ‖riemannZeta s‖
        ≤ 2 * 1 * (2 * Real.exp (π / 2 * |z.im|)) * (10 * Real.exp |z.im|) := by
          gcongr
      _ = 40 * Real.exp ((π / 2 + 1) * |z.im|) := by
          rw [mul_comm 40, show (π / 2 + 1) * |z.im| = π / 2 * |z.im| + |z.im| by ring,
            Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ### Step 8: the theorem -/

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
