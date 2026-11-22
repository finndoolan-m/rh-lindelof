import RHLindelof.ZetaBounds
import RHLindelof.Convexity
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.CriticalLineDecay
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds

/-!
# The functional equation

`Γ(s) cos(πs/2) ≪ |t|^(σ - 1/2)` for `1/2 ≤ σ ≤ 3/2`. The proof uses convexity between the
lines `σ = 1/2` and `σ = 3/2`, with no Stirling. Via `ζ(1 - s) = 2(2π)^(-s) Γ(s) cos(πs/2) ζ(s)`
this moves bounds from `σ = 1/2 + η` to `σ = 1/2 - η`. Also an a priori growth bound for `ζ` in
the strip `[1/2 - η, 1/2 + η]`.
-/

open Complex Metric Set
open scoped Real

noncomputable section

namespace RHLindelof

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

end RHLindelof
