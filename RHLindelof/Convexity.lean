import Mathlib.Analysis.Complex.Hadamard

/-!
# Phragmén–Lindelöf convexity in a vertical strip

If `f` has at most exponential growth in the strip `a ≤ re z ≤ b`, with `f ≪ (1 + |t|)^α` on
`re z = a` and `f ≪ (1 + |t|)^β` on `re z = b`, then `f ≪ (1 + |t|)^p(σ)` with `p` linear.
The proof applies the three-lines theorem to `f` times `(1 + |T|)^(-q(z))` times a Gaussian
centred at height `T`.
-/

open Complex Metric Set Complex.HadamardThreeLines
open scoped Real

noncomputable section

namespace RHLindelof

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

end RHLindelof
