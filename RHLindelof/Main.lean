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
open scoped Real

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
