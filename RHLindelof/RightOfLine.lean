import RHLindelof.LogZeta
import RHLindelof.ThreeCircles

/-!
# Lindelöf to the right of the critical line, under RH

Three circles about `3 + it` applied to `log ζ` give `log ζ(σ + it) = O((log t)^θ)` with
`θ < 1`. Hence `ζ(σ + it) = O(|t|^ε)` for `σ ≥ 1/2 + δ`.
-/

open Complex Metric Set
open scoped Real

noncomputable section

namespace RHLindelof

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

end RHLindelof
