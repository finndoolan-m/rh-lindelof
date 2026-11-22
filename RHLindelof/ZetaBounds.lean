import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity

/-!
# Unconditional bounds for `ζ`

For `σ ≥ 2`, `‖ζ(s) - 1‖ ≤ π²/6 - 1`. That gives upper and lower bounds on `σ ≥ 2`. Together with
PrimeNumberTheoremAnd's strip bound it gives `‖ζ(σ + it)‖ ≪ |t|` on `1/2 ≤ σ ≤ 6`, `|t| ≥ 1`.
-/

open Complex Metric Set
open scoped Real

noncomputable section

namespace RHLindelof

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

end RHLindelof
