# rh-lindelof

Lean 4 formalisation of **the Riemann hypothesis implies the Lindelöf hypothesis**
(Littlewood; Titchmarsh §14.2), stated against Mathlib's `RiemannHypothesis`.

Built on [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) for
the strip bound on ζ and the Gamma bounds.

## Status

Sorry-free. `#print axioms RHLindelof.lindelof_of_riemannHypothesis` shows only `propext`,
`Classical.choice` and `Quot.sound`.

| Step | Lemma | Uses RH | Status |
|---|---|---|---|
| 1 | `norm_riemannZeta_le_linear`, `norm_riemannZeta_bounds_of_two_le` | no | proved |
| 2 | `exists_log_riemannZeta` | yes | proved |
| 3 | `norm_log_riemannZeta_le` (Borel–Carathéodory) | yes | proved |
| 4 | `norm_le_of_three_circles` | no | proved |
| 5 | `norm_riemannZeta_le_rpow_right` | yes | proved |
| 6 | `norm_le_of_phragmenLindelof_convexity` | no | proved |
| 7 | `norm_gamma_mul_cos_le`, `norm_riemannZeta_le_rpow_left`, `norm_riemannZeta_le_poly_strip` | no | proved |
| 8 | `lindelof_of_riemannHypothesis` (from steps 1–7) | yes | proved |

### Notes on the proof

- **Step 1.** For `σ ≥ 2`, `‖ζ(s) − 1‖ ≤ π²/6 − 1` from the Dirichlet series. That gives both
  bounds on `σ ≥ 2` and the linear bound on `3 ≤ σ ≤ 6`. For `1/2 ≤ σ < 3` it uses
  PrimeNumberTheoremAnd's `norm_riemannZeta_lt_linear_im_on_strip`. The linear bound holds for
  `|t| ≥ 1`.
- **Step 2.** A nonvanishing holomorphic function on a ball has a holomorphic logarithm: take a
  primitive of `f'/f` (Mathlib's `DifferentiableOn.isExactOn_ball`), then `exp g / f` has zero
  derivative.
- **Step 3** takes the bound `‖g(3 + it)‖ ≤ K₀` at the centre as a hypothesis. Without it the
  statement is false, because `g + 2πik` satisfies the other hypotheses.
- **Step 4.** Mathlib's three-lines theorem applied to `w ↦ f(c + exp w)`.
- **Step 5.** On the circle of radius `1/2`, `log ζ` is `O(1)` (Borel–Carathéodory on the
  radius-1 ball, which lies in `σ > 2`). On radius `5/2 − δ/2` it is `O(log t)` (step 3). Three
  circles give `O((log t)^θ)` with `θ < 1`, which is `≤ ε log t + C`.
- **Step 6.** The growth hypothesis is `‖f z‖ ≤ D·exp(K|Im z|)`, weaker than polynomial. For a
  target height `T`, the three-lines theorem is applied to
  `f(z)·(1+|T|)^(−q(z))·exp((z − iT)²)`, which is bounded on the strip.
- **Step 7.** No Stirling. On `σ = 1/2`, `|Γ(s)| ≤ √(2π)·e^(−π|t|/2)` (PrimeNumberTheoremAnd's
  `gamma_half_vertical_norm_le_exp`) and `|cos(πs/2)| ≤ e^(π|t|/2)`. On `σ = 3/2` use
  `Γ(s+1) = sΓ(s)`. Step 6 then interpolates between the two lines. `norm_gamma_mul_cos_le` is
  stated for `1/2 ≤ σ ≤ 3/2`.

## Build

```
lake exe cache get
lake build
```
