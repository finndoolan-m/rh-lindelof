# rh-lindelof

Lean 4 formalisation of **the Riemann hypothesis implies the Lindelöf hypothesis**
(Littlewood; Titchmarsh §14.2), stated against Mathlib's `RiemannHypothesis`.

Built on [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) for
the strip bound on ζ and the Gamma bounds.

## Status

All lemmas are stated in `RHLindelof/Main.lean`. The main theorem is proved from steps 1–7, which are still `sorry`.

| Step | Lemma | Uses RH | Status |
|---|---|---|---|
| 1 | `norm_riemannZeta_le_linear`, `norm_riemannZeta_bounds_of_two_le` | no | sorry |
| 2 | `exists_log_riemannZeta` | yes | sorry |
| 3 | `norm_log_riemannZeta_le` (Borel–Carathéodory) | yes | sorry |
| 4 | `norm_le_of_three_circles` | no | sorry |
| 5 | `norm_riemannZeta_le_rpow_right` | yes | sorry |
| 6 | `norm_gamma_mul_cos_le`, `norm_riemannZeta_le_rpow_left` | no | sorry |
| 7 | `norm_le_of_phragmenLindelof_convexity`, `norm_riemannZeta_le_poly_strip` | no | sorry |
| 8 | `lindelof_of_riemannHypothesis` (from steps 1–7) | yes | proved |

## Build

```
lake exe cache get
lake build
```
