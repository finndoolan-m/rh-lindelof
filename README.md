# rh-lindelof

A Lean 4 proof that **the Riemann hypothesis implies the Lindelöf hypothesis** (Littlewood, 1912;
Titchmarsh, *The Theory of the Riemann Zeta-Function*, §14.2). It is sorry-free and stated
against Mathlib's own `RiemannHypothesis`.

```lean
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) : LindelofHypothesis
```

`#print axioms RHLindelof.lindelof_of_riemannHypothesis` gives
`[propext, Classical.choice, Quot.sound]`.

Several of the intermediate results are unconditional and reusable on their own:
Hadamard's three-circle theorem, Phragmén–Lindelöf convexity in a vertical strip, the bound
`Γ(s) cos(πs/2) ≪ |t|^(σ − 1/2)`, and explicit bounds for `ζ` on `σ ≥ 2`.

## Files

| File | Contents | Uses RH |
|---|---|---|
| `RHLindelof/ZetaBounds.lean` | `‖ζ(s) − 1‖ ≤ π²/6 − 1` on `σ ≥ 2`; `‖ζ(σ + it)‖ ≪ |t|` on `1/2 ≤ σ ≤ 6` | no |
| `RHLindelof/LogZeta.lean` | holomorphic `log ζ` on the ball of radius `5/2` about `3 + it`; Borel–Carathéodory bound | yes |
| `RHLindelof/ThreeCircles.lean` | Hadamard's three-circle theorem | no |
| `RHLindelof/RightOfLine.lean` | `ζ(σ + it) = O(|t|^ε)` for `σ ≥ 1/2 + δ` | yes |
| `RHLindelof/Convexity.lean` | Phragmén–Lindelöf convexity for functions of exponential growth | no |
| `RHLindelof/FunctionalEquation.lean` | `Γ(s) cos(πs/2)` bound; moving bounds to `σ = 1/2 − η`; growth in the strip | no |
| `RHLindelof/Main.lean` | the main theorem | yes |

## Proof outline

1. Under RH, `ζ` has no zeros in `σ > 1/2`. It therefore has a holomorphic logarithm on the
   ball of radius `5/2` about `3 + it`.
2. `ζ ≪ |t|` there, so `Re log ζ ≤ log |t| + O(1)`. Borel–Carathéodory turns this into
   `|log ζ| ≪ log |t| / δ` on the ball of radius `5/2 − δ`.
3. On the circle of radius `1/2`, `log ζ = O(1)`. Three circles then give
   `log ζ(σ + it) = O((log t)^θ)` with `θ < 1`, so `ζ(σ + it) = O(|t|^ε)` for `σ > 1/2`.
4. The functional equation turns this into `ζ(1/2 − η + it) = O(|t|^(η + ε))`. Convexity on
   `[1/2 − η, 1/2 + η]` then gives `ζ(1/2 + it) = O(|t|^(η/2 + ε))`. Letting `η → 0` finishes.

## Notes on the formalisation

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

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain is Lean v4.35.0, and the
dependency is [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
at commit `a4fb698`, which brings in Mathlib.

```
lake exe cache get
lake build
```

To check the axioms, compile a file containing

```lean
import RHLindelof
#print axioms RHLindelof.lindelof_of_riemannHypothesis
```

## Acknowledgements

Built on [Mathlib](https://github.com/leanprover-community/mathlib4): `riemannZeta`, the
functional equation, Borel–Carathéodory, the three-lines theorem and primitives on discs. Also
built on [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): the
linear strip bound for `ζ` and Gamma bounds on the critical line.

## License

Apache 2.0, the same as Mathlib and PrimeNumberTheoremAnd.
