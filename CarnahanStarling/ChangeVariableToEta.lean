import Mathlib
import CarnahanStarling.CSChangeVariableToEta

/-!
# Simplification of the η-Integrand — Eq.(6)

After the change of variable from ρ to η (Eq.5), the residual Helmholtz
free energy integral has integrand

$$\frac{4\eta - 2\eta^{2}}{(1-\eta)^{3}\,\eta}$$

By factoring η from the numerator, 4η − 2η² = η(4 − 2η), and cancelling
with the η in the denominator, the integrand simplifies to

$$\frac{4 - 2\eta}{(1-\eta)^{3}}$$

giving Eq.(6):

$$\frac{A^{res}(ref)}{Nk_{B}T}
  = \int_{0}^{\eta}\!\frac{4 - 2\eta'}{(1-\eta')^{3}}\,d\eta'$$

## Main results

- `CarnahanStarlingPrimitive.csIntegrandCancelEta` : pointwise algebraic cancellation
- `CarnahanStarlingPrimitive.csRefIntegralSimplified` : integral equality (Eq.6)
-/

open MeasureTheory Real Set

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- Pointwise simplification of the Carnahan-Starling integrand: cancelling η
    from numerator and denominator by factoring 4η - 2η² = η(4 - 2η).
    For η ∈ (0, 1):
    (4η - 2η²) / ((1 - η)³ · η) = (4 - 2η) / (1 - η)³.
    This is the core algebraic step from Eq.(5) to Eq.(6). -/
theorem csIntegrandCancelEta (η' : ℝ) (hη'_pos : 0 < η') (hη'_lt : η' < 1) :
    (4 * η' - 2 * η' ^ 2) / ((1 - η') ^ 3 * η') = (4 - 2 * η') / (1 - η') ^ 3 := by
  have hη'_ne : η' ≠ 0 := ne_of_gt hη'_pos
  have h1mη'_ne : (1 - η') ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith)
  -- Factor η from numerator: 4η - 2η² = η(4 - 2η), then cancel with η in denominator
  field_simp

/-- **Eq.(6).** The integral form of the reduced residual Helmholtz free energy
    after cancelling η in the integrand:
    ∫₀^η ((4t - 2t²)/((1-t)³ · t)) dt = ∫₀^η ((4 - 2t)/(1-t)³) dt.
    The proof lifts the pointwise cancellation `csIntegrandCancelEta` to the
    integral level using `setIntegral_congr_fun`. -/
theorem csRefIntegralSimplified (heta_pos : 0 < p.eta) :
    ∫ t in (0 : ℝ)..p.eta, (4 * t - 2 * t ^ 2) / ((1 - t) ^ 3 * t) =
    ∫ t in (0 : ℝ)..p.eta, (4 - 2 * t) / (1 - t) ^ 3 := by
  rw [intervalIntegral.integral_of_le heta_pos.le,
      intervalIntegral.integral_of_le heta_pos.le]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by
    rw [div_eq_div_iff] <;>
      nlinarith [hx.1, hx.2, p.heta_lt_one, pow_pos (show 0 < 1 - x by linarith [hx.2, p.heta_lt_one]) 3]

end CarnahanStarlingPrimitive
