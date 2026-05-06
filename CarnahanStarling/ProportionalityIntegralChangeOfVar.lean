import Mathlib
import CarnahanStarling.CarnahanStarlingPrimitive

/-!
# Proportionality Relation R.1 — Change of Integration Variable

From Eq. (8): η = (π/6) ρ m d³, so η = C · ρ where C > 0 is a constant.
This proportionality relation (R.1) states that dρ/ρ = dη/η, justifying the
change of integration variable from ρ to η in going from Eq. (3) to Eq. (5):

$$\int_{0}^{\rho}\frac{Z(\eta(\rho')) - 1}{\rho'}d\rho'
  = \int_{0}^{\eta}\frac{Z(\eta') - 1}{\eta'}d\eta'$$

## Main results

- `CarnahanStarlingPrimitive.proportionalityIntegralChangeOfVar` :
    the change-of-variable identity at the bundled density and packing fraction
-/

open MeasureTheory Real

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- **R.1 — Proportionality integral change of variable.**
    If η = C * ρ for a positive constant C, then the integral of a function
    divided by the variable is invariant under this linear change of variables:
    ∫₀^ρ g(C·ρ')/ρ' dρ' = ∫₀^η g(η')/η' dη'.
    This justifies the substitution from Eq.(3) to Eq.(5) in the SAFT derivation.

    The proof uses `intervalIntegral.integral_comp_mul_left` for the linear
    substitution u = C · ρ', combined with the pointwise identity
    g(C·ρ)/ρ = (g(·)/·)(C·ρ) · C which holds because C/ρ · (1/C) = 1/ρ
    (and also at ρ = 0 by Lean's 0⁻¹ = 0 convention). -/
theorem proportionalityIntegralChangeOfVar
    {g : ℝ → ℝ} {C : ℝ} (hC : 0 < C) (heta_eq : p.eta = C * p.rho) :
    (∫ ρ' in (0 : ℝ)..p.rho, g (C * ρ') / ρ') =
    (∫ η' in (0 : ℝ)..p.eta, g η' / η') := by
  rw [heta_eq]
  convert intervalIntegral.integral_comp_mul_left _ hC.ne' using 3
  any_goals exact fun x => g x / x * C
  · grind
  · simp +decide [div_eq_inv_mul, mul_comm, hC.ne']

end CarnahanStarlingPrimitive
