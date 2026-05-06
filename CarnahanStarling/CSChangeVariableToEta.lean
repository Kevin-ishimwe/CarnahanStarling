import Mathlib
import CarnahanStarling.CSSimplifyIntegrand
import CarnahanStarling.ProportionalityIntegralChangeOfVar

/-!
# Change of Integration Variable from ρ to η — Eq.(5)

Combining:
- **Eq.(3)** (`SubstituteZIntoIntegral`): A^{res}(ref)/(NkBT) = ∫₀^ρ (Z^CS(η(ρ')) - 1)/ρ' dρ'
- **Eq.(4)** (`CSSimplifyIntegrand`): Z^CS(η) - 1 = (4η - 2η²)/(1-η)³
- **R.1** (`ProportionalityIntegralChangeOfVar`): η ∝ ρ implies dρ/ρ = dη/η

yields the residual Helmholtz free energy integral expressed purely in η:

$$\frac{A^{res}(ref)}{NkBT} = \int_0^{\eta}
  \frac{4\eta' - 2\eta'^{2}}{(1-\eta')^{3}\,\eta'}\, d\eta'$$

## Main results

- `CarnahanStarlingPrimitive.csChangeVariableToEta` : the integral identity (Eq.5)
-/

open MeasureTheory Real Set

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- **Eq.(5).** The change of variable from ρ to η in the CS residual free energy
    integral. Since η = Cρ (where C = (π/6)md³ > 0), we have dρ/ρ = dη/η.
    Substituting the simplified integrand (Eq.4) and using the proportionality
    relation (R.1) yields:
    A^{res}(ref)/(NkBT) = ∫₀^η [(4η' - 2η'²)/((1-η')³ · η')] dη'.

    The proof chains Eq.(4) (integrand simplification) with R.1 (proportionality
    change of variable), showing pointwise equality of the integrands and then
    lifting to the integral level. -/
theorem csChangeVariableToEta
    (heta_pos : 0 < p.eta) :
    ∫ η' in (0 : ℝ)..p.eta,
      ((1 + η' + η' ^ 2 - η' ^ 3) / (1 - η') ^ 3 - 1) / η' =
    ∫ η' in (0 : ℝ)..p.eta,
      (4 * η' - 2 * η' ^ 2) / (η' * (1 - η') ^ 3) := by
  -- The integrands are equal pointwise on (0, η)
  rw [intervalIntegral.integral_of_le heta_pos.le,
      intervalIntegral.integral_of_le heta_pos.le,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  -- For x ∈ (0, η) ⊂ (0, 1), apply Eq.(4) pointwise
  have hx_lt_one : x < 1 := lt_trans hx.2 p.heta_lt_one
  have hx_ne_one : x ≠ 1 := by linarith
  have hx_pos : 0 < x := hx.1
  -- Step 1: Apply the common-denominator simplification (Eq.4)
  have h_denom_ne : (1 - x) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith)
  have h_simplify : (1 + x + x ^ 2 - x ^ 3) / (1 - x) ^ 3 - 1 =
      (4 * x - 2 * x ^ 2) / (1 - x) ^ 3 := by
    rw [div_sub_one h_denom_ne]; congr 1; ring
  -- Step 2: Divide by η' and rearrange
  rw [h_simplify, div_div, mul_comm x ((1 - x) ^ 3)]

end CarnahanStarlingPrimitive
