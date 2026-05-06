import Mathlib
import CarnahanStarling.CSCompressibilityFactor
import CarnahanStarling.CSHelmholtzResidual

/-!
# Substitution of the CS Compressibility Factor into the Helmholtz Integral — Eq.(3)

Substituting the Carnahan-Starling compressibility factor (Eq.1)

$$Z^{CS}(\eta) = \frac{1 + \eta + \eta^2 - \eta^3}{(1 - \eta)^3}$$

into the thermodynamic relation (Eq.2)

$$\frac{A^{res}(ref)}{N k_B T} = \int_0^{\rho} \frac{Z(\rho') - 1}{\rho'}\, d\rho'$$

yields Eq.(3):

$$\frac{A^{res}(ref)}{N k_B T}
  = \int_0^{\rho}
      \frac{\frac{1 + \eta + \eta^2 - \eta^3}{(1 - \eta)^3} - 1}{\rho}\, d\rho$$

## Main results

- `CarnahanStarlingPrimitive.substituteZIntoIntegral` : the substitution identity
-/

open MeasureTheory Real Set

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- **Eq.(3).** Substituting the CS compressibility factor Z^CS(η(ρ')) (Eq.1) into
    the Helmholtz integral (Eq.2). The integrand is expressed using the explicit
    rational form of Z^CS, yielding a definitionally equal expression. -/
theorem substituteZIntoIntegral (η : ℝ → ℝ) :
    p.helmholtzFromZ (fun ρ' => (1 + η ρ' + (η ρ') ^ 2 - (η ρ') ^ 3) / (1 - η ρ') ^ 3) =
      ∫ ρ' in (0 : ℝ)..p.rho,
        ((1 + η ρ' + (η ρ') ^ 2 - (η ρ') ^ 3) / (1 - η ρ') ^ 3 - 1) / ρ' := by
  unfold helmholtzFromZ
  rfl

end CarnahanStarlingPrimitive
