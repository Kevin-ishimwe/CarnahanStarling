import Mathlib
import CarnahanStarling.SubstituteZIntoIntegral

/-!
# Simplification of the Carnahan–Starling Integrand — Eq.(4)

The Carnahan–Starling compressibility factor minus 1 simplifies as:

$$\frac{1 + \eta + \eta^{2} - \eta^{3}}{(1 - \eta)^{3}} - 1
  = \frac{4\eta - 2\eta^{2}}{(1 - \eta)^{3}}$$

This is the algebraic identity underlying Eq.(4) of the derivation:
the integrand used to derive the CS Helmholtz free energy from the
thermodynamic relation $A^{res}/(NkT) = \int_0^{\rho} (Z-1)/\rho\, d\rho$.

The proof mirrors the paper's derivation:
1. Form a common denominator: (Z^CS − 1) = (Z^CS · (1−η)³ − (1−η)³) / (1−η)³
2. Expand the numerator: (1+η+η²−η³) − (1−η)³ = 4η − 2η²

## Main results

- `CarnahanStarlingPrimitive.cs_numerator_identity` : numerator expansion step
- `CarnahanStarlingPrimitive.csSimplifyIntegrand` : the full simplification
-/

open MeasureTheory Real Set

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- **Step 1 of Eq.(4):** Numerator expansion after forming a common denominator.
    (1 + η + η² − η³) − (1 − η)³ = 4η − 2η².
    This is the core algebraic identity: expanding (1−η)³ = 1 − 3η + 3η² − η³
    and subtracting from the CS numerator. -/
theorem cs_numerator_identity :
    (1 + p.eta + p.eta ^ 2 - p.eta ^ 3) - (1 - p.eta) ^ 3 =
    4 * p.eta - 2 * p.eta ^ 2 := by ring

/-- **Eq.(4).** Simplification of the Carnahan–Starling integrand.
    The CS compressibility factor Z^CS minus 1 simplifies by forming a common
    denominator and using the numerator identity:
    (1 + η + η² − η³)/(1 − η)³ − 1 = (4η − 2η²)/(1 − η)³.

    Proof:
    1. Rewrite a/b − 1 as (a − b)/b using `div_sub_one` (common denominator)
    2. Apply `cs_numerator_identity` to simplify the numerator -/
theorem csSimplifyIntegrand :
    (1 + p.eta + p.eta ^ 2 - p.eta ^ 3) / (1 - p.eta) ^ 3 - 1 =
    (4 * p.eta - 2 * p.eta ^ 2) / (1 - p.eta) ^ 3 := by
  have h_denom_ne : (1 - p.eta) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (by linarith [p.heta_lt_one])
  -- Step 1: Form a common denominator: a/b − 1 = (a − b)/b
  rw [div_sub_one h_denom_ne]
  -- Step 2: Simplify the numerator using the algebraic identity
  congr 1
  exact p.cs_numerator_identity

end CarnahanStarlingPrimitive
