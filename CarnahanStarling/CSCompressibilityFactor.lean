import Mathlib
import CarnahanStarling.CarnahanStarlingPrimitive

/-!
# Carnahan-Starling Compressibility Factor — Eq.(1)

The Carnahan-Starling compressibility factor for a hard-sphere fluid:

$$Z^{CS}(\eta) = \frac{1 + \eta + \eta^2 - \eta^3}{(1 - \eta)^3}$$

where η is the packing fraction with 0 ≤ η < 1.

This describes the repulsive (hard-sphere reference) contribution
in the SAFT equation of state.

## Main results

- `CarnahanStarlingPrimitive.csCompressibilityFactor` : Z^CS at the bundled η
- `CarnahanStarlingPrimitive.csCompressibilityFactor_pos` : positivity
- `CarnahanStarlingPrimitive.csCompressibilityFactor_at_zero` : ideal gas limit
-/

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- The Carnahan-Starling compressibility factor evaluated at the bundled
    packing fraction η ∈ [0, 1):
    Z^{CS}(η) = (1 + η + η² − η³) / (1 − η)³. -/
noncomputable def csCompressibilityFactor : ℝ :=
  (1 + p.eta + p.eta ^ 2 - p.eta ^ 3) / (1 - p.eta) ^ 3

/-- The CS compressibility factor unfolds to the rational expression. -/
theorem csCompressibilityFactor_eq :
    p.csCompressibilityFactor =
      (1 + p.eta + p.eta ^ 2 - p.eta ^ 3) / (1 - p.eta) ^ 3 := rfl

/-- For η ∈ [0, 1), the Carnahan-Starling compressibility factor is positive. -/
theorem csCompressibilityFactor_pos : 0 < p.csCompressibilityFactor := by
  unfold csCompressibilityFactor
  apply div_pos
  · nlinarith [sq_nonneg p.eta, sq_nonneg (1 - p.eta), p.heta_nonneg, p.heta_lt_one]
  · have : 0 < 1 - p.eta := by linarith [p.heta_lt_one]
    positivity

/-- At η = 0, the compressibility factor equals 1 (ideal gas limit). -/
theorem csCompressibilityFactor_at_zero (h : p.eta = 0) :
    p.csCompressibilityFactor = 1 := by
  unfold csCompressibilityFactor; rw [h]; norm_num

end CarnahanStarlingPrimitive
