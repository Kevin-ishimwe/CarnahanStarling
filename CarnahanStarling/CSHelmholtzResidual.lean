import Mathlib
import CarnahanStarling.CarnahanStarlingPrimitive

/-!
# Residual Helmholtz Free Energy from the Compressibility Factor — Eq.(2)

The reduced residual Helmholtz free energy for a hard-sphere reference fluid:

$$\frac{A^{res}(ref)}{N k_B T} = \int_0^{\rho} \frac{Z(\rho') - 1}{\rho'}\, d\rho'$$

This is the standard thermodynamic identity relating the residual Helmholtz free
energy to the compressibility factor Z(ρ) via an integral over number density.

## Main results

- `CarnahanStarlingPrimitive.helmholtzFromZ` : A^{res}/(NkBT) as an integral
- `CarnahanStarlingPrimitive.helmholtz_res_ref_eq` : recovery of unnormalized A^{res}
-/

open MeasureTheory Real

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- The reduced residual Helmholtz free energy for a hard-sphere reference fluid,
    A^{res}(ref)/(N k_B T) = ∫₀^ρ (Z(ρ') − 1)/ρ' dρ',
    where Z is the compressibility factor and ρ is the system number density. -/
noncomputable def helmholtzFromZ (Z : ℝ → ℝ) : ℝ :=
  ∫ ρ' in (0 : ℝ)..p.rho, (Z ρ' - 1) / ρ'

/-- Recovery of the unnormalized residual Helmholtz free energy:
    A^{res} = N · k_B · T · ∫₀^ρ (Z(ρ') − 1)/ρ' dρ'. -/
theorem helmholtz_res_ref_eq (A_res_ref : ℝ) (Z : ℝ → ℝ)
    (hT : 0 < p.T)
    (h : A_res_ref / (↑p.N * p.k_B * p.T) = p.helmholtzFromZ Z) :
    A_res_ref = ↑p.N * p.k_B * p.T * p.helmholtzFromZ Z := by
  have hN_pos : (0 : ℝ) < ↑p.N := Nat.cast_pos.mpr p.N_pos
  have hNkBT : ↑p.N * p.k_B * p.T ≠ 0 := ne_of_gt (mul_pos (mul_pos hN_pos p.hk_B) hT)
  rw [div_eq_iff hNkBT] at h
  linarith

end CarnahanStarlingPrimitive
