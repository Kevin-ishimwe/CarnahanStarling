import Mathlib
import CarnahanStarling.CarnahanStarlingPrimitive

/-!
# Packing Density Definition — Eq.(8)

The packing density η for a hard-sphere fluid in the SAFT framework:

$$\eta = \frac{\pi}{6}\,\rho\,m\,d^{3}$$

where:
- ρ is the number density (ρ > 0),
- m is the chain length (m ≥ 1),
- d is the segment diameter (d > 0).

The result η must satisfy 0 ≤ η < 1 for physical validity.

## Main results

- `PackingDensityParams` : structure bundling physical constraints
- `PackingDensityParams.packingDensity` : η = (π/6) · ρ · m · d³
- `PackingDensityParams.packingDensity_nonneg` : η ≥ 0
- `PackingDensityParams.packingDensity_mem_Ico` : η ∈ [0, 1)
- `CarnahanStarlingPrimitive.eta_eq_packingDensity` : bundled recovery
-/

open Real

/-- The packing density formula η = (π/6) · ρ · m · d³ as a standalone function.
    This is needed to state the well-formedness constraint in `PackingDensityParams`
    (the structure must reference the formula before bundling it as a method). -/
noncomputable def packingDensityFn (ρ : ℝ) (m : ℝ) (d : ℝ) : ℝ :=
  (Real.pi / 6) * ρ * m * d ^ 3

/-- Structure bundling the physical constraints on packing density inputs. -/
structure PackingDensityParams where
  /-- Number density -/
  ρ : ℝ
  /-- Chain length -/
  m : ℝ
  /-- Segment diameter -/
  d : ℝ
  /-- Number density is strictly positive -/
  hρ_pos : 0 < ρ
  /-- Chain length is at least 1 -/
  hm_ge_one : 1 ≤ m
  /-- Segment diameter is strictly positive -/
  hd_pos : 0 < d
  /-- Packing density is less than 1 (physical validity) -/
  hη_lt_one : packingDensityFn ρ m d < 1

namespace PackingDensityParams

variable (params : PackingDensityParams)

/-- The packing density η = (π/6) · ρ · m · d³ for the bundled parameters. -/
noncomputable def packingDensity : ℝ :=
  packingDensityFn params.ρ params.m params.d

/-- The packing density unfolds to the formula. -/
theorem packingDensity_eq :
    params.packingDensity = (Real.pi / 6) * params.ρ * params.m * params.d ^ 3 := rfl

/-- The packing density is non-negative when all inputs are non-negative. -/
theorem packingDensity_nonneg : 0 ≤ params.packingDensity := by
  unfold packingDensity packingDensityFn
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · exact div_nonneg (le_of_lt Real.pi_pos) (by norm_num)
  · exact le_of_lt params.hρ_pos
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) params.hm_ge_one
  · exact pow_nonneg (le_of_lt params.hd_pos) 3

/-- The packing density for valid parameters lies in [0, 1). -/
theorem packingDensity_mem_Ico :
    params.packingDensity ∈ Set.Ico 0 1 :=
  ⟨params.packingDensity_nonneg, params.hη_lt_one⟩

end PackingDensityParams

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- The bundled packing density evaluated at the primitive variables
    equals the stored η field, assuming the defining relation holds. -/
theorem eta_eq_packingDensity
    (h : p.eta = packingDensityFn p.rho p.m p.d) :
    p.eta = (Real.pi / 6) * p.rho * p.m * p.d ^ 3 := by
  rw [h]; rfl

end CarnahanStarlingPrimitive
