import Mathlib
import CarnahanStarling.CSSubstitutePackingDensity

/-!
# Expanded Carnahan-Starling Hard-Sphere Reference Term — Eq.(10)

$$\frac{A^{res}(ref)}{Nk_{B}T}
  = \frac{\tfrac{2\pi}{3}\rho m d^{3}
        - \tfrac{\pi^{2}}{12}\rho^{2} m^{2} d^{6}}
       {\bigl(1 - \tfrac{\pi}{6}\rho m d^{3}\bigr)^{2}}$$

This is obtained by expanding the compact Carnahan–Starling reference term
$(4\eta - 3\eta^{2})/(1-\eta)^{2}$ (Eq.7) after substituting
$\eta = \frac{\pi}{6}\rho m d^{3}$ (Eq.8).

The numerator expands in two steps:
- $4\eta = 4 \cdot \frac{\pi}{6}\rho m d^{3} = \frac{2\pi}{3}\rho m d^{3}$
- $3\eta^{2} = 3 \cdot \bigl(\frac{\pi}{6}\bigr)^{2}\rho^{2} m^{2} d^{6}
             = \frac{\pi^{2}}{12}\rho^{2} m^{2} d^{6}$

## Main results

- `PackingDensityParams.expandedCSReferenceTerm` : definition of Eq.(10)
- `PackingDensityParams.four_eta_expansion` : 4η = (2π/3)ρmd³
- `PackingDensityParams.three_eta_sq_expansion` : 3η² = (π²/12)ρ²m²d⁶
- `PackingDensityParams.expandedCSReferenceTerm_eq_compact` : Eq.(10) = compact form
-/

open Real

namespace PackingDensityParams

variable (params : PackingDensityParams)

/-- The expanded Carnahan-Starling hard-sphere reference term for the
    residual Helmholtz free energy per NkBT, expressed in terms of
    number density ρ, chain length m, and segment diameter d.
    Equation (10): A^{res}(ref)/(NkBT) = [(2π/3)ρmd³ − (π²/12)ρ²m²d⁶] / (1 − (π/6)ρmd³)² -/
noncomputable def expandedCSReferenceTerm : ℝ :=
  ((2 * Real.pi / 3) * params.ρ * params.m * params.d ^ 3 -
   (Real.pi ^ 2 / 12) * params.ρ ^ 2 * params.m ^ 2 * params.d ^ 6) /
  (1 - Real.pi / 6 * params.ρ * params.m * params.d ^ 3) ^ 2

/-! ### Intermediate algebraic steps -/

/-- **Numerator Step 1:** $4\eta = 4 \cdot (\pi/6)\rho m d^3 = (2\pi/3)\rho m d^3$.
    This expands the first term of the compact numerator. -/
theorem four_eta_expansion :
    4 * params.packingDensity =
    (2 * Real.pi / 3) * params.ρ * params.m * params.d ^ 3 := by
  unfold PackingDensityParams.packingDensity packingDensityFn; ring

/-- **Numerator Step 2:** $3\eta^2 = 3 \cdot (\pi/6)^2 \rho^2 m^2 d^6 = (\pi^2/12)\rho^2 m^2 d^6$.
    This expands the second term of the compact numerator. -/
theorem three_eta_sq_expansion :
    3 * params.packingDensity ^ 2 =
    (Real.pi ^ 2 / 12) * params.ρ ^ 2 * params.m ^ 2 * params.d ^ 6 := by
  unfold PackingDensityParams.packingDensity packingDensityFn; ring

/-! ### Main identity -/

/-- **Eq.(10).** The expanded CS reference term equals the compact form
    (4η − 3η²)/(1 − η)² when η = (π/6)ρmd³.

    Proof: substitute the expansions from `four_eta_expansion` and
    `three_eta_sq_expansion` into the compact numerator 4η − 3η², and
    unfold η in the denominator. -/
theorem expandedCSReferenceTerm_eq_compact :
    params.expandedCSReferenceTerm =
      (4 * params.packingDensity - 3 * params.packingDensity ^ 2) /
      (1 - params.packingDensity) ^ 2 := by
  unfold expandedCSReferenceTerm packingDensity packingDensityFn; ring

/-- The expanded reference term equals the csHelmholtzExpanded from Eq.(9). -/
theorem expandedCSReferenceTerm_eq_csHelmholtzExpanded :
    params.expandedCSReferenceTerm = params.csHelmholtzExpanded := by
  unfold expandedCSReferenceTerm csHelmholtzExpanded; ring

/-- The expanded reference term equals cs_antideriv at the packing density. -/
theorem expandedCSReferenceTerm_eq_antideriv :
    params.expandedCSReferenceTerm = cs_antideriv params.packingDensity := by
  rw [expandedCSReferenceTerm_eq_csHelmholtzExpanded,
      ← params.substitutePackingDensity]

end PackingDensityParams

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- **Bundled Eq.(10).** The expanded reference term at the primitive variables
    equals the compact CS form cs_antideriv(η), provided the packing density
    relation holds. -/
theorem expandedCSReferenceTerm_eq_cs_antideriv
    (params : PackingDensityParams)
    (hη_eq : p.eta = params.packingDensity) :
    params.expandedCSReferenceTerm = cs_antideriv p.eta := by
  rw [hη_eq, params.expandedCSReferenceTerm_eq_antideriv]

end CarnahanStarlingPrimitive
