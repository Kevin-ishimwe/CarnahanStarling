import Mathlib
import CarnahanStarling.SimplifyIntegrandEta
import CarnahanStarling.PackingDensity

/-!
# Substitution of Packing Density into the CS Reference Term — Eq.(9)

$$\frac{A^{res}(ref)}{Nk_{B}T}
  = \frac{4\bigl(\tfrac{\pi}{6}\rho m d^{3}\bigr)
        - 3\bigl(\tfrac{\pi}{6}\rho m d^{3}\bigr)^{2}}
       {\bigl(1 - \tfrac{\pi}{6}\rho m d^{3}\bigr)^{2}}$$

This is obtained by substituting $\eta = \frac{\pi}{6}\rho m d^{3}$ (Eq.8,
`packingDensityFn`) into the Carnahan–Starling reference term
$\frac{4\eta - 3\eta^{2}}{(1-\eta)^{2}}$ (Eq.7, `cs_antideriv`).

The identity is a direct algebraic substitution (definitional equality after
unfolding).

## Main results

- `PackingDensityParams.csHelmholtzExpanded` : the expanded form Eq.(9)
- `PackingDensityParams.substitutePackingDensity` : cs_antideriv ∘ packingDensity = csHelmholtzExpanded
-/

open Real

namespace PackingDensityParams

variable (params : PackingDensityParams)

/-- The Carnahan–Starling reduced residual Helmholtz free energy after substituting
    the packing density definition η = (π/6)ρmd³, expressed directly in terms of
    number density ρ, chain length m, and segment diameter d.  Eq.(9). -/
noncomputable def csHelmholtzExpanded : ℝ :=
  (4 * (Real.pi / 6 * params.ρ * params.m * params.d ^ 3) -
   3 * (Real.pi / 6 * params.ρ * params.m * params.d ^ 3) ^ 2) /
  (1 - Real.pi / 6 * params.ρ * params.m * params.d ^ 3) ^ 2

/-- The expanded form unfolds to the substituted expression. -/
theorem csHelmholtzExpanded_eq :
    params.csHelmholtzExpanded =
      (4 * params.packingDensity - 3 * params.packingDensity ^ 2) /
      (1 - params.packingDensity) ^ 2 := by
  unfold csHelmholtzExpanded packingDensity packingDensityFn; ring

/-- **Eq.(9).** Substituting the packing density η = (π/6)ρmd³ (Eq.8) into the
    CS reference term (4η − 3η²)/(1 − η)² (Eq.7) yields the expanded form
    expressed in terms of ρ, m, d.

    This is a direct algebraic substitution identity: unfolding
    `cs_antideriv` and `packingDensityFn` produces definitionally equal
    expressions, closed by `ring`. -/
theorem substitutePackingDensity :
    cs_antideriv params.packingDensity = params.csHelmholtzExpanded := by
  unfold cs_antideriv packingDensity packingDensityFn csHelmholtzExpanded
  ring

end PackingDensityParams

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- **Bundled Eq.(9).** At the primitive variables, substituting the packing
    density into the CS reference term yields the expanded density form,
    provided the defining relation η = packingDensityFn(ρ, m, d) holds. -/
theorem substitutePackingDensity
    (heta_eq : p.eta = packingDensityFn p.rho p.m p.d)
    (params : PackingDensityParams)
    (hρ_eq : params.ρ = p.rho) (hm_eq : params.m = p.m) (hd_eq : params.d = p.d) :
    cs_antideriv p.eta = params.csHelmholtzExpanded := by
  rw [heta_eq, show packingDensityFn p.rho p.m p.d = params.packingDensity by
    unfold PackingDensityParams.packingDensity packingDensityFn; rw [hρ_eq, hm_eq, hd_eq]]
  exact params.substitutePackingDensity

end CarnahanStarlingPrimitive
