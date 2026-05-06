import Mathlib
import CarnahanStarling.ChangeVariableToEta

/-!
# Carnahan–Starling Reference Term — Eq.(7)

Evaluating the integral from Eq.(6),

$$\int_0^{\eta}\frac{4 - 2\eta'}{(1-\eta')^{3}}\,d\eta'
  = \frac{4\eta - 3\eta^{2}}{(1 - \eta)^{2}},$$

yields the **Carnahan–Starling hard-sphere reference term** for the
reduced residual Helmholtz free energy A^{res}(ref)/(Nk_BT).

The proof proceeds by the Fundamental Theorem of Calculus:
1. Define the antiderivative F(t) = (4t − 3t²)/(1 − t)²
2. Verify F(0) = 0 (ideal gas limit)
3. Compute F'(t) = (4 − 2t)/(1 − t)³ by the quotient rule
4. Apply the FTC: ∫₀^η f(t) dt = F(η) − F(0) = F(η)

## Main results

- `CarnahanStarlingPrimitive.csReferenceTerm` : definition of (4η − 3η²)/(1 − η)²
- `CarnahanStarlingPrimitive.csReferenceTerm_nonneg` : non-negativity
- `CarnahanStarlingPrimitive.csReferenceTerm_zero` : vanishes when η = 0
- `CarnahanStarlingPrimitive.csReferenceIntegralEq` : ∫₀^η f(t) dt = csReferenceTerm
-/

open MeasureTheory Real Set

/-!
### Antiderivative helper

The function F(t) = (4t − 3t²)/(1 − t)² serves as the antiderivative for the
integrand (4 − 2t)/(1 − t)³. It is defined as a standalone `ℝ → ℝ` function
because Lean's `HasDerivAt` API requires a function, not a structure method.
-/

/-- The antiderivative F(t) = (4t − 3t²)/(1 − t)² used in the FTC proof.
    This is an integration helper required by Lean's analysis API. -/
noncomputable def cs_antideriv (t : ℝ) : ℝ :=
  (4 * t - 3 * t ^ 2) / (1 - t) ^ 2

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-! ### Definition and basic properties -/

/-- The Carnahan–Starling hard-sphere reference term for the residual Helmholtz
    free energy, normalized by NkBT:
    (4η − 3η²) / (1 − η)². -/
noncomputable def csReferenceTerm : ℝ :=
  (4 * p.eta - 3 * p.eta ^ 2) / (1 - p.eta) ^ 2

/-- The CS reference term unfolds to the rational expression. -/
theorem csReferenceTerm_eq :
    p.csReferenceTerm = (4 * p.eta - 3 * p.eta ^ 2) / (1 - p.eta) ^ 2 := rfl

/-- The CS reference term equals cs_antideriv at p.eta. -/
theorem csReferenceTerm_eq_antideriv :
    p.csReferenceTerm = cs_antideriv p.eta := rfl

/-- The CS reference term is non-negative for η ∈ [0, 1). -/
theorem csReferenceTerm_nonneg : 0 ≤ p.csReferenceTerm := by
  unfold csReferenceTerm
  apply div_nonneg
  · nlinarith [p.heta_nonneg, p.heta_lt_one]
  · positivity

/-- The CS reference term vanishes when η = 0 (ideal gas limit). -/
theorem csReferenceTerm_zero (h : p.eta = 0) : p.csReferenceTerm = 0 := by
  unfold csReferenceTerm; rw [h]; simp

/-! ### FTC proof: ∫₀^η (4 − 2t)/(1 − t)³ dt = (4η − 3η²)/(1 − η)² -/

/-- **FTC Step 1: F(0) = 0.** The antiderivative vanishes at the origin. -/
private theorem antideriv_at_zero : cs_antideriv 0 = 0 := by
  unfold cs_antideriv; simp

/-- **FTC Step 2: F'(t) = (4 − 2t)/(1 − t)³.**
    The derivative of F(t) = (4t − 3t²)/(1 − t)² is computed by the quotient rule:
    d/dt [(4t − 3t²)/(1 − t)²]
      = [(4 − 6t)(1 − t)² + 2(1 − t)(4t − 3t²)] / (1 − t)⁴
      = (4 − 2t) / (1 − t)³. -/
private theorem antideriv_hasDerivAt (t : ℝ) (ht : t ≠ 1) :
    HasDerivAt cs_antideriv ((4 - 2 * t) / (1 - t) ^ 3) t := by
  have h_num : HasDerivAt (fun t : ℝ => 4 * t - 3 * t ^ 2) (4 - 6 * t) t := by
    convert HasDerivAt.sub
      (HasDerivAt.const_mul 4 (hasDerivAt_id t))
      (HasDerivAt.const_mul 3 (hasDerivAt_pow 2 t)) using 1; ring
  have h_denom : HasDerivAt (fun t : ℝ => (1 - t) ^ 2) (-2 * (1 - t)) t := by
    convert HasDerivAt.comp t (hasDerivAt_pow 2 (1 - t))
      (hasDerivAt_id' t |> HasDerivAt.const_sub 1) using 1; ring!
  convert HasDerivAt.div h_num h_denom
    (pow_ne_zero 2 <| sub_ne_zero_of_ne ht.symm) using 1
  have h1mt : (1 - t) ≠ 0 := sub_ne_zero_of_ne ht.symm
  field_simp
  ring

/-- **FTC Step 3: Integrability.**
    The integrand (4 − 2t)/(1 − t)³ is continuous on [0, η] for η < 1,
    ensuring integrability for the FTC application. -/
private theorem integrand_continuousOn :
    ContinuousOn (fun t => (4 - 2 * t) / (1 - t) ^ 3) (Set.Icc 0 p.eta) := by
  exact continuousOn_of_forall_continuousAt fun t ht =>
    ContinuousAt.div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
      (ContinuousAt.pow (continuousAt_const.sub continuousAt_id) _)
      (pow_ne_zero _ <| by linarith [ht.2, p.heta_lt_one])

/-- **Eq.(7).** Evaluating the integral from Eq.(6) via the Fundamental Theorem
    of Calculus:
    ∫₀^η (4 − 2t)/(1 − t)³ dt = F(η) − F(0) = F(η) = (4η − 3η²)/(1 − η)².

    The proof applies `integral_eq_sub_of_hasDerivAt` with:
    - Antiderivative: F(t) = (4t − 3t²)/(1 − t)²
    - F(0) = 0 (Step 1)
    - F'(t) = (4 − 2t)/(1 − t)³ (Step 2, quotient rule)
    - Continuity/integrability on [0, η] (Step 3) -/
theorem csReferenceIntegralEq (heta_pos : 0 < p.eta) :
    ∫ t in (0 : ℝ)..p.eta, (4 - 2 * t) / (1 - t) ^ 3 = p.csReferenceTerm := by
  -- Apply FTC: ∫₀^η f(t) dt = F(η) − F(0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    -- The antiderivative F is cs_antideriv
    (fun x hx => by
      have hx_ne_one : x ≠ 1 := by
        cases Set.mem_uIcc.mp hx <;> linarith [p.heta_lt_one]
      exact antideriv_hasDerivAt x hx_ne_one)
    -- Integrability: the integrand is continuous on [0, η]
    (by
      apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        (ContinuousOn.pow (continuousOn_const.sub continuousOn_id) _)
        fun x hx => pow_ne_zero _ <| sub_ne_zero_of_ne <| by
          cases Set.mem_uIcc.mp hx <;> linarith [p.heta_lt_one])]
  -- F(η) − F(0) = F(η) since F(0) = 0
  simp [csReferenceTerm, cs_antideriv]

end CarnahanStarlingPrimitive
