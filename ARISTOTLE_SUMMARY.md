# Summary of changes for run fe55bcea-afb9-4399-b2dd-cfcc35891a96
## Refactored Carnahan-Starling Formalization

All three critique areas (Coupling, Hierarchy, Fidelity) have been addressed. The project builds cleanly with no `sorry` statements and only standard axioms.

### Coupling Fixes
All root-level definitions and theorems now accept `CarnahanStarlingPrimitive` or `PackingDensityParams` directly:

- **`CSCompressibilityFactor`** → `CarnahanStarlingPrimitive.csCompressibilityFactor` (structure method)
- **`HelmholtzFromZ`** → `CarnahanStarlingPrimitive.helmholtzFromZ` (structure method)
- **`CSReferenceTerm`** → `CarnahanStarlingPrimitive.csReferenceTerm` (structure method)
- **`ExpandedCSReferenceTerm`** → `PackingDensityParams.expandedCSReferenceTerm` (structure method)
- **`csHelmholtzExpandedDensity`** → `PackingDensityParams.csHelmholtzExpanded` (structure method)
- **`packingDensity`** → `PackingDensityParams.packingDensity` (structure method)
- All theorems (`csSimplifyIntegrand`, `csChangeVariableToEta`, `csRefIntegralSimplified`, `csReferenceIntegralEq`, `proportionalityIntegralChangeOfVar`, etc.) now accept the bundled structure.
- Only two standalone helper functions remain, justified by Lean's type system: `cs_antideriv` (needed for `HasDerivAt` API) and `packingDensityFn` (needed for `PackingDensityParams` structure constraint field).
- All `_root_` delegation wrappers eliminated — proofs are now direct.

### Hierarchy (DRY) Fixes
- **Removed `Z_CS`** — duplicate of the CS compressibility factor formula. Integrals now use inline expressions.
- **Removed `Z_CS_eq_CSCompressibilityFactor`** — bridge lemma that existed only because of duplication.
- **Removed `Z_CS_sub_one`** — used the removed `Z_CS`.
- **Removed trivial one-liner lemmas** from `CarnahanStarlingPrimitive`: `Z_ne_zero`, `d_ne_zero`, `k_B_ne_zero`, `Z_nonneg`, `d_nonneg`, `m_nonneg`, `k_B_nonneg`, `one_sub_eta_pos`, `one_sub_eta_ne_zero`. These are now inlined (`by positivity`, `by linarith`, `ne_of_gt ...`) at use sites.
- **Removed `CSCompressibilityFactor_denom_pos`**, `CSCompressibilityFactor_denom_ne_zero`, `CSReferenceTerm_denom_pos` — trivial positivity facts, now inlined.
- **Removed `integrand_eq`** private lemma — generic algebraic identity, now inlined.

### Fidelity Fixes
- **Eq.(4)**: Added explicit `cs_numerator_identity` intermediate lemma showing the numerator expansion `(1+η+η²−η³) − (1−η)³ = 4η − 2η²`. Proof explicitly shows the common-denominator step via `div_sub_one` followed by the numerator identity — mirroring the paper's derivation.
- **Eq.(7) FTC**: Proof now explicitly shows all three FTC steps: `antideriv_at_zero` (F(0) = 0), `antideriv_hasDerivAt` (quotient rule derivative), `integrand_continuousOn` (integrability). No `aesop` — the connection F(0)=0 is now a clear `simp` step.
- **Eq.(10)**: Added intermediate algebraic lemmas `four_eta_expansion` (4η = (2π/3)ρmd³) and `three_eta_sq_expansion` (3η² = (π²/12)ρ²m²d⁶) matching the paper's expansion steps.
- **Import graph** matches the derivation DAG: Eq.1 → Eq.2 → Eq.3 → Eq.4 → R.1 → Eq.5 → Eq.6 → Eq.7 → Eq.8 → Eq.9 → Eq.10.

# Summary of changes for run ad91ec06-f351-4ebb-b405-b129116cad0e
The formalization in `RequestProject/ExpandedCSReferenceTerm.lean` is already complete and verified. It contains:

1. **`ExpandedCSReferenceTerm`** — The definition of the expanded Carnahan-Starling hard-sphere reference term (Eq. 10):
   `A^{res}(ref)/(NkBT) = [(2π/3)ρmd³ − (π²/12)ρ²m²d⁶] / (1 − (π/6)ρmd³)²`

2. **`expandedCSReferenceTerm_eq_compact`** — Proof that Eq. 10 equals the compact form `(4η − 3η²)/(1−η)²` when `η = (π/6)ρmd³`, proved by `ring`.

3. **`expandedCSReferenceTerm_eq_csHelmholtzExpandedDensity`** — Consistency with `csHelmholtzExpandedDensity` from the substitution step (Eq. 9).

4. **Bundled forms** in the `CarnahanStarlingPrimitive` namespace, including `expandedCSReferenceTerm` and `expandedCSReferenceTerm_eq_cs_antideriv`, reusing the existing `CSReferenceTerm` and `ExpandedCSReferenceTerm` dependencies.

The file builds successfully with no `sorry` statements, no axioms beyond the standard ones, and properly imports and reuses existing project infrastructure (`CSSubstitutePackingDensity`, `CarnahanStarlingPrimitive`, `cs_antideriv`, `packingDensity`, etc.).

# Summary of changes for run 88363ba6-4041-4336-a658-0d0fe849be91
Created `RequestProject/ExpandedCSReferenceTerm.lean` formalizing Equation (10) — the expanded Carnahan-Starling hard-sphere reference term for the residual Helmholtz free energy per NkBT.

**What was formalized:**

1. **`ExpandedCSReferenceTerm`** — Definition of the expanded form:
   `[(2π/3)ρmd³ − (π²/12)ρ²m²d⁶] / (1 − (π/6)ρmd³)²`
   with physical constraints (ρ > 0, m ≥ 1, d > 0, packing fraction < 1).

2. **`expandedCSReferenceTerm_eq_compact`** — The main identity proving Eq.(10) equals the compact Carnahan-Starling form `(4η − 3η²)/(1−η)²` when η = (π/6)ρmd³. Proved by `ring` after unfolding.

3. **`expandedCSReferenceTerm_eq_csHelmholtzExpandedDensity`** — Consistency theorem showing the constrained definition agrees with the unconstrained `csHelmholtzExpandedDensity` from Eq.(9) in `CSSubstitutePackingDensity.lean`.

4. **Bundled forms** in the `CarnahanStarlingPrimitive` namespace:
   - `expandedCSReferenceTerm` — evaluation at bundled primitive variables
   - `expandedCSReferenceTerm_eq_cs_antideriv` — connects back to `cs_antideriv(η)`

The file imports and reuses `CSSubstitutePackingDensity` (the `SubstitutePackingDensity` dependency), follows project naming conventions, uses no axioms beyond the standard ones (`propext`, `Classical.choice`, `Quot.sound`), and builds without sorries.

# Summary of changes for run f5901d5d-2b3f-4e06-a6bc-10c3a4c170df
Created `RequestProject/CSSubstitutePackingDensity.lean` formalizing Eq.(9) — the substitution of the packing density definition η = (π/6)ρmd³ (Eq.8) into the Carnahan–Starling reference term (4η − 3η²)/(1 − η)² (Eq.7).

**What was formalized:**

- `csHelmholtzExpandedDensity` — the CS reduced residual Helmholtz free energy expressed directly in terms of number density ρ, chain length m, and segment diameter d (Eq.9).
- `substitutePackingDensity` — the core substitution identity: `cs_antideriv (packingDensity ρ m d) = csHelmholtzExpandedDensity ρ m d`, proved by unfolding and `ring`.
- `csHelmholtzExpandedDensity_eq_CSReferenceTerm` — connects the expanded form back to the constrained `CSReferenceTerm` when η ∈ [0,1).
- `CarnahanStarlingPrimitive.substitutePackingDensity` — bundled form using the project's `CarnahanStarlingPrimitive` structure.

**Design decisions:**

- Reuses existing definitions: `cs_antideriv` from `SimplifyIntegrandEta.lean` (Eq.7) and `packingDensity` from `PackingDensity.lean` (Eq.8), following the DRY principle.
- The main theorem requires no physical hypotheses (ρ > 0, m ≥ 1, d > 0) since the identity is purely algebraic — this eliminates linter warnings while the bundled form carries the constraints via `CarnahanStarlingPrimitive`.
- All proofs compile without `sorry`, with only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

# Summary of changes for run dc0c622e-c338-48f4-981b-e63f8dcdc5f8
Created `RequestProject/PackingDensity.lean` formalizing the packing density equation η = (π/6) · ρ · m · d³.

The file imports `Mathlib` and `RequestProject.CarnahanStarlingPrimitive` (the `PrimitiveVariables` dependency) and contains:

1. **`packingDensity`** — noncomputable definition: `(Real.pi / 6) * ρ * m * d ^ 3`
2. **`packingDensity_nonneg`** — proof that η ≥ 0 when all inputs are non-negative
3. **`PackingDensityParams`** — structure bundling physical constraints (ρ > 0, m ≥ 1, d > 0, η < 1)
4. **`packingDensity_mem_Ico`** — proof that η ∈ [0, 1) for valid parameters
5. **`CarnahanStarlingPrimitive.eta_eq_packingDensity`** — bundled recovery theorem connecting the primitive variable `eta` to the `packingDensity` definition

All proofs compile without `sorry`, no custom axioms are introduced (only standard `propext`, `Classical.choice`, `Quot.sound`), and `lake build` succeeds cleanly.

# Summary of changes for run a4c17eeb-a111-4121-94ec-aa6fce7286c1
Created `RequestProject/SimplifyIntegrandEta.lean` formalizing Eq.(7) of the SAFT derivation — the Carnahan–Starling hard-sphere reference term for the reduced residual Helmholtz free energy:

$$\frac{A^{res}(ref)}{Nk_BT} = \frac{4\eta - 3\eta^2}{(1 - \eta)^2}$$

The file imports `RequestProject.ChangeVariableToEta` (the SimplifyIntegrandEta dependency providing Eq.(6)) and contains:

**Definition:**
- `CSReferenceTerm η hη` — the rational function (4η − 3η²)/(1 − η)² for η ∈ [0, 1)

**Properties:**
- `CSReferenceTerm_denom_pos` — denominator (1 − η)² > 0 for η ∈ [0, 1)
- `CSReferenceTerm_nonneg` — the reference term is non-negative
- `CSReferenceTerm_zero` — vanishes at η = 0 (ideal gas limit)

**Integral evaluation (core result):**
- `cs_antideriv` — total antiderivative F(t) = (4t − 3t²)/(1 − t)²
- `cs_reference_antideriv_deriv` — F'(t) = (4 − 2t)/(1 − t)³ via quotient rule
- `cs_integrand_continuousOn` — integrand continuity on [0, η]
- `cs_reference_integral_eq` — **Eq.(7)**: ∫₀ᶯ (4 − 2t)/(1 − t)³ dt = (4η − 3η²)/(1 − η)², proved via the Fundamental Theorem of Calculus

**Bundled forms** (using `CarnahanStarlingPrimitive`):
- `csReferenceTerm` — evaluated at the bundled packing fraction
- `csReferenceTerm_eq` — unfolds to the rational expression
- `csReferenceTerm_nonneg` — non-negativity
- `CSReferenceTerm_eq` — bundled integral identity

All proofs are complete (no `sorry`), the file builds cleanly with no warnings, and only standard axioms are used.

# Summary of changes for run 199218fe-9318-416b-b54f-071f12e76288
Created `RequestProject/ChangeVariableToEta.lean` formalizing Eq.(6) from the paper — the simplification of the Carnahan–Starling integrand by cancelling η from numerator and denominator.

The file imports `RequestProject.CSChangeVariableToEta` (the dependency for Eq.(5)) and provides four theorems, all fully proved (no sorries, no custom axioms):

1. **`CS_integrand_cancel_eta`** — Pointwise algebraic identity: for η ∈ (0,1),
   `(4η - 2η²) / ((1-η)³ · η) = (4 - 2η) / (1-η)³`.
   Proved via `field_simp` after establishing η ≠ 0 and (1-η)³ ≠ 0.

2. **`CS_ref_integral_simplified`** — Integral-level equality (Eq.(6)):
   `∫₀^η₀ (4t - 2t²)/((1-t)³·t) dt = ∫₀^η₀ (4 - 2t)/(1-t)³ dt`
   for η₀ ∈ (0,1). Proved by lifting the pointwise equality via `setIntegral_congr_fun`.

3. **`CarnahanStarlingPrimitive.CS_integrand_cancel_eta`** — Bundled pointwise form.

4. **`CarnahanStarlingPrimitive.CS_ref_integral_simplified`** — Bundled integral form using the primitive's packing fraction.

The file follows the project's naming conventions, reuses existing code (`CarnahanStarlingPrimitive` structure, `CS_integrand_eta`, etc.), and builds successfully with `lake build`.

# Summary of changes for run 8730e84a-e350-4b64-84f9-04ca3a200965
Created `RequestProject/CSChangeVariableToEta.lean` formalizing the change of integration variable from density ρ to packing fraction η (Eq. 5 from the derivation).

**What was formalized:**

The LaTeX equation:
$$\frac{A^{res}(ref)}{Nk_BT} = \int \frac{4\eta - 2\eta^2}{(1-\eta)^3 \cdot \eta}\, d\eta$$

which follows from combining:
- **R.1** (ProportionalityRelation): η ∝ ρ ⟹ dρ/ρ = dη/η
- **Eq.4** (SimplifyIntegrand): Z^CS - 1 = (4η - 2η²)/(1-η)³
- **Eq.3** (SubstituteZIntoIntegral): A^res/(NkBT) = ∫₀^ρ (Z^CS - 1)/ρ dρ

**Contents of the file:**

1. `CS_integrand_eta` — the integrand (4η - 2η²)/(η(1-η)³) as a noncomputable definition
2. `cs_integrand_eq` — pointwise lemma: (Z_CS η' - 1)/η' = CS_integrand_eta η'
3. `CS_changeVariable_to_eta` — the main integral identity theorem (Eq.5)
4. `CarnahanStarlingPrimitive.CS_changeVariable_to_eta` — bundled form using the project's structure

**Design decisions:**
- Imports `CSSimplifyIntegrand` and `ProportionalityIntegralChangeOfVar` as specified dependencies
- Reuses existing `Z_CS`, `CS_simplify_integrand`, and `CarnahanStarlingPrimitive` from the project (DRY)
- Follows PascalCase for theorems, snake_case for helper lemmas
- Provides both unbundled and bundled (namespace) forms consistent with the project pattern
- No axioms, no sorry — builds cleanly with `lake build`

# Summary of changes for run ef14455a-3f0f-4722-ad8b-8103e5d7cbf9
Created `RequestProject/ProportionalityIntegralChangeOfVar.lean` formalizing the proportionality relation R.1 from the SAFT derivation.

**Main results:**

- `proportionality_integral_change_of_var`: For C > 0, proves `∫ ρ in 0..a, g(C * ρ) / ρ = ∫ η in 0..(C * a), g(η) / η`. This justifies the change of integration variable from ρ to η when η = C · ρ (e.g., η = (π/6)ρmd³), going from Eq. (3) to Eq. (5).

- `CarnahanStarlingPrimitive.proportionality_integral_change_of_var`: Bundled form using the primitive variable structure.

The proof uses Mathlib's `intervalIntegral.integral_comp_mul_left` for the substitution, with an auxiliary lemma showing that `g(C·ρ)/ρ = (g(·)/·)(C·ρ) · C` pointwise (including at ρ = 0 via Lean's 0⁻¹ = 0 convention).

The file imports `CarnahanStarlingPrimitive` as specified, follows project naming conventions, uses no axioms beyond the standard ones (`propext`, `Classical.choice`, `Quot.sound`), and builds cleanly with no sorries or warnings.

# Summary of changes for run 3cc0055f-8757-487e-aad9-6ff713f938fa
Created `RequestProject/CSSimplifyIntegrand.lean` formalizing the LaTeX identity (Eq. 4):

$$\frac{1 + η + η² - η³}{(1 - η)³} - 1 = \frac{4η - 2η²}{(1 - η)³}$$

The file imports `SubstituteZIntoIntegral` (as required) and provides:

- **`CS_simplify_integrand`** — the core algebraic identity for any η ≠ 1, proved via `div_sub_one`, `congr 1`, and `ring`.
- **`Z_CS_sub_one`** — restated in terms of the existing `Z_CS` definition.
- **`CarnahanStarlingPrimitive.CS_simplify_integrand`** — bundled form using the primitive's packing fraction, deriving η ≠ 1 from the constraint η < 1.

The proof is fully verified with no `sorry`, no custom axioms — only the standard `propext`, `Classical.choice`, and `Quot.sound`.

# Summary of changes for run 2441748b-a9e4-4738-89b2-dc8f123f9683
Created `RequestProject/SubstituteZIntoIntegral.lean` formalizing Eq.(3) from the paper — the substitution of the Carnahan-Starling compressibility factor into the thermodynamic Helmholtz integral.

**What was formalized:**

The theorem `substituteZIntoIntegral` proves that applying `HelmholtzFromZ` (Eq.2, from `CSHelmholtzResidual.lean`) with the `Z_CS` compressibility factor (Eq.1) yields the explicit integrand:

```
∫₀^ρ [(1 + η + η² − η³)/(1 − η)³ − 1] / ρ dρ
```

**Reuse of existing code:**
- Imports and uses `HelmholtzFromZ` from `CSHelmholtzResidual.lean`
- Imports and relates to `CSCompressibilityFactor` from `CSCompressibilityFactor.lean`
- Uses `CarnahanStarlingPrimitive` bundle from `CarnahanStarlingPrimitive.lean`

**Definitions and results:**
- `Z_CS` — total (constraint-free) version of the CS compressibility factor, suitable for use inside integrals
- `Z_CS_eq_CSCompressibilityFactor` — proves agreement with the constrained `CSCompressibilityFactor` when η < 1
- `substituteZIntoIntegral` — the main theorem (Eq.3), proved by definitional unfolding
- `CarnahanStarlingPrimitive.substituteZIntoIntegral` — bundled form using the primitive structure

The proof compiles without `sorry`, axioms, or `@[implemented_by]`, using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

# Summary of changes for run 8c0dde3c-e31d-444c-8c79-f4b5a32d0b42
Created `RequestProject/CSHelmholtzResidual.lean` formalizing the thermodynamic identity:

$$\frac{A^{res}(ref)}{N k_B T} = \int_0^{\rho} \frac{Z(\rho') - 1}{\rho'}\, d\rho'$$

**Contents:**

- `HelmholtzFromZ (Z : ℝ → ℝ) (ρ : ℝ) : ℝ` — the reduced residual Helmholtz free energy defined as the interval integral of `(Z ρ' - 1) / ρ'` from `0` to `ρ`, using Mathlib's `intervalIntegral`.

- `CarnahanStarlingPrimitive.helmholtz_res_ref_eq` — a bundled theorem recovering `A_res_ref = ↑N * k_B * T * HelmholtzFromZ Z ρ` from the defining equation `A_res_ref / (N * k_B * T) = HelmholtzFromZ Z ρ`, using the `CarnahanStarlingPrimitive` structure for all physical variables and their invariants.

**Design decisions following project guidelines:**
1. **Semantic bundling**: The theorem uses the existing `CarnahanStarlingPrimitive` structure rather than raw `ℝ` variables, reusing its positivity invariants (`hk_B`, `N_pos`).
2. **DRY / Mathlib reuse**: Uses `div_eq_iff`, `mul_pos`, `Nat.cast_pos`, and `linarith` from Mathlib directly — no helper lemma re-implementation.
3. **No axioms beyond standard**: Only `propext`, `Classical.choice`, and `Quot.sound`.
4. **No sorries**: `lake build` succeeds cleanly.

# Summary of changes for run c7365b45-b389-4ffb-85f0-668ba1e41128
Created `RequestProject/CSCompressibilityFactor.lean` formalizing the Carnahan-Starling compressibility factor equation:

**Z^{CS}(η) = (1 + η + η² − η³) / (1 − η)³**

The file imports and reuses the existing `CarnahanStarlingPrimitive` bundle from the project. All proofs compile without `sorry`, no custom axioms are introduced, and only standard Lean axioms are used.

### Contents

- **`CSCompressibilityFactor`** — noncomputable definition of Z^{CS}(η) as a function of η with the constraint η < 1.
- **`CSCompressibilityFactor_denom_pos`** — (1 − η)³ > 0 when η < 1.
- **`CSCompressibilityFactor_denom_ne_zero`** — (1 − η)³ ≠ 0 when η < 1.
- **`CSCompressibilityFactor_num_pos`** — the numerator is positive for η ∈ [0, 1).
- **`CSCompressibilityFactor_pos`** — Z^{CS}(η) > 0 for η ∈ [0, 1).
- **`CSCompressibilityFactor_at_zero`** — Z^{CS}(0) = 1 (ideal gas limit).
- **`CarnahanStarlingPrimitive.csZ`** — bundled evaluation at the primitive's packing fraction.
- **`CarnahanStarlingPrimitive.csZ_pos`** — positivity of the bundled form.
- **`CarnahanStarlingPrimitive.csZ_eq`** — unfolds the bundled form to the rational expression.

The formalization follows project guidelines: semantic bundling via `CarnahanStarlingPrimitive`, Mathlib reuse (`div_pos`, `positivity`, `nlinarith`), PascalCase/snake_case naming conventions, and docstrings on all declarations.

# Summary of changes for run 5b2132a6-e807-4894-8412-669cde0985cd
Created `RequestProject/CarnahanStarlingPrimitive.lean` — a fully verified formalization of the primitive variable table for the Carnahan-Starling equation of state derivation.

**Structure: `CarnahanStarlingPrimitive`**

All nine primitive variables are bundled into a single structure with their physical constraints as invariants, following the project's semantic bundling guidelines:

| Field    | Type | Constraint          | Description            |
|----------|------|---------------------|------------------------|
| `Z`      | ℝ    | `0 < Z`             | Compressibility factor |
| `d`      | ℝ    | `0 < d`             | Segment diameter       |
| `N`      | ℕ    | `1 ≤ N`             | Number of particles    |
| `pi_val` | ℝ    | `pi_val = Real.pi`  | Mathematical constant π|
| `m`      | ℝ    | `1 ≤ m`             | Chain length           |
| `k_B`    | ℝ    | `0 < k_B`           | Boltzmann constant     |
| `T`      | ℝ    | `0 ≤ T`             | Temperature            |
| `eta`    | ℝ    | `0 ≤ eta ∧ eta < 1` | Packing density        |
| `rho`    | ℝ    | `0 ≤ rho`           | Number density         |

**Derived lemmas** in the `CarnahanStarlingPrimitive` namespace provide convenient accessors for downstream proofs: `Z_ne_zero`, `d_ne_zero`, `N_pos`, `k_B_ne_zero`, `Z_nonneg`, `d_nonneg`, `m_nonneg`, `m_pos`, `k_B_nonneg`, `one_sub_eta_pos`, `one_sub_eta_ne_zero`.

The file builds successfully with no `sorry`, no custom axioms, and only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). Mathlib is reused throughout (e.g., `ne_of_gt`, `le_of_lt`, `linarith`).