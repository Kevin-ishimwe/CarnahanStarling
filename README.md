# Carnahan–Starling Hard Sphere Reference Term Formalization

This project is an AI-generated Lean formalization of the Carnahan–Starling hard sphere reference term, a key component of the Statistical Associating Fluid Theory (SAFT) equation of state.

## Overview

This project formalizes the derivation of the reduced residual Helmholtz free energy for hard sphere fluids using the Carnahan–Starling equation of state. The formalization is fully mechanically verified in [Lean 4](https://lean-lang.org/) with no `sorry` statements or unproven axioms.

### What is SAFT?

The Statistical Associating Fluid Theory (SAFT) is an equation of state that describes thermodynamic properties of fluids by decomposing them into:

- **Reference term**: Hard sphere interactions (this project)
- **Perturbation terms**: Attractive interactions, molecular association, etc.

This formalization focuses on the hard sphere reference term, which is the mathematical foundation upon which more complex SAFT models are built.

### The Carnahan–Starling Equation

For a hard sphere fluid, the reduced residual Helmholtz free energy per molecule is:

$$\frac{A^{\text{res}}}{Nk_BT} = \frac{4\eta - 3\eta^2}{(1-\eta)^2}$$

where $\eta = \frac{\pi}{6}\rho m d^3$ is the packing fraction, with:

- $\rho$ = number density
- $m$ = chain length (number of segments)
- $d$ = segment diameter

## Project Structure

The formalization is organized as a sequence of interdependent modules in `CarnahanStarling/`, each proving a specific step in the mathematical derivation:

### Core Modules

- **`CarnahanStarlingPrimitive.lean`** – Primitive variables and basic structure definitions
- **`CSCompressibilityFactor.lean`** – Compressibility factor formula (Eq. 1)
- **`CSHelmholtzResidual.lean`** – Residual Helmholtz free energy (Eq. 2-3)
- **`CSSimplifyIntegrand.lean`** – Integral simplification (Eq. 4-6)
- **`SimplifyIntegrandEta.lean`** – Carnahan–Starling reference term in packing fraction form (Eq. 7)
- **`PackingDensity.lean`** – Packing density definition (Eq. 8)
- **`CSSubstitutePackingDensity.lean`** – Substitution of packing density into reference term (Eq. 9)
- **`ExpandedCSReferenceTerm.lean`** – Fully expanded form in density variables (Eq. 10)

### Additional Modules

- **`ChangeVariableToEta.lean`**, **`CSChangeVariableToEta.lean`** – Change of variables transformations
- **`ProportionalityIntegralChangeOfVar.lean`** – Proportionality theorems
- **`SubstituteZIntoIntegral.lean`** – Integral substitutions

## Building the Project

### Prerequisites

- Lean 4
- Lake (Lean's package manager)

### Build Instructions

```bash
# Build the project
lake build

# Generate documentation (blueprint)
leanblueprint web
```

## Documentation

The formalization includes a detailed blueprint with:

- Mathematical derivation steps
- Lean code implementations
- Dependency graphs showing how equations relate to each other

View the generated documentation in `blueprint/web/index.html` after running `leanblueprint web`.

## Key Features

✓ **Fully mechanically verified** – All proofs compile in Lean 4  
✓ **No unproven claims** – No `sorry` statements  
✓ **Minimal axioms** – Uses only standard Lean/Mathlib axioms  
✓ **Well-structured** – Modules follow the mathematical derivation order  
✓ **Documented** – Each step includes proofs and intermediate theorems

## Scientific Reference

The formalization formalizes the derivation from:

- **SAFT Reference Term Derivation V1** – See `SAFT Reference Term Derivation_V1.tex`

## Related Files

- `ARISTOTLE_SUMMARY.md` – Detailed summaries of recent improvements and refactoring
- `science formilization guidelines.md` – Guidelines for scientific formalization
- `blueprint/src/content.tex` – LaTeX blueprint source
