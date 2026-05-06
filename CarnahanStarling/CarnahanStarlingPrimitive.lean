import Mathlib

/-!
# Carnahan-Starling Primitive Variables

Primitive variable table for the Carnahan-Starling equation of state derivation.

## Variables

| Symbol | Type | Constraint       | Description            |
|--------|------|------------------|------------------------|
| Z      | ℝ    | Z > 0            | Compressibility factor |
| d      | ℝ    | d > 0            | Segment diameter       |
| N      | ℕ    | N ≥ 1            | Number of particles    |
| pi_val | ℝ    | pi_val = Real.pi | Mathematical constant  |
| m      | ℝ    | m ≥ 1            | Chain length           |
| k_B    | ℝ    | k_B > 0          | Boltzmann constant     |
| T      | ℝ    | T ≥ 0            | Temperature            |
| eta    | ℝ    | 0 ≤ η < 1       | Packing density        |
| rho    | ℝ    | ρ ≥ 0            | Number density         |

## Section

Variable Table — Meta: primitive
-/

/-- Bundled primitive variables for the Carnahan-Starling equation of state derivation.

Each field carries its physical constraint as an invariant, ensuring well-formedness
of any term of this type. -/
structure CarnahanStarlingPrimitive where
  /-- Compressibility factor -/
  Z : ℝ
  /-- Segment diameter -/
  d : ℝ
  /-- Number of particles -/
  N : ℕ
  /-- Mathematical constant π -/
  pi_val : ℝ
  /-- Chain length -/
  m : ℝ
  /-- Boltzmann constant -/
  k_B : ℝ
  /-- Temperature -/
  T : ℝ
  /-- Packing density -/
  eta : ℝ
  /-- Number density -/
  rho : ℝ
  /-- Z is strictly positive -/
  hZ : 0 < Z
  /-- d is strictly positive -/
  hd : 0 < d
  /-- At least one particle -/
  hN : 1 ≤ N
  /-- pi_val is the mathematical constant π -/
  hpi : pi_val = Real.pi
  /-- Chain length is at least 1 -/
  hm : 1 ≤ m
  /-- Boltzmann constant is strictly positive -/
  hk_B : 0 < k_B
  /-- Temperature is non-negative -/
  hT : 0 ≤ T
  /-- Packing density is in [0, 1) -/
  heta_nonneg : 0 ≤ eta
  heta_lt_one : eta < 1
  /-- Number density is non-negative -/
  hrho : 0 ≤ rho

namespace CarnahanStarlingPrimitive

variable (p : CarnahanStarlingPrimitive)

/-- Number of particles is positive. -/
theorem N_pos : 0 < p.N := Nat.one_le_iff_ne_zero.mp p.hN |> Nat.pos_of_ne_zero

/-- Chain length is strictly positive (since m ≥ 1). -/
theorem m_pos : 0 < p.m := lt_of_lt_of_le one_pos p.hm

end CarnahanStarlingPrimitive
