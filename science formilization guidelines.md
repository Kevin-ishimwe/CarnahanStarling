# Formalization Guidelines for Autoformalization Pipeline

These guidelines ensure generated code integrates seamlessly with the 5-phase pipeline.

### 1. Semantic Bundling (Coupling) ⭐

- **NEVER** accept raw `ℝ` variables for related quantities
- **ALWAYS** bundle them into a `structure` with invariants

**Bad:**

```lean
theorem science_something (A B C : ℝ)
```

**Good:**

```lean
structure SpecificScienceName where
  A : ℝ
  B : ℝ 
  C : ℝ 
  k_A : ℝ
  hC : 0 < C  
  hV : 0 < B

theorem science_something (p : SpecificScienceName) ...
```

### 2. Hierarchy & DRY (Don't Repeat Yourself)

- ✅ Reuse Mathlib theorems (e.g., `mul_pos`, `div_pos`, `pow_pos`)
- ❌ Don't re-implement lemmas provable in one line
- ❌ Don't duplicate helper lemmas
- ❌ Don't over-segment

**Bad:**

```lean
lemma my_mul_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos ha hb
```

**Good:** Use `mul_pos` directly from Mathlib.

### 3. Derivation Fidelity

- Mirror the paper's **step-by-step logic**, not just the final result where appropriate.
- If the paper does: "multiply by X, substitute Y, then simplify"
- Your proof should show these steps, or use intermediate lemmas

**Bad:**

```lean
theorem key_equation : X = Y := by nlinarith
```
**Good:**

```lean
theorem key_equation : X = Y := by
  rw [mul_comm, ← substitution_lemma]
  simp [definition_xy]
  ring
```

### 4. Module Organization

Place new code in the appropriate module:

- **Basics.lean**: Generic patterns used across domains
- **{NewDomain}.lean**: Create new modules for your domain

### 5. Naming Conventions

- **Theorems** for main results: `PascalCase`
- **Lemmas** for helpers: `snake_case`
- **Definitions** following user's style but **MUST describe**: `my_definition : Type := ...`
- **Proofs**: Use proof names that hint at the technique (`_by_algebra`, `_by_induction`)

## Phase 4 & 5: Verifier & Checkpoint

Your code will be checked for:

1. **Coupling**: Are structures bundled properly? (no raw ℝ)
2. **Hierarchy**: Is Mathlib reused liberally?
3. **Fidelity**: Does logic match the paper step-by-step?

If your code fails these checks, it enters **Checkpoint Phase** where a review agent refines it.

## Quick Checklist for Prover Output

- [ ] All parameter groups bundled in structures with invariants
- [ ] No raw variables; use bundled params
- [ ] Mathlib and library theorems reused (no re-implementation)
- [ ] Proof logic mirrors paper derivation
- [ ] Lemmas in correct module
- [ ] Naming follows conventions
- [ ] Code is idiomatic Lean 4 
