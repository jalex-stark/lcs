import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import RobustLCS.Core.Density
import RobustLCS.Tactics.SimpTrace

/-!
# Matrix Helper Lemmas

This file contains auxiliary lemmas about matrix operations (trace cyclicity, PSD properties)
used throughout the robust self-testing formalization.

## Main results

* `trace_mul_cycle3`: Three-factor trace cyclicity
* `seminorm_triangle_rho`: Triangle inequality for the ρ-weighted seminorm

## Implementation notes

These lemmas support the proofs in StateDistance.lean, particularly for establishing
that D_ρ(·∥·) satisfies the axioms of a semimetric.

-/

open Matrix Complex RobustLCS.Tactics

namespace RobustLCS.MatrixFacts

variable {n : Type} [Fintype n] [DecidableEq n]
abbrev M := RobustLCS.M n

/-- Cyclicity of trace for three-factor products.
**Proof strategy:** Direct application of Matrix.trace_mul_cycle from mathlib. -/
@[simp] theorem trace_mul_cycle3 (A B C : Matrix n n ℂ) :
    Matrix.trace (A * B * C) = Matrix.trace (C * A * B) := by
  -- PLAN: Immediate application of binary trace_mul_cycle twice (or Matrix.trace_mul_assoc).
  -- DEPENDS: Matrix.trace_mul_cycle (or Matrix.trace_mul_assoc from Mathlib)
  -- TACTIC SKETCH:
  --   rw [show A * B * C = A * (B * C) by ring]
  --   rw [Matrix.trace_mul_cycle A (B * C)]
  --   rw [show B * C * A = B * (C * A) by ring]
  --   rw [Matrix.trace_mul_cycle B (C * A)]
  sorry

/-- Triangle inequality for the seminorm `‖·‖_ρ` induced by ⟪·,·⟫_ρ.
**Proof strategy:** Define Q(T) := Re Tr(ρ T† T). For Δ₁ = X - Y and Δ₂ = Y - Z,
expand Q(Δ₁ + t Δ₂) as a quadratic in real t. Positivity for all t yields
discriminant bound (Cauchy-Schwarz), which implies the triangle inequality. -/
theorem seminorm_triangle_rho (ρd : Density n) (X Y Z : M) :
    Density.Drho ρd X Z ≤ Density.Drho ρd X Y + Density.Drho ρd Y Z := by
  -- PLAN: Recognize ⟪·,·⟫_ρ as a real bilinear form. For quadratic Q(Δ) = ⟪Δ,Δ⟫_ρ,
  --       the seminorm Drho satisfies Drho(X,Z) = sqrt(Q(X-Z)).
  --       For arbitrary Δ₁, Δ₂, the quadratic Q(Δ₁ + t Δ₂) ≥ 0 for all real t.
  --       Expanding yields: Q(Δ₁) + 2t ⟪Δ₁,Δ₂⟫_ρ + t² Q(Δ₂) ≥ 0.
  --       Discriminant ≥ 0 gives 4⟪Δ₁,Δ₂⟫_ρ² ≤ 4 Q(Δ₁) Q(Δ₂), i.e., Cauchy-Schwarz.
  --       Triangle then follows by setting Δ₁ = X-Y, Δ₂ = Y-Z.
  -- DEPENDS: Density.rhoInner definition, ρd.psd_op (PSD property),
  --          Density.Drho definition, Real.sqrt properties, arithmetic inequalities
  -- TACTIC SKETCH:
  --   unfold Density.Drho Density.rhoInner
  --   [construct quadratic Q and discriminant bound]
  --   [apply to Δ₁ = X-Y, Δ₂ = Y-Z]
  --   simp only [Real.sqrt_add_sq] or similar to conclude
  sorry

end RobustLCS.MatrixFacts
