import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
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
  sorry

/-- Triangle inequality for the seminorm `‖·‖_ρ` induced by ⟪·,·⟫_ρ.
**Proof strategy:** Define Q(T) := Re Tr(ρ T† T). For Δ₁ = X - Y and Δ₂ = Y - Z,
expand Q(Δ₁ + t Δ₂) as a quadratic in real t. Positivity for all t yields
discriminant bound (Cauchy-Schwarz), which implies the triangle inequality. -/
theorem seminorm_triangle_rho (ρd : Density n) (X Y Z : M) :
    Density.Drho ρd X Z ≤ Density.Drho ρd X Y + Density.Drho ρd Y Z := by
  sorry

end RobustLCS.MatrixFacts
