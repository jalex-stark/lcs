import Mathlib.LinearAlgebra.Matrix.Trace
import RobustLCS.Core.Density
import RobustLCS.Core.MatrixFacts
import RobustLCS.Tactics.SimpTrace

/-!
# Isometries

This file defines isometric matrices V : m×n satisfying V†V = I.

## Main definitions

* `Isometry V`: Predicate asserting V†V = I (isometric embedding from ℂⁿ → ℂᵐ)
* `isometry_mul_left`: Simp lemma for the definition

## Implementation notes

Isometries appear in Lemma 4.4(i) for the isometry covariance property of D_ρ.
The condition V†V = I means V preserves inner products when mapping from the smaller
space to the larger space.

-/

open Matrix Complex RobustLCS.Tactics

namespace RobustLCS.Isometry

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A matrix `V : m×n` is an isometry (`Vᴴ V = I`). -/
def Isometry (V : Matrix m n ℂ) : Prop := Vᴴ * V = (1 : Matrix n n ℂ)

@[simp] lemma isometry_mul_left {V : Matrix m n ℂ} :
    Isometry V ↔ Vᴴ * V = 1 := Iff.rfl

end RobustLCS.Isometry
