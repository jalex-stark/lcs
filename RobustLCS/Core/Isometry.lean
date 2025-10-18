import Mathlib.LinearAlgebra.Matrix.Trace
import RobustLCS.Core.Density
import RobustLCS.Core.MatrixFacts
import RobustLCS.Tactics.SimpTrace

open Matrix Complex RobustLCS.Tactics

namespace RobustLCS.Isometry

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A matrix `V : m×n` is an isometry (`Vᴴ V = I`). -/
def Isometry (V : Matrix m n ℂ) : Prop := Vᴴ * V = (1 : Matrix n n ℂ)

@[simp] lemma isometry_mul_left {V : Matrix m n ℂ} :
    Isometry V ↔ Vᴴ * V = 1 := Iff.rfl

end RobustLCS.Isometry
