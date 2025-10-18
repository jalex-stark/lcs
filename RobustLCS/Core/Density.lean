import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt

open Matrix Complex

namespace RobustLCS

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Square matrices over `ℂ` on `n`. -/
abbrev M (n : Type) [Fintype n] [DecidableEq n] := Matrix n n ℂ

/-- A *density matrix* on `ℂ^n`. We encode:
  * Hermitian: ρᴴ = ρ
  * Operator positivity: ∀ X, Re Tr(ρ X† X) ≥ 0
  * trace(ρ).re = 1
This "operator-positivity" is the finite-dimensional form we use for Minkowski/CS. -/
structure Density (n : Type) [Fintype n] [DecidableEq n] where
  ρ      : M n
  herm   : ρᴴ = ρ
  psd_op : ∀ X : M n, 0 ≤ (Matrix.trace (ρ * Xᴴ * X)).re
  trOne  : (Matrix.trace ρ).re = 1

namespace Density

/-- Real bilinear form ⟪X,Y⟫_ρ := Re Tr(ρ X† Y). -/
def rhoInner (ρd : Density n) (X Y : M n) : ℝ :=
  (Matrix.trace (ρd.ρ * Xᴴ * Y)).re

/-- State-dependent distance `D_ρ(X ∥ Y) := sqrt ⟪X-Y, X-Y⟫_ρ`. -/
noncomputable def Drho (ρd : Density n) (X Y : M n) : ℝ :=
  Real.sqrt (ρd.rhoInner (X - Y) (X - Y))

notation:max "⟪" X "," Y "⟫_(" ρd ")" => Density.rhoInner ρd X Y
notation:max "Dρ[" ρd "](" X "∥" Y ")" => Density.Drho ρd X Y

end Density
end RobustLCS
