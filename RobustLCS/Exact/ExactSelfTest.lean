import RobustLCS.Core.StateDistance
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix Complex

namespace RobustLCS.Exact

-- Minimal surface to house the exact result; we'll fill after
-- porting the small character lemmas and support projections.

structure ObsStrategy
    (nA nB : Type) [Fintype nA] [DecidableEq nA]
                   [Fintype nB] [DecidableEq nB]  where
  ρAB   : Matrix (nA × nB) (nA × nB) ℂ
  -- Observables placeholders; for Magic Square we'll make these explicit.

/-- Lemma 4.3 (support projections) — to be proved next. -/
theorem lemma43_support : True := by
  sorry

/-- Lemma 4.2 (irrep selection) — after porting basic character facts. -/
theorem lemma42_irrep_selection : True := by
  sorry

/-- Theorem 4.1 (exact self-test). -/
theorem theorem41_exact : True := by
  sorry

end RobustLCS.Exact
