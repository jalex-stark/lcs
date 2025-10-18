-- This module serves as the root of the `RobustLCS` library.
-- Import modules here that should be built as part of the library.

-- Tactics and helper lemmas
import RobustLCS.Tactics.SimpTrace

-- Core mathematical definitions
import RobustLCS.Core.Density
import RobustLCS.Core.Isometry
import RobustLCS.Core.MatrixFacts
import RobustLCS.Core.StateDistance

-- Exact self-testing framework (Phase 1)
import RobustLCS.Exact.ExactSelfTest
import RobustLCS.Exact.PartialTrace
import RobustLCS.Exact.Support
