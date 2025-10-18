import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Module
import RobustLCS.Tactics.SimpTrace

/-!
# Partial Trace Operations

This file defines partial trace operations over subsystems of a composite quantum system.
Given a bipartite state on `nA × nB`, we can trace out either subsystem (A or B) to obtain
a marginal state on the other subsystem.

## Main definitions

* `ptrB`: Partial trace over subsystem B, yielding marginal state on A
* `ptrA`: Partial trace over subsystem A, yielding marginal state on B

## Main results

* `trace_kron_left`: Pushforward of trace through left Kronecker factor
  - `Tr((A ⊗ I) X) = Tr(A · Tr_B X)`
* `trace_kron_right`: Pushforward of trace through right Kronecker factor
  - `Tr(X (A ⊗ I)) = Tr((Tr_B X) · A)`

## Implementation notes

The partial trace is defined blockwise at the index level:
- `ptrB X` extracts diagonal blocks along the B index
- `ptrA X` extracts diagonal blocks along the A index

This avoids functional analysis machinery and stays within finite-dimensional matrix algebra.

## References

Used in the mixed-state support machinery (see Support.lean) and general robust self-testing
analysis of subsystem supports.
-/

open Matrix Complex RobustLCS.Tactics

namespace RobustLCS.Exact.PartialTrace

variable {nA nB : Type} [Fintype nA] [DecidableEq nA]
                         [Fintype nB] [DecidableEq nB]

abbrev MA  := Matrix nA nA ℂ
abbrev MB  := Matrix nB nB ℂ
abbrev MAB := Matrix (nA × nB) (nA × nB) ℂ

/-- Partial trace over `B`:
`(Tr_B X) a a' = ∑ b, X (a,b),(a',b)`.

This extracts the marginal state on system A by summing over all states of system B.
-/
def ptrB (X : MAB) : MA :=
  fun a a' => ∑ b, X (a, b) (a', b)

/-- Partial trace over `A`:
`(Tr_A X) b b' = ∑ a, X (a,b),(a,b')`.

This extracts the marginal state on system B by summing over all states of system A.
-/
def ptrA (X : MAB) : MB :=
  fun b b' => ∑ a, X (a, b) (a, b')

@[simp] lemma ptrB_apply (X : MAB) (a a' : nA) :
    ptrB (nA:=nA) (nB:=nB) X a a' = ∑ b, X (a, b) (a', b) := rfl

@[simp] lemma ptrA_apply (X : MAB) (b b' : nB) :
    ptrA (nA:=nA) (nB:=nB) X b b' = ∑ a, X (a, b) (a, b') := rfl

/-- Trace pushforward for left Kronecker factor: `Tr( (A ⊗ I) X ) = Tr( A · Tr_B X )`.

This identity shows that tracing a product of `(A ⊗ I)` with `X` reduces to applying
the trace identity to the partial trace of X over B.
-/
theorem trace_kron_left (A : MA) (X : MAB) :
    Matrix.trace ((Matrix.kronecker A (1 : MB)) ⬝ X)
      = Matrix.trace (A ⬝ ptrB (nA:=nA) (nB:=nB) X) := by
  classical
  -- Expand trace on AB and collapse the `B` sum using (I) on B
  simp [Matrix.trace, Matrix.diag, ptrB, mul_apply, Matrix.kronecker, Finset.mul_sum,
        Finset.sum_mul, Finset.sum_sigma', Finset.unorderedListSum, mul_comm, mul_left_comm,
        mul_assoc]

/-- Trace pushforward for right Kronecker factor: `Tr( X (A ⊗ I) ) = Tr( (Tr_B X) · A )`.

This is the right-multiplication variant of trace_kron_left, obtained via cyclicity
and the left-multiplication identity.
-/
theorem trace_kron_right (A : MA) (X : MAB) :
    Matrix.trace (X ⬝ (Matrix.kronecker A (1 : MB)))
      = Matrix.trace ((ptrB (nA:=nA) (nB:=nB) X) ⬝ A) := by
  -- Use cyclicity of trace and the left identity
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    congrArg Complex.re
      (by
        -- Exact complex equality; derive from `trace_kron_left` using cyclicity
        have := trace_kron_left (nA:=nA) (nB:=nB) A X
        -- Switch sides with trace_mul_cycle3
        simpa [Matrix.trace_mul_cycle, mul_assoc, mul_comm, mul_left_comm] using this)

end RobustLCS.Exact.PartialTrace
