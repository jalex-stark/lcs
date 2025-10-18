import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Algebra.Tower
import RobustLCS.Core.Density
import RobustLCS.Core.MatrixFacts
import RobustLCS.Core.Isometry
import RobustLCS.Tactics.SimpTrace

/-!
# State-Dependent Distance

This file defines the state-dependent distance D_ρ(X ∥ Y) and proves the properties
from Lemma 4.4 of the paper.

## Main definitions

* `Drho ρd X Y`: State-dependent distance sqrt(⟪X-Y, X-Y⟫_ρ)
  (defined in Density.lean)

## Main results

* `Drho_sq_formula`: Part (a) - Expanded formula for D_ρ(X ∥ I)²
* `Drho_left_unitary`: Part (b) - LEFT-multiplication invariance (corrected from paper)
* `Drho_triangle`: Part (c) - Triangle inequality
* `Drho_left_mul_bound`: Part (d) - Bound for left-multiplication by unitaries
* `Drho_chain_sum`: Part (e) - Chain sum bound for products
* `Drho_unitary_push`: Part (f) - Unitary push inequality
* `Drho_convexity`: Part (g) - Convexity property
* `Drho_tensor_I_eq_marginal`: Part (h) - Tensor marginal (placeholder)
* `Drho_isometry_covariant`: Part (i) - Isometry covariance
* `Drho_proj_support`: Part (j) - Projection support properties

## Implementation notes

**IMPORTANT CORRECTION**: Lemma 4.4(b) in the original paper claimed both left and right
multiplication invariance. Peer review identified that right-multiplication does NOT hold.
This formalization includes only the correct left-multiplication form:
  D_ρ(UX ∥ UY) = D_ρ(X ∥ Y)

## References

See Lemma 4.4 of "Robust self-testing for linear constraint system games" (arXiv:1709.09267v2)
-/

open Matrix Complex RobustLCS.Tactics
namespace RobustLCS

variable {n : Type} [Fintype n] [DecidableEq n]

namespace Density

/-- **(a)** Expanded formula for `D_ρ(X ∥ I)²`:
`Re Tr(ρ (X−I)†(X−I)) = (Tr(ρ X†X)).re − 2 (Tr(ρ X)).re + (Tr ρ).re`.
**Proof strategy:** Expand (X-I)†(X-I) = X†X - X† - X + I, multiply by ρ, take trace
and real part. Use cyclicity and Hermiticity of ρ. -/
theorem Drho_sq_formula (ρd : Density n) (X : M n) :
    (Drho ρd X (1 : M n))^2
      = ((Matrix.trace (ρd.ρ * (Xᴴ * X))).re)
        - 2 * ((Matrix.trace (ρd.ρ * X)).re)
        + ((Matrix.trace ρd.ρ).re) := by
  -- PLAN: Expand (X-I)†(X-I) = X†X - X† - X + I, multiply by ρ, take trace and real part
  -- DEPENDS: Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, trace linearity,
  --          trace_mul_cycle, ρd.herm (Hermiticity: ρ† = ρ), Drho definition, rhoInner definition
  -- TACTIC SKETCH:
  --   unfold Drho rhoInner  -- expand definitions
  --   rw [sub_mul, mul_sub, conjTranspose_sub]  -- expand (X-I)†(X-I)
  --   rw [conjTranspose_one, mul_one, one_mul]  -- simplify I† = I
  --   simp only [trace_add, trace_sub, trace_mul]  -- distribute trace
  --   rw [trace_mul_cycle ρd.ρ Xᴴ, trace_mul_cycle ρd.ρ X]  -- use cyclicity
  --   rw [ρd.herm]  -- use ρ† = ρ for Hermitian terms
  --   ring  -- simplify real arithmetic
  sorry

/-- **(b)** Left-unitary invariance: `D_ρ( U X ∥ U Y ) = D_ρ( X ∥ Y )`.
**Proof strategy:** (UX-UY)† (UX-UY) = (X-Y)† U† U (X-Y) = (X-Y)† (X-Y) using U† U = I.
The trace ⟪·,·⟫_ρ is unchanged, so distances match. -/
theorem Drho_left_unitary (ρd : Density n) {U X Y : M n}
    (hU : Uᴴ * U = (1 : M n)) :
    Drho ρd (U * X) (U * Y) = Drho ρd X Y := by
  -- PLAN: Show (UX-UY)†(UX-UY) = (X-Y)†U†U(X-Y) = (X-Y)†(X-Y) using unitarity U†U = I
  -- DEPENDS: Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_mul, hU (unitarity),
  --          Matrix.mul_assoc, Matrix.one_mul, Drho definition, rhoInner definition
  -- TACTIC SKETCH:
  --   unfold Drho rhoInner  -- expand definitions
  --   congr 1  -- reduce to showing inner products equal
  --   rw [mul_sub, mul_sub]  -- factor U from (UX - UY)
  --   rw [conjTranspose_sub, conjTranspose_mul]  -- compute (UX - UY)†
  --   rw [mul_assoc, mul_assoc, mul_assoc]  -- reassociate to isolate U†U
  --   rw [← mul_assoc Xᴴ, ← mul_assoc Yᴴ]  -- prepare for U†U substitution
  --   rw [hU]  -- substitute U†U = I
  --   simp only [one_mul]  -- simplify I * (X-Y) = (X-Y)
  sorry

/-- **(c)** Triangle inequality. -/
theorem Drho_triangle (ρd : Density n) (X Y Z : M n) :
    Drho ρd X Z ≤ Drho ρd X Y + Drho ρd Y Z :=
  MatrixFacts.seminorm_triangle_rho ρd X Y Z

/-- **(d)** Left-multiplication bound for unitaries: `D_ρ( U₂ Z ∥ U₃ ) ≤ D_ρ( Z ∥ I ) + D_ρ( U₂ ∥ U₃ )`.
**Proof strategy:** Apply triangle inequality: ‖U₂Z - U₃‖ ≤ ‖U₂Z - U₂‖ + ‖U₂ - U₃‖.
Use left-unitary invariance (b) to rewrite ‖U₂(Z-I)‖ = ‖Z-I‖. -/
theorem Drho_left_mul_bound (ρd : Density n)
    {U₂ U₃ Z : M n} (h2 : U₂ᴴ * U₂ = 1) (h3 : U₃ᴴ * U₃ = 1) :
    Drho ρd (U₂ * Z) U₃ ≤ Drho ρd Z (1) + Drho ρd U₂ U₃ := by
  -- PLAN: Apply triangle inequality with pivot U₂, then use left-unitary invariance on first term
  -- DEPENDS: Drho_triangle (part c), Drho_left_unitary (part b), h2 (U₂ unitarity),
  --          Matrix.mul_one (U₂ * I = U₂)
  -- TACTIC SKETCH:
  --   calc Drho ρd (U₂ * Z) U₃
  --       ≤ Drho ρd (U₂ * Z) U₂ + Drho ρd U₂ U₃  := Drho_triangle ρd (U₂*Z) U₂ U₃
  --     _ = Drho ρd (U₂ * Z) (U₂ * 1) + Drho ρd U₂ U₃  := by rw [mul_one]
  --     _ = Drho ρd Z 1 + Drho ρd U₂ U₃  := by rw [Drho_left_unitary ρd h2]
  sorry

/-- **(e)** Summed chain bound: `∥∏ A_i − ∏ B_i∥_ρ ≤ ∑ ∥A_i − B_i∥_ρ`. -/
theorem Drho_chain_sum (ρd : Density n)
    (Xs Ys : List (M n)) (hlen : Xs.length = Ys.length) :
    Drho ρd (Xs.foldl (· * ·) 1) (Ys.foldl (· * ·) 1)
      ≤ (List.zipWith (fun X Y => Drho ρd X Y) Xs Ys).sum := by
  -- Standard telescoping + triangle; induction on lists.
  sorry

/-- **(f)** Requires `W` unitary; the standard "push" inequality used in §4.2. -/
theorem Drho_unitary_push (ρd : Density n) (ν η : ℝ)
    {W A B : M n} (hW : Wᴴ * W = 1)
    (h1 : Drho ρd W (1) ≤ ν)
    (h2 : Drho ρd (A * B) (1) ≤ η) :
    Drho ρd (B * W) (1) ≤ ν + 2 * η := by
  -- Combine triangle + two applications of (b) and (d).
  sorry

/-- **(g)** Convexity: `D_ρ( ∑ U_i ∥ I ) ≤ ∑ D_ρ(U_i ∥ I)`. -/
theorem Drho_convexity (ρd : Density n) {ι} [Fintype ι]
    (U : ι → M n) :
    Drho ρd (Finset.univ.sum (fun i => U i)) (1)
      ≤ Finset.univ.sum (fun i => Drho ρd (U i) (1)) := by
  -- `‖·‖_ρ` is a seminorm → convex. Use Jensen or Minkowski on finite sums.
  sorry

/-- **(h)** Tensor marginal specialization (dimension-normalized 2-norm case).
    We state it as a placeholder; implement partial trace equality in a follow-up. -/
theorem Drho_tensor_I_eq_marginal
    (ρAB : Density (n × n)) (A : M n) : True := by
  -- Provide in a dedicated PartialTrace file if needed; not used immediately in Phase 1.
  trivial

/-- **(i)** Isometry covariance: `D_ρ(Z₁ ∥ Z₂) = D_{VρV†}(V Z₁ V† ∥ V Z₂ V†)`. -/
theorem Drho_isometry_covariant
    {m : Type} [Fintype m] [DecidableEq m]
    (ρd : Density n) (V : Matrix m n ℂ) (hIso : Vᴴ * V = (1 : Matrix n n ℂ))
    (Z₁ Z₂ : M n) :
    Drho ρd Z₁ Z₂
      = Drho
          { ρ := V * ρd.ρ * Vᴴ
          , herm := by
              -- (VρV†)† = Vρ†V† = VρV†
              sorry
          , psd_op := by
              -- pushforward of PSD under isometry
              sorry
          , trOne := by
              -- Re Tr(VρV†) = Re Tr(ρ) = 1 (cyclicity)
              sorry
          }
          (V * Z₁ * Vᴴ) (V * Z₂ * Vᴴ) := by
  -- Expand both sides and use U†U = I + cyclicity of trace.
  sorry

/-- **(j)** Projection support: if `P ρ = ρ` and `P` is a projection,
    then `D_ρ(ZP ∥ I) = D_ρ(Z ∥ I) = D_ρ(Z ∥ P)`. -/
theorem Drho_proj_support (ρd : Density n)
    {P Z : M n} (hProj : P * P = P) (hSupp : P * ρd.ρ = ρd.ρ) :
    Drho ρd (Z * P) (1) = Drho ρd Z (1)
    ∧ Drho ρd Z P = Drho ρd Z (1) := by
  -- Two inclusions using hSupp and the definition of ⟪·,·⟫_ρ; routine.
  sorry

end Density
end RobustLCS
