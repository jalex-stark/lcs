import Mathlib.Algebra.Algebra.Tower
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import RobustLCS.Core.Density
import RobustLCS.Core.Isometry
import RobustLCS.Core.MatrixFacts
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

/-- **(c)** Triangle inequality.
**Proof strategy:** D_ρ is a seminorm induced by the bilinear form ⟪·,·⟫_ρ.
Triangle inequality follows from Cauchy-Schwarz applied to Re Tr(ρ (X-Z)† (X-Z))
with the quadratic form in Δ₁ = X-Y and Δ₂ = Y-Z. -/
theorem Drho_triangle (ρd : Density n) (X Y Z : M n) :
    Drho ρd X Z ≤ Drho ρd X Y + Drho ρd Y Z := by
  -- PLAN: Recognize D_ρ as a seminorm from inner product ⟪·,·⟫_ρ.
  --       Apply Cauchy-Schwarz to the quadratic form Q(t) = ⟪Δ₁ + t Δ₂, Δ₁ + t Δ₂⟫_ρ
  --       where Δ₁ = X - Y, Δ₂ = Y - Z. For all real t, Q(t) ≥ 0 (PSD property).
  --       The discriminant condition gives the Cauchy-Schwarz bound.
  -- DEPENDS: Density.rhoInner definition, PSD property of ρd (psd_op),
  --          Drho definition, seminorm_triangle_rho (helper in MatrixFacts)
  -- TACTIC SKETCH:
  --   exact MatrixFacts.seminorm_triangle_rho ρd X Y Z
  exact MatrixFacts.seminorm_triangle_rho ρd X Y Z

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

/-- **(e)** Summed chain bound: `∥∏ A_i − ∏ B_i∥_ρ ≤ ∑ ∥A_i − B_i∥_ρ`.
**Proof strategy:** Telescoping product: ∏Aᵢ - ∏Bᵢ = ∑ᵢ (∏ⱼ<ᵢ Aⱼ)(Aᵢ - Bᵢ)(∏ⱼ>ᵢ Bⱼ).
Each term is bounded by ‖Aᵢ - Bᵢ‖ρ via unitarity of left/right product factors. -/
theorem Drho_chain_sum (ρd : Density n)
    (Xs Ys : List (M n)) (hlen : Xs.length = Ys.length) :
    Drho ρd (Xs.foldl (· * ·) 1) (Ys.foldl (· * ·) 1)
      ≤ (List.zipWith (fun X Y => Drho ρd X Y) Xs Ys).sum := by
  -- PLAN: Use telescoping: ∏Aᵢ - ∏Bᵢ = Σᵢ (∏ⱼ<ᵢ Aⱼ)(Aᵢ - Bᵢ)(∏ⱼ>ᵢ Bⱼ)
  --       Each term contributes D_ρ(Aᵢ - Bᵢ) after bounding with unitarity.
  --       Induction on list length with hlen constraint.
  -- DEPENDS: Drho_triangle (part c), Drho_left_unitary (part b), List.foldl, List.zipWith
  -- TACTIC SKETCH:
  --   induction Xs, Ys using List.rec₂ with hlen constraint
  --   base case: empty lists → 0 ≤ 0
  --   inductive case: fold telescoping on head + induction hypothesis on tail
  --   apply triangle inequality for each segment
  sorry

/-- **(f)** Unitary push inequality used in §4.2 analysis.
**Proof strategy:** BW - I = (B-I)W + (W-I). Apply triangle inequality and use (b), (d)
to bound the left-multiplication term. -/
theorem Drho_unitary_push (ρd : Density n) (ν η : ℝ)
    {W A B : M n} (hW : Wᴴ * W = 1)
    (h1 : Drho ρd W (1) ≤ ν)
    (h2 : Drho ρd (A * B) (1) ≤ η) :
    Drho ρd (B * W) (1) ≤ ν + 2 * η := by
  -- PLAN: Rewrite B*W - I as (B-I)*W + W - I. Apply triangle inequality.
  --       The (B-I)*W term is bounded using left-unitary invariance (b) + chain sum (e).
  --       Combine with bound on W - I from h1.
  -- DEPENDS: Drho_triangle (c), Drho_left_unitary (b), Drho_chain_sum (e),
  --          h1 (bound on W), h2 (bound on A*B)
  -- TACTIC SKETCH:
  --   calc Drho ρd (B * W) 1
  --       ≤ Drho ρd (B * W) (A * B) + Drho ρd (A * B) 1  := Drho_triangle
  --     _ ≤ ... + η  := by rw [h2]
  --     _ ≤ ν + 2 * η  := by [use chain sum bounds with unitary W]
  sorry

/-- **(g)** Convexity: `D_ρ( ∑ U_i ∥ I ) ≤ ∑ D_ρ(U_i ∥ I)`.
**Proof strategy:** D_ρ is a seminorm; the inequality is Minkowski for finite sums.
∑ Uᵢ - I = ∑ (Uᵢ - I), so apply seminorm subadditivity. -/
theorem Drho_convexity (ρd : Density n) {ι} [Fintype ι]
    (U : ι → M n) :
    Drho ρd (Finset.univ.sum (fun i => U i)) (1)
      ≤ Finset.univ.sum (fun i => Drho ρd (U i) (1)) := by
  -- PLAN: D_ρ(·∥·) is a seminorm induced by ⟪·,·⟫_ρ (inner product).
  --       Minkowski inequality for seminorms: D_ρ(∑ Aᵢ) ≤ ∑ D_ρ(Aᵢ).
  --       Rewrite ∑ Uᵢ - I = ∑ (Uᵢ - I) and apply to difference vectors.
  -- DEPENDS: Drho definition, rhoInner definition, seminorm properties (from MatrixFacts),
  --          Finset.sum properties, PSD property of ⟪·,·⟫_ρ
  -- TACTIC SKETCH:
  --   unfold Drho rhoInner
  --   simp only [sub_sum, ← Finset.sum_congr]
  --   apply Finset.sum_le_sum
  --   intro i hi
  --   [use seminorm Minkowski inequality]
  sorry

/-- **(h)** Tensor marginal specialization (dimension-normalized 2-norm case).
    We state it as a placeholder; implement partial trace equality in a follow-up. -/
theorem Drho_tensor_I_eq_marginal
    {m : Type} [Fintype m] [DecidableEq m] :
    True := by
  -- PLAN: Placeholder for partial trace identity. Full implementation requires partial trace
  --       machinery (trace over subsystem) and will be developed in follow-up phase.
  -- DEPENDS: (deferred) partial trace definition, density marginals
  trivial

/-- **(i)** Isometry covariance: `D_ρ(Z₁ ∥ Z₂) = D_{VρV†}(V Z₁ V† ∥ V Z₂ V†)`. -/
theorem Drho_isometry_covariant
    {m : Type} [Fintype m] [DecidableEq m]
    (ρd : Density n) (V : Matrix m n ℂ) (hIso : RobustLCS.Isometry.IsometryProp V)
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
  -- PLAN: Isometry covariance. Expand definitions of D_ρ and ⟪·,·⟫_ρ for both sides.
  --       Use (VZ V†-VW V†)† = VZ† V† - VW† V† = V(Z† - W†) V†.
  --       Apply hIso (V†V = I) to cancel these in the trace inner product.
  -- DEPENDS: Drho definition, rhoInner definition, Matrix.conjTranspose_mul, Matrix.mul_assoc,
  --          trace_mul_cycle, hIso (IsometryProp V), Hermiticity of ρd
  -- TACTIC SKETCH:
  --   unfold Drho rhoInner
  --   congr 1
  --   rw [show V * (Z₁ - Z₂) * Vᴴ = V * Z₁ * Vᴴ - V * Z₂ * Vᴴ by ring]
  --   rw [conjTranspose_mul, mul_assoc, mul_assoc, ← mul_assoc Zᴴ]
  --   rw [← mul_assoc Wᴴ]
  --   rw [hIso]  -- V†V = I
  --   simp only [one_mul]
  --   rw [trace_mul_cycle]
  sorry

/-- **(j)** Projection support: if `P ρ = ρ` and `P` is a projection,
    then `D_ρ(ZP ∥ I) = D_ρ(Z ∥ I) = D_ρ(Z ∥ P)`.
**Proof strategy:** Use hSupp (P ρ = ρ) with projection property (P P = P) to simplify
trace inner products. (ZP - I)† (ZP - I) simplifies via projection idempotence and support. -/
theorem Drho_proj_support (ρd : Density n)
    {P Z : M n} (hProj : P * P = P) (hSupp : P * ρd.ρ = ρd.ρ) :
    Drho ρd (Z * P) (1) = Drho ρd Z (1)
    ∧ Drho ρd Z P = Drho ρd Z (1) := by
  -- PLAN: Two-part proof:
  --   (1) Show D_ρ(Z P ∥ I) = D_ρ(Z ∥ I): Use (ZP - I)† = P Z† - I (projection idempotence).
  --       Trace simplification via hSupp and hProj yields equality.
  --   (2) Show D_ρ(Z ∥ P) = D_ρ(Z ∥ I): Use (Z - P)† = Z† - P (P is Hermitian projection).
  --       Trace simplification via hSupp yields equivalence.
  -- DEPENDS: Drho definition, rhoInner definition, hProj (P² = P), hSupp (Pρ = ρ),
  --          Matrix.conjTranspose_sub, trace_mul_cycle, Hermiticity of projection P
  -- TACTIC SKETCH:
  --   constructor
  --   · unfold Drho rhoInner; simp only [mul_sub, sub_mul]; rw [show P*Zᴴ = Zᴴ by ...]; ring
  --   · unfold Drho rhoInner; simp only [sub_mul]; rw [show Zᴴ*P - P = ... by ...]; ring
  sorry

end Density
end RobustLCS
