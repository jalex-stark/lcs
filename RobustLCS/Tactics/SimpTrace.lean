import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

open Matrix Complex

namespace RobustLCS.Tactics

-- A few convenience simp rules for matrices.
@[simp] lemma conjTranspose_mul {m n} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    (A * B)ᴴ = Bᴴ * Aᴴ :=
  Matrix.conjTranspose_mul A B

@[simp] lemma conjTranspose_conjTranspose {n} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : (Aᴴ)ᴴ = A :=
  Matrix.conjTranspose_conjTranspose A

@[simp] lemma mul_one' {n} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    A * (1 : Matrix n n ℂ) = A := Matrix.mul_one A

@[simp] lemma one_mul' {n} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (1 : Matrix n n ℂ) * A = A := Matrix.one_mul A

end RobustLCS.Tactics
