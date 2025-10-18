import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Simp Lemmas for Matrix Algebra

This file provides convenience simp lemmas for conjugate transpose and matrix multiplication,
used throughout the formalization to simplify matrix expressions in proofs.

## Main simp lemmas

* `conjTranspose_mul`: Conjugate transpose of a product reverses order: (A*B)† = B†*A†
* `conjTranspose_conjTranspose`: Double conjugate is identity: (A†)† = A
* `mul_one'`: Right multiplicative identity: A * I = A
* `one_mul'`: Left multiplicative identity: I * A = A

-/

open Matrix Complex

namespace RobustLCS.Tactics
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
