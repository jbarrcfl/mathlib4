/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.MatrixSVD
public import Mathlib.Analysis.Matrix.Normed

/-!
# The matrix Frobenius norm and singular values

This file identifies the basis-independent Hilbert--Schmidt norm transported through
`Matrix.toEuclideanLin` with Mathlib's entrywise Frobenius norm, then restates the matrix
Eckart--Young--Mirsky results using the native scoped norm.
-/

open Module

namespace Matrix

public section
variable {𝕜 : Type*} [RCLike 𝕜]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The transported squared Hilbert--Schmidt norm is the sum of squared entry norms. -/
theorem hilbertSchmidtNormSq_eq_sum_entry_norm_sq (A : Matrix m n 𝕜) :
    A.hilbertSchmidtNormSq = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.hilbertSchmidtNormSq,
    LinearMap.hilbertSchmidtNormSq_eq_sum_norm_sq_basis _
      ((EuclideanSpace.basisFun n 𝕜).reindex (Fintype.equivFin n))]
  simp only [OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply,
    Matrix.toLpLin_apply, PiLp.norm_eq_of_L2, PiLp.single,
    Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc
    ∑ j : Fin (Fintype.card n), ∑ i : m, ‖A i ((Fintype.equivFin n).symm j)‖ ^ 2 =
        ∑ j : n, ∑ i : m, ‖A i j‖ ^ 2 :=
      Fintype.sum_equiv (Fintype.equivFin n).symm
        (fun j : Fin (Fintype.card n) => ∑ i : m, ‖A i ((Fintype.equivFin n).symm j)‖ ^ 2)
        (fun j : n => ∑ i : m, ‖A i j‖ ^ 2) fun _ => rfl
    _ = ∑ i : m, ∑ j : n, ‖A i j‖ ^ 2 := Finset.sum_comm

/-- The transported Hilbert--Schmidt norm is the square root of the entrywise square sum. -/
theorem hilbertSchmidtNorm_eq_sqrt_sum_entry_norm_sq (A : Matrix m n 𝕜) :
    A.hilbertSchmidtNorm = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [Matrix.hilbertSchmidtNorm, LinearMap.hilbertSchmidtNorm,
    ← Matrix.hilbertSchmidtNormSq]
  exact congrArg Real.sqrt (A.hilbertSchmidtNormSq_eq_sum_entry_norm_sq)

open scoped Matrix.Norms.Frobenius in
/-- The transported Hilbert--Schmidt norm equals Mathlib's native matrix Frobenius norm. -/
theorem hilbertSchmidtNorm_eq_frobeniusNorm (A : Matrix m n 𝕜) :
    A.hilbertSchmidtNorm = ‖A‖ := by
  rw [hilbertSchmidtNorm_eq_sqrt_sum_entry_norm_sq, frobenius_norm_def,
    Real.sqrt_eq_rpow]
  congr 1
  norm_num

open scoped Matrix.Norms.Frobenius in
omit [DecidableEq n] in
/-- The native squared Frobenius norm is the sum of squared matrix entries. -/
theorem frobeniusNorm_sq_eq_sum_entry_norm_sq (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  classical
  rw [← hilbertSchmidtNorm_eq_frobeniusNorm,
    hilbertSchmidtNorm_eq_sqrt_sum_entry_norm_sq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

open scoped Matrix.Norms.Frobenius in
/-- The native squared Frobenius norm is the sum of squared singular values. -/
theorem frobeniusNorm_sq_eq_sum_singularValues_sq (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i : Fin (Fintype.card n), A.singularValues i ^ 2 := by
  rw [frobeniusNorm_sq_eq_sum_entry_norm_sq,
    ← hilbertSchmidtNormSq_eq_sum_entry_norm_sq,
    hilbertSchmidtNormSq_eq_sum_singularValues_sq]

open scoped Matrix.Norms.Frobenius in
/-- The native Frobenius error of the SVD truncation is the square root of the
singular-value tail. -/
theorem frobeniusNorm_sub_svdTruncation (A : Matrix m n 𝕜) (k : ℕ) :
    ‖A - A.svdTruncation k‖ =
      Real.sqrt (∑ i : Fin (Fintype.card n),
        if k ≤ (i : ℕ) then A.singularValues i ^ 2 else 0) := by
  rw [← hilbertSchmidtNorm_eq_frobeniusNorm]
  exact A.hilbertSchmidtNorm_sub_svdTruncation k

open scoped Matrix.Norms.Frobenius in
/-- Eckart--Young--Mirsky for matrices using Mathlib's native Frobenius norm. -/
theorem frobeniusNorm_sub_svdTruncation_le {k : ℕ} (A B : Matrix m n 𝕜)
    (hB : B.rank ≤ k) (hk : k < Fintype.card n) :
    ‖A - A.svdTruncation k‖ ≤ ‖A - B‖ := by
  rw [← hilbertSchmidtNorm_eq_frobeniusNorm,
    ← hilbertSchmidtNorm_eq_frobeniusNorm]
  exact hilbertSchmidtNorm_sub_svdTruncation_le A B hB hk

end

end Matrix
