/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.SingularValueDecomposition
public import Mathlib.Analysis.InnerProductSpace.HilbertSchmidtSVD

/-!
# Singular value decomposition for finite matrices

This file transports the finite-dimensional linear-map SVD and Eckart--Young--Mirsky
theorems to matrices through `Matrix.toEuclideanLin`.
-/

public section

open Module

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The singular values of a matrix, in decreasing order. -/
noncomputable def singularValues (A : Matrix m n 𝕜) : ℕ →₀ ℝ :=
  A.toEuclideanLin.singularValues

/-- The spectral norm of a matrix, induced by the Euclidean norms on its domain and codomain. -/
noncomputable def spectralNorm (A : Matrix m n 𝕜) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

/-- The Hilbert--Schmidt norm of a matrix, transported from its Euclidean linear map. -/
noncomputable def hilbertSchmidtNorm (A : Matrix m n 𝕜) : ℝ :=
  A.toEuclideanLin.hilbertSchmidtNorm finrank_euclideanSpace

/-- The squared Hilbert--Schmidt norm of a matrix. -/
noncomputable def hilbertSchmidtNormSq (A : Matrix m n 𝕜) : ℝ :=
  A.toEuclideanLin.hilbertSchmidtNormSq finrank_euclideanSpace

/-- The rank-`k` singular-value truncation of a matrix. -/
noncomputable def svdTruncation (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  Matrix.toEuclideanLin.symm (A.toEuclideanLin.truncation finrank_euclideanSpace k)

@[simp]
theorem toEuclideanLin_svdTruncation (A : Matrix m n 𝕜) (k : ℕ) :
    (A.svdTruncation k).toEuclideanLin =
      A.toEuclideanLin.truncation finrank_euclideanSpace k := by
  simp [svdTruncation]

/-- Matrix singular values are nonnegative. -/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (i : ℕ) :
    0 ≤ A.singularValues i :=
  A.toEuclideanLin.singularValues_nonneg i

/-- Matrix singular values are ordered decreasingly. -/
theorem singularValues_antitone (A : Matrix m n 𝕜) :
    Antitone A.singularValues :=
  A.toEuclideanLin.singularValues_antitone

/-- The matrix spectral norm is its largest singular value when the domain is nonempty. -/
theorem spectralNorm_eq_singularValues_zero [Nonempty n] (A : Matrix m n 𝕜) :
    A.spectralNorm = A.singularValues 0 := by
  exact ContinuousLinearMap.norm_eq_singularValues_zero A.toEuclideanLin.toContinuousLinearMap
    finrank_euclideanSpace (Fintype.card_pos_iff.mpr inferInstance)

omit [Fintype m] in
/-- Matrix rank agrees with the dimension of the range of its Euclidean linear map. -/
theorem rank_eq_finrank_range_toEuclideanLin [Finite m] (A : Matrix m n 𝕜) :
    A.rank = finrank 𝕜 (LinearMap.range A.toEuclideanLin) := by
  letI := Fintype.ofFinite m
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact
    A.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun m 𝕜).toBasis (EuclideanSpace.basisFun n 𝕜).toBasis

/-- The SVD truncation has matrix rank at most `k`. -/
theorem rank_svdTruncation_le (A : Matrix m n 𝕜) (k : ℕ) :
    (A.svdTruncation k).rank ≤ k := by
  rw [rank_eq_finrank_range_toEuclideanLin, toEuclideanLin_svdTruncation]
  by_cases hkn : Fintype.card n ≤ k
  · exact (LinearMap.finrank_range_le _).trans (finrank_euclideanSpace.trans_le hkn)
  · push Not at hkn
    let b : Fin k → EuclideanSpace 𝕜 m := fun i =>
      A.toEuclideanLin.leftSingularVector finrank_euclideanSpace
        ⟨(i : ℕ), i.isLt.trans hkn⟩
    have hrange : LinearMap.range
        (A.toEuclideanLin.truncation finrank_euclideanSpace k) ≤
        Submodule.span 𝕜 (Set.range b) := by
      rintro y ⟨x, rfl⟩
      rw [LinearMap.truncation_apply]
      apply Submodule.sum_mem
      intro i _
      by_cases hik : (i : ℕ) < k
      · rw [if_pos hik]
        have hu : A.toEuclideanLin.leftSingularVector finrank_euclideanSpace i ∈
            Submodule.span 𝕜 (Set.range b) :=
          Submodule.subset_span ⟨⟨(i : ℕ), hik⟩, by congr 1⟩
        simp only [LinearMap.svdTerm]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hu)
      · simp [if_neg hik]
    calc
      finrank 𝕜 (LinearMap.range
          (A.toEuclideanLin.truncation finrank_euclideanSpace k))
          ≤ finrank 𝕜 (Submodule.span 𝕜 (Set.range b)) :=
        Submodule.finrank_mono hrange
      _ ≤ k := by
        haveI : DecidableEq (EuclideanSpace 𝕜 m) := Classical.decEq _
        calc
          finrank 𝕜 (Submodule.span 𝕜 (Set.range b))
              ≤ (Set.range b).toFinset.card := finrank_span_le_card (Set.range b)
          _ = (Finset.univ.image b).card := by rw [Set.toFinset_range]
          _ ≤ Finset.univ.card := Finset.card_image_le
          _ = k := by simp

/-- Spectral-norm error of the SVD truncation equals the next singular value. -/
theorem spectralNorm_sub_svdTruncation_eq (A : Matrix m n 𝕜) (k : ℕ) :
    (A - A.svdTruncation k).spectralNorm = A.singularValues k := by
  simpa [spectralNorm, singularValues, map_sub] using
    LinearMap.norm_sub_truncation_eq (T := A.toEuclideanLin)
      (hn := finrank_euclideanSpace) k

/-- Eckart--Young--Mirsky for matrices in spectral norm. -/
theorem spectralNorm_sub_svdTruncation_le {k : ℕ} (A B : Matrix m n 𝕜)
    (hB : B.rank ≤ k) (hk : k < Fintype.card n) :
    (A - A.svdTruncation k).spectralNorm ≤ (A - B).spectralNorm := by
  have hRange : finrank 𝕜 (LinearMap.range B.toEuclideanLin) ≤ k := by
    rwa [← rank_eq_finrank_range_toEuclideanLin]
  simpa [spectralNorm, map_sub, toEuclideanLin_svdTruncation] using
    LinearMap.norm_sub_truncation_le_of_finrank_range_le
      (T := A.toEuclideanLin) (hn := finrank_euclideanSpace) B.toEuclideanLin hRange hk

/-- The squared matrix Hilbert--Schmidt norm is the sum of squared singular values. -/
theorem hilbertSchmidtNormSq_eq_sum_singularValues_sq (A : Matrix m n 𝕜) :
    A.hilbertSchmidtNormSq = ∑ i : Fin (Fintype.card n), A.singularValues i ^ 2 := by
  exact LinearMap.hilbertSchmidtNormSq_eq_sum_sq

/-- Frobenius/Hilbert--Schmidt error of the SVD truncation has the tail singular-value formula. -/
theorem hilbertSchmidtNorm_sub_svdTruncation (A : Matrix m n 𝕜) (k : ℕ) :
    (A - A.svdTruncation k).hilbertSchmidtNorm =
      Real.sqrt (∑ i : Fin (Fintype.card n),
        if k ≤ (i : ℕ) then A.singularValues i ^ 2 else 0) := by
  simpa [hilbertSchmidtNorm, singularValues, map_sub] using
    LinearMap.hilbertSchmidtNorm_sub_truncation (T := A.toEuclideanLin)
      (hn := finrank_euclideanSpace) k

/-- Eckart--Young--Mirsky for matrices in Hilbert--Schmidt norm. -/
theorem hilbertSchmidtNorm_sub_svdTruncation_le {k : ℕ} (A B : Matrix m n 𝕜)
    (hB : B.rank ≤ k) (hk : k < Fintype.card n) :
    (A - A.svdTruncation k).hilbertSchmidtNorm ≤ (A - B).hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm, hilbertSchmidtNorm, map_sub, map_sub,
    toEuclideanLin_svdTruncation]
  change (A.toEuclideanLin -
      A.toEuclideanLin.truncation finrank_euclideanSpace k).hilbertSchmidtNorm
        finrank_euclideanSpace ≤
    (A.toEuclideanLin - B.toEuclideanLin).hilbertSchmidtNorm finrank_euclideanSpace
  apply LinearMap.hilbertSchmidtNorm_sub_truncation_le
    (T := A.toEuclideanLin) (hn := finrank_euclideanSpace) B.toEuclideanLin
  · rwa [← rank_eq_finrank_range_toEuclideanLin]
  · exact hk

end Matrix
