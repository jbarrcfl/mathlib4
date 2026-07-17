/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.HilbertSchmidtSVD

/-!
# Courant--Fischer and Weyl principles for singular values

This file packages the variational content of the finite-dimensional SVD.  It gives an attained
top-singular-subspace lower bound, the rank-approximation min--max characterization of each
singular value, and Weyl interlacing under a low-rank perturbation.
-/

public section

open InnerProductSpace Module RCLike

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]
  {T : E →ₗ[𝕜] F} {n : ℕ} (hn : finrank 𝕜 E = n)

/-- The error values attained by rank-at-most-`k` approximations to `T`. -/
def rankApproximationErrors (T : E →ₗ[𝕜] F) (k : ℕ) : Set ℝ :=
  {r | ∃ B : E →ₗ[𝕜] F,
    finrank 𝕜 (LinearMap.range B) ≤ k ∧ r = ‖(T - B).toContinuousLinearMap‖}

/-- The Hilbert--Schmidt error values attained by rank-at-most-`k` approximations to `T`. -/
noncomputable def hilbertSchmidtRankApproximationErrors
    (T : E →ₗ[𝕜] F) (hn : finrank 𝕜 E = n) (k : ℕ) : Set ℝ :=
  {r | ∃ B : E →ₗ[𝕜] F,
    finrank 𝕜 (LinearMap.range B) ≤ k ∧ r = (T - B).hilbertSchmidtNorm hn}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Attained Courant--Fischer lower subspace.** On the span of the first `k+1` right singular
vectors, `T` expands every vector by at least `σ_k`. -/
theorem singularValues_mul_norm_le_of_mem_topSingularSpan {k : ℕ} (hk : k < n)
    {x : E} (hx : x ∈ T.topSingularSpan hn hk) :
    T.singularValues k * ‖x‖ ≤ ‖T x‖ := by
  have hsq := sq_singularValues_mul_normSq_le_normSq_image
    (T := T) (hn := hn) hk hx
  have hs : 0 ≤ T.singularValues k := T.singularValues_nonneg k
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hTx0 : 0 ≤ ‖T x‖ := norm_nonneg (T x)
  nlinarith [sq_nonneg (T.singularValues k * ‖x‖ - ‖T x‖)]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The top `k+1` singular span attains the lower-subspace side of Courant--Fischer: it has
dimension `k+1`, and every vector in it satisfies `σ_k ‖x‖ ≤ ‖T x‖`. -/
theorem exists_submodule_finrank_succ_and_singularValues_mul_norm_le
    (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    ∃ W : Submodule 𝕜 E, finrank 𝕜 W = k + 1 ∧
      ∀ x : E, x ∈ W → T.singularValues k * ‖x‖ ≤ ‖T x‖ := by
  refine ⟨T.topSingularSpan hn hk, finrank_topSingularSpan (T := T) (hn := hn) hk, ?_⟩
  intro x hx
  exact singularValues_mul_norm_le_of_mem_topSingularSpan (T := T) (hn := hn) hk hx

omit [CompleteSpace E] [CompleteSpace F] in
private theorem finrank_range_truncation_le_aux (hn : finrank 𝕜 E = n)
    (S : E →ₗ[𝕜] F) (j : ℕ) :
    finrank 𝕜 (LinearMap.range (S.truncation hn j)) ≤ j := by
  by_cases hjn : n ≤ j
  · exact (LinearMap.finrank_range_le _).trans (hn ▸ hjn)
  · push Not at hjn
    let b : Fin j → F := fun i =>
      S.leftSingularVector hn ⟨(i : ℕ), i.isLt.trans hjn⟩
    have hrange : LinearMap.range (S.truncation hn j) ≤
        Submodule.span 𝕜 (Set.range b) := by
      rintro y ⟨x, rfl⟩
      rw [truncation_apply]
      apply Submodule.sum_mem
      intro i _
      by_cases hij : (i : ℕ) < j
      · rw [if_pos hij]
        have hlsv : S.leftSingularVector hn i ∈ Submodule.span 𝕜 (Set.range b) :=
          Submodule.subset_span ⟨⟨(i : ℕ), hij⟩, by congr 1⟩
        simp only [svdTerm]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hlsv)
      · simp [if_neg hij]
    calc
      finrank 𝕜 (LinearMap.range (S.truncation hn j))
          ≤ finrank 𝕜 (Submodule.span 𝕜 (Set.range b)) := Submodule.finrank_mono hrange
      _ ≤ j := by
        haveI : DecidableEq F := Classical.decEq F
        calc
          finrank 𝕜 (Submodule.span 𝕜 (Set.range b))
              ≤ (Set.range b).toFinset.card := finrank_span_le_card (Set.range b)
          _ = (Finset.univ.image b).card := by rw [Set.toFinset_range]
          _ ≤ Finset.univ.card := Finset.card_image_le
          _ = j := by simp [Finset.card_univ, Fintype.card_fin]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Rank-approximation Courant--Fischer principle.** `σ_k` is the least operator-norm error
attained by a rank-at-most-`k` approximation.  The rank-`k` SVD truncation attains the minimum. -/
theorem isLeast_rankApproximationErrors (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    IsLeast (T.rankApproximationErrors k) (T.singularValues k) := by
  constructor
  · refine ⟨T.truncation hn k, ?_, ?_⟩
    · exact finrank_range_truncation_le_aux hn T k
    · exact (norm_sub_truncation_eq (T := T) (hn := hn) k).symm
  · rintro r ⟨B, hB, rfl⟩
    exact eckart_young_mirsky (T := T) (hn := hn) B hB hk

omit [CompleteSpace E] [CompleteSpace F] in
/-- A convenient quantified form of the rank-approximation min--max characterization. -/
theorem singularValues_eq_rankApproximation_iff (hn : finrank 𝕜 E = n)
    {k : ℕ} (hk : k < n) :
    (T.singularValues k ∈ T.rankApproximationErrors k) ∧
      ∀ B : E →ₗ[𝕜] F, finrank 𝕜 (LinearMap.range B) ≤ k →
        T.singularValues k ≤ ‖(T - B).toContinuousLinearMap‖ := by
  exact ⟨(isLeast_rankApproximationErrors (T := T) hn hk).1,
    fun B hB ↦ eckart_young_mirsky (T := T) (hn := hn) B hB hk⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ky Fan--Mirsky rank-approximation principle (Hilbert--Schmidt norm).** The SVD truncation
attains the least Hilbert--Schmidt error among all rank-at-most-`k` maps. -/
theorem isLeast_hilbertSchmidtRankApproximationErrors
    (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    IsLeast (T.hilbertSchmidtRankApproximationErrors hn k)
      ((T - T.truncation hn k).hilbertSchmidtNorm hn) := by
  constructor
  · exact ⟨T.truncation hn k, finrank_range_truncation_le_aux hn T k, rfl⟩
  · rintro r ⟨B, hB, rfl⟩
    exact hilbertSchmidtNorm_sub_truncation_le (T := T) (hn := hn) B hB hk

omit [CompleteSpace E] [CompleteSpace F] in
/-- Explicit Ky Fan--Mirsky minimum value: the optimal squared-tail error is the square root of
the sum of the squared singular values from index `k` onward. -/
theorem isLeast_hilbertSchmidtRankApproximationErrors_tail
    (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    IsLeast (T.hilbertSchmidtRankApproximationErrors hn k)
      (Real.sqrt (∑ i : Fin n, if k ≤ (i : ℕ) then T.singularValues i ^ 2 else 0)) := by
  simpa only [hilbertSchmidtNorm_sub_truncation (T := T) (hn := hn) k] using
    isLeast_hilbertSchmidtRankApproximationErrors (T := T) hn hk

omit [CompleteSpace E] [CompleteSpace F] in
/-- The range of the rank-`j` SVD truncation has dimension at most `j`. -/
theorem finrank_range_truncation_le_public (hn : finrank 𝕜 E = n)
    (S : E →ₗ[𝕜] F) (j : ℕ) :
    finrank 𝕜 (LinearMap.range (S.truncation hn j)) ≤ j := by
  exact finrank_range_truncation_le_aux hn S j

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Weyl interlacing for a low-rank perturbation.** If `B` has rank at most `k`, then
`σ_{j+k}(T) ≤ σ_j(T-B)` whenever `j+k` lies in the singular range. -/
theorem singularValues_add_le_of_finrank_range_le (hn : finrank 𝕜 E = n)
    {j k : ℕ} (B : E →ₗ[𝕜] F)
    (hB : finrank 𝕜 (LinearMap.range B) ≤ k) (hjk : j + k < n) :
    T.singularValues (j + k) ≤ (T - B).singularValues j := by
  let C := (T - B).truncation hn j + B
  have hrange : LinearMap.range C ≤
      LinearMap.range ((T - B).truncation hn j) ⊔ LinearMap.range B := by
    exact LinearMap.range_add_le _ _
  have htrunc : finrank 𝕜 (LinearMap.range ((T - B).truncation hn j)) ≤ j :=
    finrank_range_truncation_le_public hn (T - B) j
  haveI hfi : Module.Finite 𝕜 ↥(LinearMap.range ((T - B).truncation hn j)) := inferInstance
  haveI hgi : Module.Finite 𝕜 ↥(LinearMap.range B) := inferInstance
  haveI hsup : Module.Finite 𝕜
      ↥(LinearMap.range ((T - B).truncation hn j) ⊔ LinearMap.range B) :=
    Submodule.finite_sup _ _
  have hrank : finrank 𝕜 (LinearMap.range C) ≤ j + k := by
    linarith [Submodule.finrank_mono hrange,
      Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range ((T - B).truncation hn j)) (LinearMap.range B)]
  have hsub : T - C = (T - B) - (T - B).truncation hn j := by
    dsimp [C]
    abel
  have hEY := eckart_young_mirsky (T := T) (hn := hn) C hrank hjk
  rw [hsub, norm_sub_truncation_eq (T := T - B) (hn := hn) j] at hEY
  exact hEY

omit [CompleteSpace E] [CompleteSpace F] in
/-- Equivalent indexed Weyl form: a rank-`k` perturbation can shift the singular-value index by
at most `k`. -/
theorem singularValues_le_sub_of_finrank_range_le (hn : finrank 𝕜 E = n)
    {i k : ℕ} (B : E →ₗ[𝕜] F)
    (hB : finrank 𝕜 (LinearMap.range B) ≤ k) (hi : i < n) (hki : k ≤ i) :
    T.singularValues i ≤ (T - B).singularValues (i - k) := by
  have hsum : i - k + k = i := Nat.sub_add_cancel hki
  have hlt : i - k + k < n := by omega
  have h := singularValues_add_le_of_finrank_range_le
    (T := T) hn (j := i - k) (k := k) B hB hlt
  simpa only [hsum] using h

omit [CompleteSpace E] [CompleteSpace F] in
/-- Symmetric low-rank perturbation interlacing.  Applying Weyl to `T-B` and perturbation `-B`
gives the reverse comparison. -/
theorem sub_singularValues_add_le_of_finrank_range_le (hn : finrank 𝕜 E = n)
    {j k : ℕ} (B : E →ₗ[𝕜] F)
    (hB : finrank 𝕜 (LinearMap.range B) ≤ k) (hjk : j + k < n) :
    (T - B).singularValues (j + k) ≤ T.singularValues j := by
  have hneg : finrank 𝕜 (LinearMap.range (-B)) ≤ k := by
    rw [LinearMap.range_neg]
    exact hB
  have h := singularValues_add_le_of_finrank_range_le (T := T - B) hn (-B) hneg hjk
  simpa only [sub_neg_eq_add, sub_add_cancel] using h

end LinearMap
