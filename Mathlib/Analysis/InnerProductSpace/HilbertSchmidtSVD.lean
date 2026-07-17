/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.SingularValuesNorm
public import Mathlib.Analysis.InnerProductSpace.SingularValueDecomposition

/-!
# Hilbert-Schmidt norm and Frobenius-norm Eckart-Young identity
-/

open InnerProductSpace Module RCLike LinearMap

namespace LinearMap

public section

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)

/-- The Hilbert-Schmidt (Frobenius) norm squared of T, defined via T's right singular basis. -/
@[expose] noncomputable def hilbertSchmidtNormSq : ℝ :=
  ∑ i : Fin n, ‖T (T.rightSingularBasis hn i)‖ ^ 2

/-- The Hilbert-Schmidt (Frobenius) norm of T. -/
@[expose] noncomputable def hilbertSchmidtNorm : ℝ :=
  Real.sqrt (T.hilbertSchmidtNormSq hn)

variable {T hn}

/-- The HS norm squared equals the sum of squared singular values. -/
theorem hilbertSchmidtNormSq_eq_sum_sq :
    T.hilbertSchmidtNormSq hn = ∑ i : Fin n, T.singularValues i ^ 2 := by
  simp only [hilbertSchmidtNormSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact norm_image_sq (T := T) (hn := hn) i

/-- Basis independence: sum_j ||S(b_j)||^2 = sum_i S.singularValues_i^2 for any ONB b.
The rank witness hmE is passed explicitly to bring n and hn into scope. -/
private theorem sum_norm_sq_any_basis {m : ℕ} (hmE : finrank 𝕜 E = m)
    (S : E →ₗ[𝕜] F) (b : OrthonormalBasis (Fin m) 𝕜 E) :
    ∑ j : Fin m, ‖S (b j)‖ ^ 2 = ∑ i : Fin m, S.singularValues i ^ 2 := by
  have hexp : ∀ j : Fin m, ‖S (b j)‖ ^ 2 =
      ∑ i : Fin m, S.singularValues i ^ 2 * ‖⟪S.rightSingularBasis hmE i, b j⟫_𝕜‖ ^ 2 := fun j =>
    normSq_image (T := S) (hn := hmE) (x := b j)
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  have hparseval : ∑ j : Fin m, ‖⟪S.rightSingularBasis hmE i, b j⟫_𝕜‖ ^ 2 = 1 := by
    have h := b.sum_sq_norm_inner_left (S.rightSingularBasis hmE i)
    rw [(rightSingularBasis_orthonormal (T := S) (hn := hmE)).norm_eq_one i, one_pow] at h
    exact h
  rw [hparseval, mul_one]

/-- The HS norm squared can be computed with any orthonormal basis. -/
theorem hilbertSchmidtNormSq_eq_sum_norm_sq_basis (S : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    S.hilbertSchmidtNormSq hn = ∑ i : Fin n, ‖S (b i)‖ ^ 2 := by
  rw [hilbertSchmidtNormSq_eq_sum_sq]
  exact (sum_norm_sq_any_basis hn S b).symm

/-- (Frobenius Eckart-Young, squared) ||T - A_k||_F^2 = sum_{i >= k} sigma_i(T)^2.
Proof: switch to T's right singular basis, expand via normSq_sub_truncation,
swap sums, then collapse each column by Parseval. -/
theorem hilbertSchmidtNormSq_sub_truncation (k : ℕ) :
    (T - T.truncation hn k).hilbertSchmidtNormSq hn
      = ∑ i : Fin n, if k ≤ (i : ℕ) then T.singularValues i ^ 2 else 0 := by
  rw [hilbertSchmidtNormSq_eq_sum_norm_sq_basis _ (T.rightSingularBasis hn)]
  simp only [LinearMap.sub_apply]
  have step : ∀ j : Fin n,
      ‖T (T.rightSingularBasis hn j) - T.truncation hn k (T.rightSingularBasis hn j)‖ ^ 2 =
        ∑ i : Fin n, if k ≤ (i : ℕ) then
          T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, T.rightSingularBasis hn j⟫_𝕜‖ ^ 2
        else 0 := fun j =>
    normSq_sub_truncation (T := T) (hn := hn) k (T.rightSingularBasis hn j)
  simp_rw [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hki : k ≤ (i : ℕ)
  · simp only [if_pos hki]
    rw [← Finset.mul_sum]
    have hparseval : ∑ j : Fin n,
        ‖⟪T.rightSingularBasis hn i, T.rightSingularBasis hn j⟫_𝕜‖ ^ 2 = 1 := by
      have h := (T.rightSingularBasis hn).sum_sq_norm_inner_left (T.rightSingularBasis hn i)
      rw [(rightSingularBasis_orthonormal (T := T) (hn := hn)).norm_eq_one i, one_pow] at h
      exact h
    rw [hparseval, mul_one]
  · simp only [if_neg hki, Finset.sum_const_zero]

/-- (Frobenius Eckart-Young identity) ||T - A_k||_F = sqrt(sum_{i >= k} sigma_i(T)^2). -/
theorem hilbertSchmidtNorm_sub_truncation (k : ℕ) :
    (T - T.truncation hn k).hilbertSchmidtNorm hn =
      Real.sqrt (∑ i : Fin n, if k ≤ (i : ℕ) then T.singularValues i ^ 2 else 0) := by
  rw [hilbertSchmidtNorm, hilbertSchmidtNormSq_sub_truncation]

/-- **Rank bound for truncation.** The range of the rank-`j` truncation has finrank ≤ j. -/
private lemma finrank_range_truncation_le
    {T : E →ₗ[𝕜] F} {n : ℕ} (hn : finrank 𝕜 E = n) (j : ℕ) :
    finrank 𝕜 (LinearMap.range (T.truncation hn j)) ≤ j := by
  by_cases hjn : n ≤ j
  · -- range ≤ E, so finrank ≤ n ≤ j
    exact (LinearMap.finrank_range_le _).trans (hn ▸ hjn)
  · push Not at hjn
    -- j < n: range ⊆ span of the first j left singular vectors
    let b : Fin j → F := fun i =>
      T.leftSingularVector hn ⟨(i : ℕ), i.isLt.trans hjn⟩
    have hrange : LinearMap.range (T.truncation hn j) ≤
        Submodule.span 𝕜 (Set.range b) := by
      rintro y ⟨x, rfl⟩
      rw [truncation_apply]
      apply Submodule.sum_mem
      intro i _
      by_cases hij : (i : ℕ) < j
      · rw [if_pos hij]
        have hlsv : T.leftSingularVector hn i ∈ Submodule.span 𝕜 (Set.range b) :=
          Submodule.subset_span ⟨⟨(i : ℕ), hij⟩, by congr 1⟩
        simp only [svdTerm]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hlsv)
      · simp [if_neg hij]
    calc finrank 𝕜 (LinearMap.range (T.truncation hn j))
        ≤ finrank 𝕜 (Submodule.span 𝕜 (Set.range b)) := Submodule.finrank_mono hrange
      _ ≤ j := by
            haveI : DecidableEq F := Classical.decEq F
            calc finrank 𝕜 (Submodule.span 𝕜 (Set.range b))
                ≤ (Set.range b).toFinset.card := finrank_span_le_card (Set.range b)
              _ = (Finset.univ.image b).card := by rw [Set.toFinset_range]
              _ ≤ Finset.univ.card := Finset.card_image_le
              _ = j := by simp [Finset.card_univ, Fintype.card_fin]

/-- **Frobenius-norm Eckart-Young-Mirsky optimality.** For any rank-≤k linear map B,
the HS-norm error of the rank-k truncation A_k is at most the HS-norm error of B:
  hilbertSchmidtNorm (T − A_k) ≤ hilbertSchmidtNorm (T − B).
Equivalently, A_k is the best rank-≤k approximation to T in the Hilbert-Schmidt (Frobenius) norm.

Proof sketch:
1. Rewrite both HS norms to sums of squared singular values via `hilbertSchmidtNormSq_eq_sum_sq`.
2. Weyl interlacing: for each i ≥ k, T.sv i ≤ (T−B).sv (i−k), obtained by applying
   `eckart_young_mirsky` to T with the map C = (T−B).truncation hn (i−k) + B (rank ≤ i).
3. Sum the squared Weyl bounds, reindex, and drop extra nonneg RHS terms. -/
theorem hilbertSchmidtNorm_sub_truncation_le {k : ℕ} (B : E →ₗ[𝕜] F)
    (hB : finrank 𝕜 (LinearMap.range B) ≤ k) (_hk : k < n) :
    (T - T.truncation hn k).hilbertSchmidtNorm hn
      ≤ (T - B).hilbertSchmidtNorm hn := by
  simp only [hilbertSchmidtNorm]
  apply Real.sqrt_le_sqrt
  -- Unpack both sides into sums of squared singular values
  have eq1 : (T - T.truncation hn k).hilbertSchmidtNormSq hn =
      ∑ i : Fin n, if k ≤ (i : ℕ) then T.singularValues i ^ 2 else 0 :=
    hilbertSchmidtNormSq_sub_truncation k
  have eq2 : (T - B).hilbertSchmidtNormSq hn =
      ∑ i : Fin n, (T - B).singularValues i ^ 2 :=
    hilbertSchmidtNormSq_eq_sum_sq
  rw [eq1, eq2]
  -- Goal: ∑ i, (if k ≤ ↑i then T.sv i^2 else 0) ≤ ∑ i, (T−B).sv i^2
  -- Step 1: Weyl inequality: for i : Fin n with k ≤ i, T.sv i ≤ (T−B).sv (i−k)
  have weyl : ∀ (i : Fin n) (hi : k ≤ (i : ℕ)),
      T.singularValues i ≤ (T - B).singularValues ((i : ℕ) - k) := by
    intro i hi
    -- Let j = (i:ℕ) − k; then j + k = (i:ℕ) < n
    set j := (i : ℕ) - k with hj_def
    have hjk : j + k = (i : ℕ) := Nat.sub_add_cancel hi
    have hlt : j + k < n := hjk ▸ i.isLt
    -- Build the witness map C = (T−B).truncation hn j + B, rank ≤ j + k
    set C := (T - B).truncation hn j + B with hC_def
    have hrank_C : finrank 𝕜 (LinearMap.range C) ≤ j + k := by
      have h1 : LinearMap.range C ≤
          LinearMap.range ((T - B).truncation hn j) ⊔ LinearMap.range B := by
        rw [hC_def]; exact LinearMap.range_add_le _ _
      have hlt1 : finrank 𝕜 (LinearMap.range ((T - B).truncation hn j)) ≤ j :=
        finrank_range_truncation_le (T := T - B) hn j
      -- Provide Module.Finite instances explicitly to avoid universe-Max synthesis failure
      haveI hfi : Module.Finite 𝕜 ↥(LinearMap.range ((T - B).truncation hn j)) := inferInstance
      haveI hgi : Module.Finite 𝕜 ↥(LinearMap.range B) := inferInstance
      haveI hsup :
          Module.Finite 𝕜 ↥(LinearMap.range ((T - B).truncation hn j) ⊔ LinearMap.range B) :=
        Submodule.finite_sup _ _
      linarith [Submodule.finrank_mono h1,
                Submodule.finrank_add_le_finrank_add_finrank
                  (LinearMap.range ((T - B).truncation hn j)) (LinearMap.range B),
                hlt1, hB]
    -- T − C = (T−B) − (T−B).truncation hn j
    have hTmC : T - C = (T - B) - (T - B).truncation hn j := by
      simp only [hC_def]; abel
    -- By Eckart–Young (operator norm), T.sv (j+k) ≤ ‖(T−C)‖ = (T−B).sv j
    have h_ey := eckart_young_mirsky (T := T) (hn := hn) C hrank_C hlt
    have hnorm : ‖(T - C).toContinuousLinearMap‖ = (T - B).singularValues j := by
      rw [hTmC]
      exact norm_sub_truncation_eq (T := T - B) (hn := hn) j
    rw [hjk, hnorm] at h_ey
    exact h_ey
  -- Step 2: Apply Weyl term-by-term to bound LHS ≤ ∑ i, (if k≤i then (T−B).sv(i−k)^2 else 0)
  have step1 : ∑ i : Fin n, (if k ≤ (i : ℕ) then T.singularValues i ^ 2 else 0) ≤
      ∑ i : Fin n, (if k ≤ (i : ℕ) then (T - B).singularValues ((i : ℕ) - k) ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : k ≤ (i : ℕ)
    · simp only [if_pos hi]
      exact pow_le_pow_left₀ (T.singularValues_nonneg i) (weyl i hi) 2
    · simp [if_neg hi]
  -- Step 3: Reindex the intermediate sum ≤ ∑ i, (T−B).sv i^2
  have step2 : ∑ i : Fin n, (if k ≤ (i : ℕ) then (T - B).singularValues ((i : ℕ) - k) ^ 2 else 0) ≤
      ∑ i : Fin n, (T - B).singularValues i ^ 2 := by
    -- Let S = filter (k ≤ ·) univ and φ i = ⟨i−k, _⟩ : Fin n for i ∈ S
    let S := Finset.filter (fun i : Fin n => k ≤ (i : ℕ)) Finset.univ
    let φ : Fin n → Fin n := fun i => ⟨(i : ℕ) - k, (Nat.sub_le (i : ℕ) k).trans_lt i.isLt⟩
    -- LHS = ∑ i ∈ S, (T−B).sv(i−k)^2
    have hLHS : ∑ i : Fin n, (if k ≤ (i : ℕ) then (T - B).singularValues ((i : ℕ) - k) ^ 2 else 0) =
        ∑ i ∈ S, (T - B).singularValues ((i : ℕ) - k) ^ 2 := by
      simp only [S, ← Finset.sum_filter]
    -- φ is injective on S
    have hφ_inj : Set.InjOn φ (S : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have heq : (a : ℕ) - k = (b : ℕ) - k := congr_arg Fin.val hab
      exact Fin.ext (by omega)
    -- ∑ i ∈ S, sv(i−k)^2 = ∑ j ∈ S.image φ, sv j^2  (reindex)
    have hreindex : ∑ i ∈ S, (T - B).singularValues ((i : ℕ) - k) ^ 2 =
        ∑ j ∈ S.image φ, (T - B).singularValues j ^ 2 := by
      rw [Finset.sum_image hφ_inj]
    -- ∑ j ∈ S.image φ, sv j^2 ≤ ∑ j : Fin n, sv j^2
    have hsubset : ∑ j ∈ S.image φ, (T - B).singularValues j ^ 2 ≤
        ∑ j : Fin n, (T - B).singularValues j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => by positivity)
    calc ∑ i : Fin n, (if k ≤ (i : ℕ) then (T - B).singularValues ((i : ℕ) - k) ^ 2 else 0)
        = ∑ i ∈ S, (T - B).singularValues ((i : ℕ) - k) ^ 2 := hLHS
      _ = ∑ j ∈ S.image φ, (T - B).singularValues j ^ 2 := hreindex
      _ ≤ ∑ j : Fin n, (T - B).singularValues j ^ 2 := hsubset
  linarith [step1, step2]

end

end LinearMap
