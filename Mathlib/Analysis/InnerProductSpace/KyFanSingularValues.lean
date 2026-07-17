/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.CourantFischerSingularValues

/-!
# Ky Fan maximum principle for singular values

This file proves the finite-dimensional Ky Fan maximum principle for the squared singular values.
For an orthonormal `k`-frame `e`, the energy `∑ j, ‖T (e j)‖²` is at most the sum of the first
`k` squared singular values, with equality for the first `k` right singular vectors.

The proof isolates the required weighted majorization argument.  Relative to a full right singular
basis, the frame has coefficients `cᵢ = ∑ j, ‖⟪vᵢ, eⱼ⟫‖²`.  Bessel and Parseval give
`0 ≤ cᵢ ≤ 1` and `∑ i, cᵢ = k`; monotonicity of `σᵢ²` then bounds the weighted sum by its first
`k` terms.
-/

public section

open InnerProductSpace Module RCLike

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]
  {T : E →ₗ[𝕜] F} {n : ℕ}

private theorem weighted_sum_le_top
    (a c : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hcsum : ∑ i, c i = k) :
    (∑ i : Fin n, a i * c i) ≤
      ∑ i : Fin n, if (i : ℕ) < k then a i else 0 := by
  by_cases hkn : k = n
  · subst k
    simp only [Fin.is_lt, if_true]
    exact Finset.sum_le_sum fun i _ ↦ by
      nlinarith [hc1 i, ha0 i]
  · have hklt : k < n := lt_of_le_of_ne hk hkn
    let q : Fin n := ⟨k, hklt⟩
    let head : Finset (Fin n) := Finset.univ.filter fun i ↦ (i : ℕ) < k
    let tail : Finset (Fin n) := Finset.univ.filter fun i ↦ k ≤ (i : ℕ)
    have hpartition : head ∪ tail = Finset.univ := by
      ext i
      simp [head, tail, lt_or_ge]
    have hdisj : Disjoint head tail := by
      refine Finset.disjoint_left.mpr ?_
      intro i hih hit
      simp only [head, Finset.mem_filter, Finset.mem_univ, true_and] at hih
      simp only [tail, Finset.mem_filter, Finset.mem_univ, true_and] at hit
      omega
    have hcard : (head.card : ℝ) = k := by
      have : head.card = k := by
        simpa [head, min_eq_right hk] using (Fin.card_filter_val_lt (n := n) (m := k))
      exact_mod_cast this
    have hmass : ∑ i ∈ head, (1 - c i) = ∑ i ∈ tail, c i := by
      have hsplit : (∑ i ∈ head, c i) + ∑ i ∈ tail, c i = k := by
        rw [← hcsum, ← Finset.sum_union hdisj, hpartition]
      rw [Finset.sum_sub_distrib]
      have hone : ∑ _i ∈ head, (1 : ℝ) = k := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hcard
      rw [hone]
      linarith
    have hhead : ∑ i ∈ head, a q * (1 - c i) ≤ ∑ i ∈ head, a i * (1 - c i) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hik : (i : ℕ) ≤ k := by
        simp only [head, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        omega
      have hai : a q ≤ a i := ha hik
      exact mul_le_mul_of_nonneg_right hai (sub_nonneg.mpr (hc1 i))
    have htail : ∑ i ∈ tail, a i * c i ≤ ∑ i ∈ tail, a q * c i := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hki : k ≤ (i : ℕ) := by
        simpa only [tail, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have hai : a i ≤ a q := ha hki
      exact mul_le_mul_of_nonneg_right hai (hc0 i)
    have hmain : ∑ i ∈ tail, a i * c i ≤ ∑ i ∈ head, a i * (1 - c i) := by
      calc
        ∑ i ∈ tail, a i * c i ≤ ∑ i ∈ tail, a q * c i := htail
        _ = ∑ i ∈ head, a q * (1 - c i) := by
          simp_rw [← Finset.mul_sum]
          rw [hmass]
        _ ≤ ∑ i ∈ head, a i * (1 - c i) := hhead
    have hfull : (∑ i : Fin n, a i * c i) =
        (∑ i ∈ head, a i * c i) + ∑ i ∈ tail, a i * c i := by
      rw [← Finset.sum_union hdisj, hpartition]
    rw [hfull]
    have htop : (∑ i : Fin n, if (i : ℕ) < k then a i else 0) = ∑ i ∈ head, a i := by
      dsimp only [head]
      rw [Finset.sum_filter]
    rw [htop]
    calc
      (∑ i ∈ head, a i * c i) + ∑ i ∈ tail, a i * c i
          ≤ (∑ i ∈ head, a i * c i) + ∑ i ∈ head, a i * (1 - c i) :=
        by linarith [hmain]
      _ = ∑ i ∈ head, a i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring

omit [CompleteSpace E] [CompleteSpace F] in
/-- The squared overlaps of an orthonormal frame with an orthonormal basis form weights in
`[0,1]` whose total mass is the frame cardinality. -/
theorem orthonormalFrame_overlap_weights
    (hn : finrank 𝕜 E = n) {k : ℕ} (e : Fin k → E) (he : Orthonormal 𝕜 e) :
    (∀ i : Fin n, 0 ≤ ∑ j : Fin k, ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2) ∧
    (∀ i : Fin n, (∑ j : Fin k, ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2) ≤ 1) ∧
    (∑ i : Fin n, ∑ j : Fin k, ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2) = k := by
  constructor
  · intro i
    positivity
  constructor
  · intro i
    calc
      ∑ j : Fin k, ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2
          = ∑ j : Fin k, ‖⟪e j, T.rightSingularBasis hn i⟫_𝕜‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [norm_inner_symm]
      _ ≤ ‖T.rightSingularBasis hn i‖ ^ 2 :=
        he.sum_inner_products_le (T.rightSingularBasis hn i) (s := Finset.univ)
      _ = 1 := by rw [(T.rightSingularBasis hn).norm_eq_one]; norm_num
  · rw [Finset.sum_comm]
    calc
      ∑ j : Fin k, ∑ i : Fin n, ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2
          = ∑ _j : Fin k, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [(T.rightSingularBasis hn).sum_sq_norm_inner_right]
            rw [he.norm_eq_one]
            norm_num
      _ = k := by simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ky Fan maximum principle (squared singular values).** The energy captured by any
orthonormal `k`-frame is at most the sum of the first `k` squared singular values. -/
theorem sum_norm_sq_image_orthonormal_le_sum_top_sq_singularValues
    (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k ≤ n)
    (e : Fin k → E) (he : Orthonormal 𝕜 e) :
    ∑ j : Fin k, ‖T (e j)‖ ^ 2 ≤
      ∑ i : Fin n, if (i : ℕ) < k then T.singularValues i ^ 2 else 0 := by
  let c : Fin n → ℝ := fun i ↦
    ∑ j : Fin k, ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2
  obtain ⟨hc0, hc1, hcsum⟩ := orthonormalFrame_overlap_weights
    (T := T) hn e he
  have ha : Antitone (fun i : Fin n ↦ T.singularValues i ^ 2) := by
    intro i j hij
    have hs := T.singularValues_antitone hij
    nlinarith [T.singularValues_nonneg i, T.singularValues_nonneg j]
  have hweighted := weighted_sum_le_top
    (fun i : Fin n ↦ T.singularValues i ^ 2) c k hk ha
      (fun i ↦ sq_nonneg (T.singularValues i)) hc0 hc1 hcsum
  calc
    ∑ j : Fin k, ‖T (e j)‖ ^ 2
        = ∑ j : Fin k, ∑ i : Fin n,
            T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, e j⟫_𝕜‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact normSq_image (T := T) (hn := hn) (e j)
    _ = ∑ i : Fin n, T.singularValues i ^ 2 * c i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [c, Finset.mul_sum]
    _ ≤ _ := hweighted

private theorem sum_castLE_eq_sum_top {k : ℕ} (hk : k ≤ n) (a : Fin n → ℝ) :
    (∑ j : Fin k, a (Fin.castLE hk j)) =
      ∑ i : Fin n, if (i : ℕ) < k then a i else 0 := by
  rw [← Finset.sum_filter]
  let s : Finset (Fin n) := Finset.univ.filter fun i ↦ (i : ℕ) < k
  have hs : ∀ i : Fin n, i ∈ s ↔ (i : ℕ) < k := by simp [s]
  rw [show (Finset.univ.filter fun i : Fin n ↦ (i : ℕ) < k) = s from rfl]
  rw [Finset.sum_subtype s hs]
  exact (Fin.castLEquiv hk).sum_comp (fun i ↦ a i.1)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first `k` right singular vectors attain the Ky Fan upper bound. -/
theorem sum_norm_sq_image_first_rightSingularVectors
    (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k ≤ n) :
    ∑ j : Fin k, ‖T (T.rightSingularBasis hn (Fin.castLE hk j))‖ ^ 2 =
      ∑ i : Fin n, if (i : ℕ) < k then T.singularValues i ^ 2 else 0 := by
  calc
    ∑ j : Fin k, ‖T (T.rightSingularBasis hn (Fin.castLE hk j))‖ ^ 2
        = ∑ j : Fin k, T.singularValues (Fin.castLE hk j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact norm_image_sq (T := T) (hn := hn) (Fin.castLE hk j)
    _ = _ := sum_castLE_eq_sum_top hk (fun i ↦ T.singularValues i ^ 2)

/-- Energies captured by orthonormal `k`-frames. -/
def kyFanFrameEnergies (T : E →ₗ[𝕜] F) (k : ℕ) : Set ℝ :=
  {r | ∃ e : Fin k → E, Orthonormal 𝕜 e ∧ r = ∑ j : Fin k, ‖T (e j)‖ ^ 2}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Classical Ky Fan maximum principle.** The sum of the first `k` squared singular values is
the greatest energy captured by an orthonormal `k`-frame. -/
theorem isGreatest_kyFanFrameEnergies
    (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k ≤ n) :
    IsGreatest (T.kyFanFrameEnergies k)
      (∑ i : Fin n, if (i : ℕ) < k then T.singularValues i ^ 2 else 0) := by
  constructor
  · let e : Fin k → E := fun j ↦ T.rightSingularBasis hn (Fin.castLE hk j)
    refine ⟨e, ?_, ?_⟩
    · exact (rightSingularBasis_orthonormal (T := T) (hn := hn)).comp (Fin.castLE hk)
        (Fin.castLE_injective hk)
    · exact (sum_norm_sq_image_first_rightSingularVectors
        (T := T) hn hk).symm
  · rintro r ⟨e, he, rfl⟩
    exact sum_norm_sq_image_orthonormal_le_sum_top_sq_singularValues
      (T := T) hn hk e he

end LinearMap
