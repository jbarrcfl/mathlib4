/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.CourantFischerSingularValues
public import Mathlib.Analysis.InnerProductSpace.HilbertSchmidtSVD

/-!
# Finite-dimensional Schatten quantities and Mirsky bounds

For a positive natural exponent `p`, this file defines the finite singular-value power sum
`sum i, sigma_i ^ p` and its `p`-th root.  It proves a general Mirsky lower bound for every
rank-at-most-`k` approximation.  The established residual-spectrum APIs then give exact
attainment for `p = 2` (Hilbert--Schmidt/Frobenius) and `p = infinity` (operator norm).

No `Norm` instance is declared for the general `p`-functional: although it is the usual
finite-dimensional Schatten norm for `1 <= p`, its triangle inequality is not proved here.
For `p = 1`, this file therefore proves the nuclear singular-value formula and Mirsky lower
bound, but does not overstate an unproved truncation-attainment result.
-/

public section

open InnerProductSpace Module RCLike

namespace LinearMap

variable {K E F : Type*} [RCLike K]
  [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
  [NormedAddCommGroup F] [InnerProductSpace K F] [FiniteDimensional K F]
  [CompleteSpace E] [CompleteSpace F]
  {T : E →ₗ[K] F} {n : ℕ} (hn : finrank K E = n)

/-- The `p`-th singular-value power sum.  This is defined for every natural `p`; the
associated Schatten functional below requires `0 < p`. -/
noncomputable def schattenPowerSum (T : E →ₗ[K] F) (n p : ℕ) : ℝ :=
  ∑ i : Fin n, T.singularValues i ^ p

/-- The tail of the `p`-th singular-value power sum beginning at index `k`. -/
noncomputable def schattenTailPowerSum (T : E →ₗ[K] F) (n p k : ℕ) : ℝ :=
  ∑ i : Fin n, if k ≤ (i : ℕ) then T.singularValues i ^ p else 0

/-- The finite-dimensional positive-integral Schatten functional
`(sum i, sigma_i^p)^(1/p)`.  Callers should supply `0 < p` to its theorems.

This definition is deliberately not installed as a `Norm`: the triangle inequality is not
part of the development in this file. -/
noncomputable def schattenNat (T : E →ₗ[K] F) (n p : ℕ) : ℝ :=
  (T.schattenPowerSum n p) ^ ((p : ℝ)⁻¹)

/-- The corresponding `p`-th root of a singular-value tail. -/
noncomputable def schattenTailNat (T : E →ₗ[K] F) (n p k : ℕ) : ℝ :=
  (T.schattenTailPowerSum n p k) ^ ((p : ℝ)⁻¹)

/-- The Schatten-infinity functional is the operator norm. -/
noncomputable def schattenInfinity (T : E →ₗ[K] F) : ℝ :=
  ‖T.toContinuousLinearMap‖

omit [CompleteSpace E] [CompleteSpace F] in
theorem schattenPowerSum_nonneg (T : E →ₗ[K] F) (n p : ℕ) :
    0 ≤ T.schattenPowerSum n p := by
  exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (T.singularValues_nonneg i) p

omit [CompleteSpace E] [CompleteSpace F] in
theorem schattenTailPowerSum_nonneg (T : E →ₗ[K] F) (n p k : ℕ) :
    0 ≤ T.schattenTailPowerSum n p k := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact pow_nonneg (T.singularValues_nonneg i) p
  · exact le_rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem schattenNat_nonneg (T : E →ₗ[K] F) (n p : ℕ) :
    0 ≤ T.schattenNat n p := by
  exact Real.rpow_nonneg (T.schattenPowerSum_nonneg n p) _

omit [CompleteSpace E] [CompleteSpace F] in
theorem schattenTailNat_nonneg (T : E →ₗ[K] F) (n p k : ℕ) :
    0 ≤ T.schattenTailNat n p k := by
  exact Real.rpow_nonneg (T.schattenTailPowerSum_nonneg n p k) _

omit [CompleteSpace E] [CompleteSpace F] in
/-- `p = 1` is the nuclear (trace) singular-value sum. -/
theorem schattenNat_one (T : E →ₗ[K] F) (n : ℕ) :
    T.schattenNat n 1 = ∑ i : Fin n, T.singularValues i := by
  simp [schattenNat, schattenPowerSum]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The `p = 2` power sum is exactly the existing Hilbert--Schmidt square. -/
theorem schattenPowerSum_two (hn : finrank K E = n) :
    T.schattenPowerSum n 2 = T.hilbertSchmidtNormSq hn := by
  rw [hilbertSchmidtNormSq_eq_sum_sq]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The positive-integral Schatten functional at `p = 2` is the existing
Hilbert--Schmidt norm. -/
theorem schattenNat_two (hn : finrank K E = n) :
    T.schattenNat n 2 = T.hilbertSchmidtNorm hn := by
  have hzero : T.truncation hn 0 = 0 := by
    ext x
    rw [truncation_apply]
    simp
  have h := hilbertSchmidtNorm_sub_truncation (T := T) (hn := hn) 0
  rw [hzero, sub_zero] at h
  simp only [Nat.zero_le, if_true] at h
  rw [schattenNat, schattenPowerSum, h, Real.sqrt_eq_rpow]
  norm_num

omit [FiniteDimensional K F] [CompleteSpace E] [CompleteSpace F] in
/-- `p = infinity` is definitionally the operator norm. -/
theorem schattenInfinity_eq_operatorNorm (T : E →ₗ[K] F) :
    T.schattenInfinity = ‖T.toContinuousLinearMap‖ := by
  rw [schattenInfinity]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem tailPowerSum_le_powerSum_of_weyl
    (hn : finrank K E = n) {p k : ℕ} (B : E →ₗ[K] F)
    (hB : finrank K (LinearMap.range B) ≤ k) :
    T.schattenTailPowerSum n p k ≤ (T - B).schattenPowerSum n p := by
  have hweyl : ∀ (i : Fin n), k ≤ (i : ℕ) →
      T.singularValues i ≤ (T - B).singularValues ((i : ℕ) - k) := by
    intro i hi
    exact singularValues_le_sub_of_finrank_range_le (T := T) hn B hB i.isLt hi
  have hterm : T.schattenTailPowerSum n p k ≤
      ∑ i : Fin n, if k ≤ (i : ℕ) then
        (T - B).singularValues ((i : ℕ) - k) ^ p else 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : k ≤ (i : ℕ)
    · simp only [if_pos hi]
      exact pow_le_pow_left₀ (T.singularValues_nonneg i) (hweyl i hi) p
    · simp [if_neg hi]
  have hreindex :
      (∑ i : Fin n, if k ≤ (i : ℕ) then
        (T - B).singularValues ((i : ℕ) - k) ^ p else 0) ≤
        (T - B).schattenPowerSum n p := by
    let S := Finset.filter (fun i : Fin n ↦ k ≤ (i : ℕ)) Finset.univ
    let f : Fin n → Fin n := fun i ↦
      ⟨(i : ℕ) - k, (Nat.sub_le (i : ℕ) k).trans_lt i.isLt⟩
    have hinj : Set.InjOn f (S : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      apply Fin.ext
      have hv : (a : ℕ) - k = (b : ℕ) - k := congrArg Fin.val hab
      omega
    rw [schattenPowerSum]
    have hfilter :
        (∑ i : Fin n, if k ≤ (i : ℕ) then
          (T - B).singularValues ((i : ℕ) - k) ^ p else 0) =
          ∑ i ∈ S, (T - B).singularValues ((i : ℕ) - k) ^ p := by
      simp only [S, ← Finset.sum_filter]
    have himage :
        (∑ i ∈ S, (T - B).singularValues ((i : ℕ) - k) ^ p) =
          ∑ j ∈ S.image f, (T - B).singularValues j ^ p := by
      rw [Finset.sum_image hinj]
    have hsubset :
        (∑ j ∈ S.image f, (T - B).singularValues j ^ p) ≤
          ∑ j : Fin n, (T - B).singularValues j ^ p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ pow_nonneg ((T - B).singularValues_nonneg i) p)
    calc
      (∑ i : Fin n, if k ≤ (i : ℕ) then
          (T - B).singularValues ((i : ℕ) - k) ^ p else 0)
          = ∑ i ∈ S, (T - B).singularValues ((i : ℕ) - k) ^ p := hfilter
      _ = ∑ j ∈ S.image f, (T - B).singularValues j ^ p := himage
      _ ≤ ∑ j : Fin n, (T - B).singularValues j ^ p := hsubset
  exact hterm.trans hreindex

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Integral Mirsky lower bound.** Every rank-at-most-`k` approximation has `p`-power
error at least the `p`-power tail of `T`.  The statement is useful for every positive natural
`p`; it is also algebraically true at `p = 0`. -/
theorem schattenTailPowerSum_le_sub_of_finrank_range_le
    (hn : finrank K E = n) {p k : ℕ} (B : E →ₗ[K] F)
    (hB : finrank K (LinearMap.range B) ≤ k) :
    T.schattenTailPowerSum n p k ≤ (T - B).schattenPowerSum n p := by
  exact tailPowerSum_le_powerSum_of_weyl (T := T) hn B hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rooted integral Mirsky lower bound for `0 < p`. -/
theorem schattenTailNat_le_sub_of_finrank_range_le
    (hn : finrank K E = n) {p k : ℕ} (_hp : 0 < p) (B : E →ₗ[K] F)
    (hB : finrank K (LinearMap.range B) ≤ k) :
    T.schattenTailNat n p k ≤ (T - B).schattenNat n p := by
  apply Real.rpow_le_rpow
  · exact T.schattenTailPowerSum_nonneg n p k
  · exact schattenTailPowerSum_le_sub_of_finrank_range_le (T := T) hn B hB
  · exact inv_nonneg.mpr (Nat.cast_nonneg p)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Nuclear (`p = 1`) Mirsky lower bound. -/
theorem nuclearTail_le_sub_of_finrank_range_le
    (hn : finrank K E = n) {k : ℕ} (B : E →ₗ[K] F)
    (hB : finrank K (LinearMap.range B) ≤ k) :
    (∑ i : Fin n, if k ≤ (i : ℕ) then T.singularValues i else 0) ≤
      (T - B).schattenNat n 1 := by
  simpa [schattenTailNat, schattenTailPowerSum] using
    schattenTailNat_le_sub_of_finrank_range_le (T := T) hn (p := 1) Nat.zero_lt_one B hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- Exact `p = 2` truncation tail, expressed as the Schatten-2 functional. -/
theorem schattenTwo_sub_truncation (hn : finrank K E = n) (k : ℕ) :
    (T - T.truncation hn k).schattenNat n 2 =
      Real.sqrt (T.schattenTailPowerSum n 2 k) := by
  rw [schattenNat_two (T := T - T.truncation hn k) hn,
    hilbertSchmidtNorm_sub_truncation (T := T) (hn := hn) k]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Schatten-2/Frobenius best rank-`k` approximation.** -/
theorem schattenTwo_sub_truncation_le {k : ℕ} (hn : finrank K E = n)
    (B : E →ₗ[K] F) (hB : finrank K (LinearMap.range B) ≤ k) (hk : k < n) :
    (T - T.truncation hn k).schattenNat n 2 ≤ (T - B).schattenNat n 2 := by
  rw [schattenNat_two (T := T - T.truncation hn k) hn,
    schattenNat_two (T := T - B) hn]
  exact hilbertSchmidtNorm_sub_truncation_le (T := T) (hn := hn) B hB hk

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Schatten-infinity best rank-`k` approximation.** -/
theorem schattenInfinity_sub_truncation_le {k : ℕ} (hn : finrank K E = n)
    (B : E →ₗ[K] F) (hB : finrank K (LinearMap.range B) ≤ k) (hk : k < n) :
    (T - T.truncation hn k).schattenInfinity ≤ (T - B).schattenInfinity := by
  exact norm_sub_truncation_le_of_finrank_range_le (T := T) (hn := hn) B hB hk

omit [CompleteSpace E] [CompleteSpace F] in
/-- Exact Schatten-infinity truncation error. -/
theorem schattenInfinity_sub_truncation (hn : finrank K E = n) (k : ℕ) :
    (T - T.truncation hn k).schattenInfinity = T.singularValues k := by
  exact norm_sub_truncation_eq (T := T) (hn := hn) k

end LinearMap
