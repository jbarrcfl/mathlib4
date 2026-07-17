/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValueDecomposition

/-!
# Moore--Penrose pseudoinverse from the singular system

This file constructs the pseudoinverse of a finite-dimensional linear map from its singular
vectors and proves the four Penrose equations. It also derives exact-solvability, least-squares,
and minimum-norm characterizations.
-/

public section

open InnerProductSpace Module RCLike

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)

/-- The Moore--Penrose pseudoinverse, defined from the singular system by
`T⁺ y = ∑ i, σᵢ⁻¹ ⟨uᵢ, y⟩ vᵢ`. -/
noncomputable def moorePenrose : F →ₗ[𝕜] E :=
  ∑ i : Fin n, (T.singularValues i : 𝕜)⁻¹ •
    (InnerProductSpace.rankOne 𝕜 (T.rightSingularBasis hn i)
      (T.leftSingularVector hn i)).toLinearMap

variable {T hn}

@[simp]
theorem moorePenrose_apply (y : F) :
    T.moorePenrose hn y = ∑ i : Fin n,
      ((T.singularValues i : 𝕜)⁻¹ * (inner 𝕜 (T.leftSingularVector hn i) y)) •
        T.rightSingularBasis hn i := by
  simp [moorePenrose, InnerProductSpace.rankOne_apply, smul_smul]

theorem moorePenrose_apply_image_rightSingularBasis (i : Fin n) :
    T.moorePenrose hn (T (T.rightSingularBasis hn i)) =
      if T.singularValues i = 0 then 0 else T.rightSingularBasis hn i := by
  rw [image_eq_smul (T := T) (hn := hn), map_smul, moorePenrose_apply]
  by_cases hi : T.singularValues i = 0
  · simp [hi]
  · simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_eq_single i]
    · rw [orthonormal_u hi hi, if_pos rfl]
      simp [hi]
    · intro j _ hji
      by_cases hj : T.singularValues j = 0
      · simp [hj]
      · rw [orthonormal_u hj hi, if_neg hji]
        simp
    · simp

theorem comp_moorePenrose_apply (y : F) :
    (T ∘ₗ T.moorePenrose hn) y = ∑ i : Fin n,
      if T.singularValues i = 0 then 0
      else (inner 𝕜 (T.leftSingularVector hn i) y) • T.leftSingularVector hn i := by
  rw [coe_comp, Function.comp_apply, moorePenrose_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, image_eq_smul (T := T) (hn := hn) i, smul_smul]
  by_cases hi : T.singularValues i = 0
  · simp [hi]
  · have hiK : (T.singularValues i : 𝕜) ≠ 0 := by exact_mod_cast hi
    rw [if_neg hi]
    congr 1
    field_simp

theorem moorePenrose_comp_apply_rightSingularBasis (i : Fin n) :
    (T.moorePenrose hn ∘ₗ T) (T.rightSingularBasis hn i) =
      if T.singularValues i = 0 then 0 else T.rightSingularBasis hn i := by
  change T.moorePenrose hn (T (T.rightSingularBasis hn i)) = _
  exact moorePenrose_apply_image_rightSingularBasis i

theorem moorePenrose_comp_apply (x : E) :
    (T.moorePenrose hn ∘ₗ T) x = ∑ i : Fin n,
      if T.singularValues i = 0 then 0
      else (inner 𝕜 (T.rightSingularBasis hn i) x) • T.rightSingularBasis hn i := by
  conv_lhs => rw [← (T.rightSingularBasis hn).sum_repr' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, moorePenrose_comp_apply_rightSingularBasis]
  by_cases hi : T.singularValues i = 0 <;> simp [hi]

/-- First Penrose equation: `T T⁺ T = T`. -/
theorem comp_moorePenrose_comp : T ∘ₗ T.moorePenrose hn ∘ₗ T = T := by
  apply (T.rightSingularBasis hn).toBasis.ext
  intro i
  change T (T.moorePenrose hn (T (T.rightSingularBasis hn i))) =
    T (T.rightSingularBasis hn i)
  rw [moorePenrose_apply_image_rightSingularBasis]
  by_cases hi : T.singularValues i = 0
  · rw [if_pos hi, map_zero, image_eq_zero_of_sv_zero hi]
  · rw [if_neg hi]

/-- Second Penrose equation: `T⁺ T T⁺ = T⁺`. -/
theorem moorePenrose_comp_comp : T.moorePenrose hn ∘ₗ T ∘ₗ T.moorePenrose hn =
    T.moorePenrose hn := by
  ext y
  change (T.moorePenrose hn ∘ₗ T) (T.moorePenrose hn y) = T.moorePenrose hn y
  rw [moorePenrose_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, moorePenrose_comp_apply_rightSingularBasis]
  by_cases hi : T.singularValues i = 0
  · simp [hi]
  · simp [hi]

/-- The range projection `T T⁺` is symmetric. -/
theorem isSymmetric_comp_moorePenrose : (T ∘ₗ T.moorePenrose hn).IsSymmetric := by
  intro x y
  rw [comp_moorePenrose_apply, comp_moorePenrose_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : T.singularValues i = 0
  · simp [hi]
  · simp only [if_neg hi, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring

/-- The domain projection `T⁺ T` is symmetric. -/
theorem isSymmetric_moorePenrose_comp : (T.moorePenrose hn ∘ₗ T).IsSymmetric := by
  intro x y
  rw [moorePenrose_comp_apply, moorePenrose_comp_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : T.singularValues i = 0
  · simp [hi]
  · simp only [if_neg hi, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring

/-- Third Penrose equation: `(T T⁺)† = T T⁺`. -/
theorem adjoint_comp_moorePenrose : (T ∘ₗ T.moorePenrose hn).adjoint =
    T ∘ₗ T.moorePenrose hn :=
  isSymmetric_comp_moorePenrose.adjoint_eq

/-- Fourth Penrose equation: `(T⁺ T)† = T⁺ T`. -/
theorem adjoint_moorePenrose_comp : (T.moorePenrose hn ∘ₗ T).adjoint =
    T.moorePenrose hn ∘ₗ T :=
  isSymmetric_moorePenrose_comp.adjoint_eq

/-! ## Range, least-squares, and minimum-norm consequences -/

/-- `T⁺y` is an exact solution iff `y` lies in the range of `T`. -/
theorem apply_moorePenrose_eq_iff_mem_range {y : F} :
    T (T.moorePenrose hn y) = y ↔ y ∈ T.range := by
  constructor
  · intro h
    exact ⟨T.moorePenrose hn y, h⟩
  · rintro ⟨x, rfl⟩
    have h := LinearMap.congr_fun (comp_moorePenrose_comp (T := T) (hn := hn)) x
    simpa [LinearMap.comp_apply] using h

/-- The least-squares residual is orthogonal to the range of `T`. -/
theorem inner_residual_image_eq_zero (y : F) (x : E) :
    inner 𝕜 (y - T (T.moorePenrose hn y)) (T x) = 0 := by
  let Q := T ∘ₗ T.moorePenrose hn
  have hQT : Q (T x) = T x := by
    have h := LinearMap.congr_fun (comp_moorePenrose_comp (T := T) (hn := hn)) x
    simpa [Q, LinearMap.comp_apply] using h
  calc
    inner 𝕜 (y - Q y) (T x) = inner 𝕜 (y - Q y) (Q (T x)) := by rw [hQT]
    _ = inner 𝕜 (Q (y - Q y)) (T x) :=
      (isSymmetric_comp_moorePenrose (T := T) (hn := hn) _ _).symm
    _ = 0 := by
      have hQ2 : Q (Q y) = Q y := by
        change T (T.moorePenrose hn (T (T.moorePenrose hn y))) = T (T.moorePenrose hn y)
        have h := LinearMap.congr_fun (comp_moorePenrose_comp (T := T) (hn := hn))
          (T.moorePenrose hn y)
        simpa [LinearMap.comp_apply] using h
      have hz : Q (y - Q y) = 0 := by rw [map_sub, hQ2, sub_self]
      rw [hz, inner_zero_left]

/-- Pythagorean identity underlying least-squares optimality. -/
theorem norm_residual_sq_add (y : F) (x : E) :
    ‖y - T x‖ ^ 2 = ‖y - T (T.moorePenrose hn y)‖ ^ 2 +
      ‖T (T.moorePenrose hn y - x)‖ ^ 2 := by
  have horth : inner 𝕜 (y - T (T.moorePenrose hn y))
      (T (T.moorePenrose hn y - x)) = 0 :=
    inner_residual_image_eq_zero (T := T) (hn := hn) y _
  have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (y - T (T.moorePenrose hn y)) (T (T.moorePenrose hn y - x)) horth
  rw [show y - T x = (y - T (T.moorePenrose hn y)) +
    T (T.moorePenrose hn y - x) by rw [map_sub]; abel]
  simpa [pow_two] using hsum

/-- `T⁺y` minimizes the least-squares residual. -/
theorem moorePenrose_isLeastSquares (y : F) (x : E) :
    ‖y - T (T.moorePenrose hn y)‖ ≤ ‖y - T x‖ := by
  have h := norm_residual_sq_add (T := T) (hn := hn) y x
  nlinarith [sq_nonneg ‖T (T.moorePenrose hn y - x)‖,
    norm_nonneg (y - T (T.moorePenrose hn y)), norm_nonneg (y - T x)]

/-- Characterization of all least-squares minimizers: they have the same image as `T⁺y`. -/
theorem norm_residual_eq_min_iff (y : F) (x : E) :
    ‖y - T x‖ = ‖y - T (T.moorePenrose hn y)‖ ↔
      T x = T (T.moorePenrose hn y) := by
  constructor
  · intro heq
    have h := norm_residual_sq_add (T := T) (hn := hn) y x
    rw [heq] at h
    have hs : ‖T (T.moorePenrose hn y - x)‖ ^ 2 = 0 := by nlinarith
    have hz : T (T.moorePenrose hn y - x) = 0 := by
      rw [sq_eq_zero_iff, norm_eq_zero] at hs
      exact hs
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm
  · intro h
    rw [h]

/-- The pseudoinverse solution is orthogonal to the kernel. -/
theorem inner_moorePenrose_ker_eq_zero (y : F) {z : E} (hz : T z = 0) :
    inner 𝕜 (T.moorePenrose hn y) z = 0 := by
  let P := T.moorePenrose hn ∘ₗ T
  have hfix : P (T.moorePenrose hn y) = T.moorePenrose hn y := by
    have h := LinearMap.congr_fun (moorePenrose_comp_comp (T := T) (hn := hn)) y
    simpa [P, LinearMap.comp_apply] using h
  calc
    inner 𝕜 (T.moorePenrose hn y) z = inner 𝕜 (P (T.moorePenrose hn y)) z := by
      rw [hfix]
    _ = inner 𝕜 (T.moorePenrose hn y) (P z) :=
      isSymmetric_moorePenrose_comp (T := T) (hn := hn) _ _
    _ = 0 := by simp [P, LinearMap.comp_apply, hz]

/-- Pythagorean identity for every exact solution `x` of `T x = y`. -/
theorem norm_sq_eq_moorePenrose_add_ker {y : F} {x : E} (hx : T x = y) :
    ‖x‖ ^ 2 = ‖T.moorePenrose hn y‖ ^ 2 + ‖x - T.moorePenrose hn y‖ ^ 2 := by
  have hker : T (x - T.moorePenrose hn y) = 0 := by
    have hrange : y ∈ T.range := ⟨x, hx⟩
    have hsol := (apply_moorePenrose_eq_iff_mem_range (T := T) (hn := hn)).2 hrange
    rw [map_sub, hx, hsol, sub_self]
  have horth := inner_moorePenrose_ker_eq_zero (T := T) (hn := hn) y hker
  have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (T.moorePenrose hn y) (x - T.moorePenrose hn y) horth
  calc
    ‖x‖ ^ 2 = ‖T.moorePenrose hn y + (x - T.moorePenrose hn y)‖ ^ 2 := by
      congr 2
      abel
    _ = _ := by simpa [pow_two] using hsum

/-- Among exact solutions, `T⁺y` has minimum norm. -/
theorem moorePenrose_minimumNorm {y : F} {x : E} (hx : T x = y) :
    ‖T.moorePenrose hn y‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_moorePenrose_add_ker (T := T) (hn := hn) hx
  nlinarith [sq_nonneg ‖x - T.moorePenrose hn y‖,
    norm_nonneg (T.moorePenrose hn y), norm_nonneg x]

/-- The minimum-norm exact solution is unique. -/
theorem norm_eq_moorePenrose_iff {y : F} {x : E} (hx : T x = y) :
    ‖x‖ = ‖T.moorePenrose hn y‖ ↔ x = T.moorePenrose hn y := by
  constructor
  · intro heq
    have h := norm_sq_eq_moorePenrose_add_ker (T := T) (hn := hn) hx
    rw [heq] at h
    have hs : ‖x - T.moorePenrose hn y‖ ^ 2 = 0 := by nlinarith
    have hz : x - T.moorePenrose hn y = 0 := by
      rw [sq_eq_zero_iff, norm_eq_zero] at hs
      exact hs
    exact sub_eq_zero.mp hz
  · rintro rfl
    rfl

end LinearMap
