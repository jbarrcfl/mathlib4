/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.PolarDecompositionSVD

/-!
# The partial-isometry structure of the polar factor

This file identifies the initial space of the polar factor constructed from the SVD, proves that
it is isometric there, and sharpens the kernel, range, and uniqueness statements of the polar
decomposition.
-/

public section

open InnerProductSpace Module RCLike LinearMap

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)

/-- The initial space of the SVD polar factor: the span of right singular vectors whose singular
value is nonzero. -/
noncomputable def singularSupport : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : {i : Fin n // T.singularValues i ≠ 0} =>
    T.rightSingularBasis hn i)

/-- A minimal algebraic partial-isometry predicate suitable for finite-dimensional spaces. -/
def IsPartialIsometry (U : E →ₗ[𝕜] F) (initial : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ initial, ‖U x‖ = ‖x‖

variable {T hn}

/-- The polar factor preserves inner products on generators of the singular support. -/
theorem inner_polarFactor_rightSingularBasis {i j : Fin n}
    (hi : T.singularValues i ≠ 0) (hj : T.singularValues j ≠ 0) :
    ⟪T.polarFactor hn (T.rightSingularBasis hn i),
      T.polarFactor hn (T.rightSingularBasis hn j)⟫_𝕜 =
      ⟪T.rightSingularBasis hn i, T.rightSingularBasis hn j⟫_𝕜 := by
  rw [polarFactor_apply_rightSingularBasis, polarFactor_apply_rightSingularBasis,
    orthonormal_u hi hj]
  exact (orthonormal_iff_ite.mp rightSingularBasis_orthonormal i j).symm

/-- The polar factor preserves inner products on the singular support. -/
theorem inner_polarFactor_eq {x y : E}
    (hx : x ∈ T.singularSupport hn) (hy : y ∈ T.singularSupport hn) :
    ⟪T.polarFactor hn x, T.polarFactor hn y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j, rfl⟩ := hz
          exact inner_polarFactor_rightSingularBasis i.property j.property
      | zero => simp
      | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz]
      | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]

/-- The canonical polar factor is a partial isometry with initial space `singularSupport`. -/
theorem polarFactor_isPartialIsometry :
    IsPartialIsometry (T.polarFactor hn) (T.singularSupport hn) := by
  intro x hx
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hinner := inner_polarFactor_eq (T := T) (hn := hn) hx hx
  have hsq : (‖T.polarFactor hn x‖ ^ 2 : 𝕜) = (‖x‖ ^ 2 : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K, hinner]
  exact_mod_cast hsq

/-- A vector in the kernel is orthogonal to every nonzero right singular direction. -/
theorem inner_rightSingularBasis_eq_zero_of_mem_ker {x : E} (hx : x ∈ T.ker)
    {i : Fin n} (hi : T.singularValues i ≠ 0) :
    ⟪T.rightSingularBasis hn i, x⟫_𝕜 = 0 := by
  rw [mem_ker] at hx
  have h : ⟪T (T.rightSingularBasis hn i), T x⟫_𝕜 = 0 := by rw [hx, inner_zero_right]
  rw [← adjoint_inner_left] at h
  have hS : (adjoint T) (T (T.rightSingularBasis hn i)) =
      (T.isSymmetric_adjoint_comp_self.eigenvalues hn i : 𝕜) •
        T.rightSingularBasis hn i := apply_rightSingularBasis (T := T) (hn := hn) i
  rw [hS, inner_smul_left, RCLike.conj_ofReal,
    ← sq_singularValues_fin (T := T) hn i] at h
  have hσ : ((T.singularValues i ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 hi
  exact (mul_eq_zero.mp h).resolve_left hσ

/-- The kernel of `T` is the orthogonal complement of its singular support. -/
theorem ker_eq_orthogonal_singularSupport : T.ker = (T.singularSupport hn)ᗮ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_orthogonal']
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact (inner_eq_zero_symm.mpr
          (inner_rightSingularBasis_eq_zero_of_mem_ker hx i.property))
    | zero => simp
    | add y z _ _ hy hz => simp only [inner_add_right, hy, hz, add_zero]
    | smul c y _ hy => simp only [inner_smul_right, hy, mul_zero]
  · intro x hx
    rw [mem_ker]
    rw [reconstruction (T := T) (hn := hn) x]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : T.singularValues i = 0
    · simp [hi]
    · have hs : T.rightSingularBasis hn i ∈ T.singularSupport hn :=
        Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      have hinner := (Submodule.mem_orthogonal' _ _).mp hx _ hs
      rw [inner_eq_zero_symm] at hinner
      simp [hinner]

/-- Coordinate expansion of the positive polar magnitude in the right singular basis. -/
theorem polarMagnitude_apply_eq_sum (x : E) :
    T.polarMagnitude hn x = ∑ i : Fin n,
      ((T.singularValues i : 𝕜) * ⟪T.rightSingularBasis hn i, x⟫_𝕜) •
        T.rightSingularBasis hn i := by
  conv_lhs => rw [← (T.rightSingularBasis hn).sum_repr' x]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, polarMagnitude_apply_rightSingularBasis, smul_smul]
  congr 1
  exact mul_comm _ _

/-- The positive polar magnitude has exactly the same kernel as `T`. -/
theorem ker_polarMagnitude_eq_ker : (T.polarMagnitude hn).ker = T.ker := by
  apply le_antisymm
  · exact ker_polarMagnitude_le_ker
  · intro x hx
    rw [mem_ker, polarMagnitude_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : T.singularValues i = 0
    · simp [hi]
    · rw [inner_rightSingularBasis_eq_zero_of_mem_ker hx hi]
      simp

/-- The singular support is the orthogonal complement of the kernel of `T`. -/
theorem singularSupport_eq_orthogonal_ker : T.singularSupport hn = T.kerᗮ := by
  rw [ker_eq_orthogonal_singularSupport (T := T) (hn := hn)]
  exact (T.singularSupport hn).orthogonal_orthogonal.symm

/-- The polar factor is isometric on `ker Tᗮ`, the usual initial space of a partial isometry. -/
theorem norm_polarFactor_of_mem_orthogonal_ker {x : E} (hx : x ∈ T.kerᗮ) :
    ‖T.polarFactor hn x‖ = ‖x‖ := by
  apply polarFactor_isPartialIsometry
  rwa [singularSupport_eq_orthogonal_ker]

/-- The image of the positive polar magnitude lies in the singular support. -/
theorem polarMagnitude_mem_singularSupport (x : E) :
    T.polarMagnitude hn x ∈ T.singularSupport hn := by
  rw [polarMagnitude_apply_eq_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : T.singularValues i = 0
  · simp [hi]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)

/-- The image of the singular support under the phase is exactly the range of `T`. -/
theorem map_singularSupport_polarFactor_eq_range :
    (T.singularSupport hn).map (T.polarFactor hn) = T.range := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine ⟨((T.singularValues i : 𝕜)⁻¹ • T.rightSingularBasis hn i), ?_⟩
        rw [map_smul, image_eq_smul, polarFactor_apply_rightSingularBasis,
          smul_smul, inv_mul_cancel₀ (by exact_mod_cast i.property), one_smul]
    | zero => simpa only [map_zero] using T.range.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using T.range.add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using T.range.smul_mem c hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨T.polarMagnitude hn x, polarMagnitude_mem_singularSupport x, ?_⟩
    rw [← comp_apply, ← polar_decomposition (T := T) (hn := hn)]

/-- Uniqueness of the polar phase from the factorization once its behavior on the kernel is fixed.
Equivalently, the factorization determines the phase on `ker Tᗮ`; only its kernel action can
vary. -/
theorem polarFactor_unique_of_comp_polarMagnitude {U : E →ₗ[𝕜] F}
    (hcomp : T = U ∘ₗ T.polarMagnitude hn)
    (hker : ∀ x ∈ T.ker, U x = T.polarFactor hn x) :
    U = T.polarFactor hn := by
  apply (T.rightSingularBasis hn).toBasis.ext
  intro i
  change U (T.rightSingularBasis hn i) =
    T.polarFactor hn (T.rightSingularBasis hn i)
  by_cases hi : T.singularValues i = 0
  · apply hker
    rw [mem_ker, image_eq_zero_of_sv_zero hi]
  · have hU := LinearMap.congr_fun hcomp (T.rightSingularBasis hn i)
    rw [comp_apply, polarMagnitude_apply_rightSingularBasis, map_smul,
      image_eq_smul] at hU
    rw [polarFactor_apply_rightSingularBasis]
    have hσ : (T.singularValues i : 𝕜) ≠ 0 := by exact_mod_cast hi
    have := congrArg (fun z : F => (T.singularValues i : 𝕜)⁻¹ • z) hU.symm
    simpa only [smul_smul, inv_mul_cancel₀ hσ, one_smul] using this

#print axioms LinearMap.ker_polarMagnitude_eq_ker
#print axioms LinearMap.polarFactor_isPartialIsometry
#print axioms LinearMap.map_singularSupport_polarFactor_eq_range
#print axioms LinearMap.polarFactor_unique_of_comp_polarMagnitude

end LinearMap
