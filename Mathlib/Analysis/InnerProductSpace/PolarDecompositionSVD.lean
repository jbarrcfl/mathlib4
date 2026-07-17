/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValueDecomposition

/-!
# Finite-dimensional polar decomposition from the singular value decomposition

This file constructs the positive factor and canonical phase of a finite-dimensional linear map
in singular coordinates.  No general operator square-root or partial-isometry API is currently
available in Mathlib, so positivity is recorded by the diagonal quadratic form and the phase is
characterized by its action on the right singular basis.
-/

public section

open InnerProductSpace Module RCLike LinearMap

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)

/-- The positive factor `|T|`, defined in right-singular coordinates as `V⁻¹ Σ V`. -/
noncomputable def polarMagnitude : E →ₗ[𝕜] E :=
  (T.rightIsometry hn).symm.toLinearEquiv.toLinearMap ∘ₗ
    (T.diagonalSingularValues ∘ₗ (T.rightIsometry hn).toLinearEquiv.toLinearMap)

/-- The canonical polar phase. It sends each right singular vector to its left singular vector. -/
noncomputable def polarFactor : E →ₗ[𝕜] F :=
  leftSingularLinearMap T hn ∘ₗ (T.rightIsometry hn).toLinearEquiv.toLinearMap

variable {T hn}

/-- `|T|` scales a right singular vector by its singular value. -/
theorem polarMagnitude_apply_rightSingularBasis (i : Fin n) :
    T.polarMagnitude hn (T.rightSingularBasis hn i) =
      (T.singularValues i : 𝕜) • T.rightSingularBasis hn i := by
  rw [polarMagnitude, comp_apply, comp_apply]
  change (T.rightIsometry hn).symm
      (T.diagonalSingularValues (T.rightIsometry hn (T.rightSingularBasis hn i))) = _
  rw [rightIsometry_apply_basis, diagonalSingularValues_single, map_smul]
  congr 1
  rw [← rightIsometry_apply_basis (T := T) (hn := hn) i]
  exact (T.rightIsometry hn).symm_apply_apply _

/-- The polar phase sends a right singular vector to the corresponding left singular vector. -/
theorem polarFactor_apply_rightSingularBasis (i : Fin n) :
    T.polarFactor hn (T.rightSingularBasis hn i) = T.leftSingularVector hn i := by
  rw [polarFactor, comp_apply]
  change leftSingularLinearMap T hn
    (T.rightIsometry hn (T.rightSingularBasis hn i)) = _
  rw [rightIsometry_apply_basis, leftSingularLinearMap_single]

/-- Every eigenvalue displayed by `|T|` on the right singular basis is nonnegative. -/
theorem polarMagnitude_eigenvalue_nonneg (i : Fin n) : 0 ≤ T.singularValues i :=
  T.singularValues_nonneg i

/-- **Polar decomposition.** `T = U |T|` for the canonical phase and positive factor. -/
theorem polar_decomposition :
    T = T.polarFactor hn ∘ₗ T.polarMagnitude hn := by
  apply (T.rightSingularBasis hn).toBasis.ext
  intro i
  change T (T.rightSingularBasis hn i) =
    (T.polarFactor hn ∘ₗ T.polarMagnitude hn) (T.rightSingularBasis hn i)
  rw [comp_apply, polarMagnitude_apply_rightSingularBasis, map_smul,
    polarFactor_apply_rightSingularBasis, image_eq_smul]

/-- The kernel of `|T|` is contained in the kernel of `T`. -/
theorem ker_polarMagnitude_le_ker : (T.polarMagnitude hn).ker ≤ T.ker := by
  intro x hx
  rw [mem_ker] at hx ⊢
  rw [polar_decomposition (T := T) (hn := hn), comp_apply, hx, map_zero]

/-- The range of `T` is contained in the range of its polar phase. -/
theorem range_le_range_polarFactor : T.range ≤ (T.polarFactor hn).range := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨T.polarMagnitude hn x, ?_⟩
  rw [← comp_apply, ← polar_decomposition (T := T) (hn := hn)]

/-- A linear map with the canonical phase's action on the right singular basis is that phase. -/
theorem polarFactor_unique {U : E →ₗ[𝕜] F}
    (hU : ∀ i : Fin n, U (T.rightSingularBasis hn i) = T.leftSingularVector hn i) :
    U = T.polarFactor hn := by
  apply (T.rightSingularBasis hn).toBasis.ext
  intro i
  change U (T.rightSingularBasis hn i) =
    T.polarFactor hn (T.rightSingularBasis hn i)
  rw [hU, polarFactor_apply_rightSingularBasis]

/-- On a zero singular direction, the singular-value-scaled phase vanishes. -/
theorem singularValue_smul_polarFactor_eq_zero {i : Fin n}
    (hi : T.singularValues i = 0) :
    (T.singularValues i : 𝕜) •
      T.polarFactor hn (T.rightSingularBasis hn i) = 0 := by
  rw [hi]
  simp

/-- The canonical phase preserves the norm of every nonzero singular basis vector. -/
theorem norm_polarFactor_rightSingularBasis {i : Fin n}
    (hi : T.singularValues i ≠ 0) :
    ‖T.polarFactor hn (T.rightSingularBasis hn i)‖ =
      ‖T.rightSingularBasis hn i‖ := by
  rw [polarFactor_apply_rightSingularBasis, norm_rightSingularBasis,
    norm_leftSingularVector (T := T) (hn := hn) hi]

end LinearMap

#print axioms LinearMap.polar_decomposition
#print axioms LinearMap.ker_polarMagnitude_le_ker
#print axioms LinearMap.polarFactor_unique
