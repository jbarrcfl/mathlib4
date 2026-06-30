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

/-!
# Left singular vectors (Milestone M2a)

For `T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, we build the right
singular basis `v := (T† ∘ₗ T).eigenvectorBasis` and the left singular vectors
`u i := (σ i)⁻¹ • T (v i)`, and prove the orthogonality relations relating them to the
singular values `σ i = T.singularValues i`.

## Milestone M2c — isometry packaging (matrix-diagonal form)

We achieve the **matrix-diagonal form** of the singular value decomposition: the matrix of `T`
between the right singular basis `v` (domain) and the left singular vectors `u` (codomain) is
diagonal with the singular values on the diagonal,
`⟪u i, T (v j)⟫ = if i = j then σ j else 0`
(`matrixEntry_diagonal`, for nonzero singular values), and we record the existence of an
orthonormal basis of `F` extending the orthonormal left-singular family
(`exists_orthonormalBasis_extending_left`). We also package the domain side as a genuine
linear isometry `V : E ≃ₗᵢ[𝕜] (EuclideanSpace 𝕜 (Fin n))` built from the right singular basis.

## Milestone M2d — corollaries (operator norm and Eckart–Young)

(a) `norm_toContinuousLinearMap_eq_singularValues_zero`: the operator norm of `T` equals the top
singular value, re-derived (and cross-checked with M1) for the `LinearMap` packaging.

(b) `truncation T hn k`: the rank-`k` truncation `A_k x = ∑_{i < k} σ i • ⟪v i, x⟫ • u i`, and the
**upper** Eckart–Young inequality `‖(T - A_k).toContinuousLinearMap‖ ≤ T.singularValues k`.
-/

public section

open InnerProductSpace Module RCLike LinearMap

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n)

/-- The symmetric (self-adjoint) operator `S = T† ∘ₗ T`. -/
local notation "S" => (adjoint T ∘ₗ T)

/-- The orthonormal eigenbasis of `S = T† ∘ₗ T`; these are the right singular vectors. -/
noncomputable def rightSingularBasis : OrthonormalBasis (Fin n) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn

/-- The left singular vectors `u i = (σ i)⁻¹ • T (v i)`. -/
noncomputable def leftSingularVector (i : Fin n) : F :=
  (T.singularValues i : 𝕜)⁻¹ • T (T.rightSingularBasis hn i)

variable {T hn}

/-- The eigenbasis vectors are orthonormal. -/
theorem rightSingularBasis_orthonormal :
    Orthonormal 𝕜 (T.rightSingularBasis hn) :=
  (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).orthonormal

/-- Each right singular vector has unit norm. -/
theorem norm_rightSingularBasis (i : Fin n) : ‖T.rightSingularBasis hn i‖ = 1 :=
  (rightSingularBasis_orthonormal).norm_eq_one i

/-- `S` applied to the `i`-th right singular vector scales it by the eigenvalue `λ i`. -/
theorem apply_rightSingularBasis (i : Fin n) :
    S (T.rightSingularBasis hn i)
      = (T.isSymmetric_adjoint_comp_self.eigenvalues hn i : 𝕜) • T.rightSingularBasis hn i :=
  T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i

/-- **(1) inner_image.** Moving `T` across the inner product turns the image inner products into
the eigenvalue times the inner product of the eigenvectors. -/
theorem inner_image (i j : Fin n) :
    ⟪T (T.rightSingularBasis hn i), T (T.rightSingularBasis hn j)⟫_𝕜
      = (T.isSymmetric_adjoint_comp_self.eigenvalues hn i : 𝕜)
          * ⟪T.rightSingularBasis hn i, T.rightSingularBasis hn j⟫_𝕜 := by
  rw [← adjoint_inner_left]
  have : (adjoint T) (T (T.rightSingularBasis hn i)) = S (T.rightSingularBasis hn i) := rfl
  rw [this, apply_rightSingularBasis, inner_smul_left, RCLike.conj_ofReal]

/-- Corollary of (1): the images of distinct right singular vectors are orthogonal. -/
theorem inner_image_eq_zero {i j : Fin n} (hij : i ≠ j) :
    ⟪T (T.rightSingularBasis hn i), T (T.rightSingularBasis hn j)⟫_𝕜 = 0 := by
  rw [inner_image, rightSingularBasis_orthonormal.inner_eq_zero hij, mul_zero]

/-- **(2) norm_image_sq.** The squared norm of the image equals the squared singular value. -/
theorem norm_image_sq (i : Fin n) :
    ‖T (T.rightSingularBasis hn i)‖ ^ 2 = T.singularValues i ^ 2 := by
  have hr : (‖T (T.rightSingularBasis hn i)‖ ^ 2 : 𝕜)
      = ⟪T (T.rightSingularBasis hn i), T (T.rightSingularBasis hn i)⟫_𝕜 :=
    (inner_self_eq_norm_sq_to_K _).symm
  rw [inner_image, (orthonormal_iff_ite.mp rightSingularBasis_orthonormal i i),
    if_pos rfl, mul_one, ← T.sq_singularValues_fin hn i] at hr
  exact_mod_cast hr

/-- **(3) image_eq_zero_of_sv_zero.** If the singular value is zero, the image is zero. -/
theorem image_eq_zero_of_sv_zero {i : Fin n} (hσ : T.singularValues i = 0) :
    T (T.rightSingularBasis hn i) = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, norm_image_sq, hσ]; ring

/-- **(4) image_eq_smul.** `T (v i) = σ i • u i`. -/
theorem image_eq_smul (i : Fin n) :
    T (T.rightSingularBasis hn i) = (T.singularValues i : 𝕜) • T.leftSingularVector hn i := by
  rw [leftSingularVector]
  rcases eq_or_ne (T.singularValues i) 0 with hσ | hσ
  · rw [hσ, image_eq_zero_of_sv_zero hσ]; simp
  · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hσ), one_smul]

/-- **(5) orthonormal_u.** The left singular vectors with nonzero singular value are orthonormal. -/
theorem orthonormal_u {i j : Fin n} (hi : T.singularValues i ≠ 0) (hj : T.singularValues j ≠ 0) :
    ⟪T.leftSingularVector hn i, T.leftSingularVector hn j⟫_𝕜 = if i = j then 1 else 0 := by
  have hiK : (T.singularValues i : 𝕜) ≠ 0 := by exact_mod_cast hi
  have hjK : (T.singularValues j : 𝕜) ≠ 0 := by exact_mod_cast hj
  rw [leftSingularVector, leftSingularVector, inner_smul_left, inner_smul_right, inner_image,
    RCLike.conj_inv, RCLike.conj_ofReal]
  split_ifs with h
  · subst h
    rw [(orthonormal_iff_ite.mp rightSingularBasis_orthonormal i i), if_pos rfl, mul_one,
      ← T.sq_singularValues_fin hn i]
    push_cast
    field_simp
  · rw [rightSingularBasis_orthonormal.inner_eq_zero h, mul_zero, mul_zero, mul_zero]

/-- **(M2b) reconstruction.** Every vector's image under `T` is reconstructed from the singular
triples: `T x = ∑ i, (σ i) • ⟪v i, x⟫ • u i`. -/
theorem reconstruction (x : E) :
    T x = ∑ i : Fin n, (T.singularValues i : 𝕜) • (⟪T.rightSingularBasis hn i, x⟫_𝕜)
      • T.leftSingularVector hn i := by
  conv_lhs => rw [← (T.rightSingularBasis hn).sum_repr' x]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, image_eq_smul (T := T) (hn := hn) i, smul_smul, smul_smul, mul_comm]

/-! ## Milestone M2c — isometry packaging (matrix-diagonal form) -/

/-- Each left singular vector with nonzero singular value has unit norm. -/
theorem norm_leftSingularVector {i : Fin n} (hi : T.singularValues i ≠ 0) :
    ‖T.leftSingularVector hn i‖ = 1 := by
  have h := orthonormal_u (T := T) (hn := hn) hi hi
  rw [if_pos rfl] at h
  have := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (T.leftSingularVector hn i)
  rw [h] at this
  have hnn : (0 : ℝ) ≤ ‖T.leftSingularVector hn i‖ := norm_nonneg _
  have : (‖T.leftSingularVector hn i‖ : 𝕜) ^ 2 = (1 : 𝕜) := this.symm
  have hcast : ‖T.leftSingularVector hn i‖ ^ 2 = (1 : ℝ) := by exact_mod_cast this
  nlinarith [hcast, hnn, sq_nonneg (‖T.leftSingularVector hn i‖ - 1)]

/-- **(M2c-key) `matrixEntry`.** The matrix entry of `T` between the right singular basis `v`
(domain) and the left singular vectors `u` (codomain): for indices with nonzero singular value,
`⟪u i, T (v j)⟫ = if i = j then (σ j : 𝕜) else 0`. This is the diagonal form of the SVD. -/
theorem matrixEntry_diagonal {i j : Fin n}
    (hi : T.singularValues i ≠ 0) (hj : T.singularValues j ≠ 0) :
    ⟪T.leftSingularVector hn i, T (T.rightSingularBasis hn j)⟫_𝕜
      = if i = j then (T.singularValues j : 𝕜) else 0 := by
  rw [image_eq_smul (T := T) (hn := hn) j, inner_smul_right, orthonormal_u hi hj]
  split_ifs with h
  · rw [mul_one]
  · rw [mul_zero]

/-- **(M2c) off-diagonal entries vanish.** For distinct indices with nonzero singular values,
the matrix entry of `T` is zero. -/
theorem matrixEntry_offDiag {i j : Fin n} (hij : i ≠ j)
    (hi : T.singularValues i ≠ 0) (hj : T.singularValues j ≠ 0) :
    ⟪T.leftSingularVector hn i, T (T.rightSingularBasis hn j)⟫_𝕜 = 0 := by
  rw [matrixEntry_diagonal hi hj, if_neg hij]

/-- **(M2c) diagonal entries are the singular values.** The `i`-th diagonal matrix entry of `T`
is the `i`-th singular value. -/
theorem matrixEntry_diag {i : Fin n} (hi : T.singularValues i ≠ 0) :
    ⟪T.leftSingularVector hn i, T (T.rightSingularBasis hn i)⟫_𝕜
      = (T.singularValues i : 𝕜) := by
  rw [matrixEntry_diagonal hi hi, if_pos rfl]

/-- **(M2c) the left singular family is orthonormal.** Restricting to the indices with nonzero
singular value, `u` is an orthonormal family, packaged as an `Orthonormal` statement over the
subtype `{i // σ i ≠ 0}`. -/
theorem orthonormal_leftSingularVector_subtype :
    Orthonormal 𝕜 (fun i : {i : Fin n // T.singularValues i ≠ 0} =>
      T.leftSingularVector hn i.1) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  rw [orthonormal_u hi hj]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (by simpa using h)]

/-- **(M2c) extension to an orthonormal basis of `F`.** The orthonormal left-singular family
(over the nonzero-singular-value indices) extends to an orthonormal basis of the codomain `F`.
This is the existential statement that supplies the columns of the left isometry `U`. -/
theorem exists_orthonormalBasis_extending_left :
    ∃ (w : Finset F) (b : OrthonormalBasis w 𝕜 F),
      (Set.range (fun i : {i : Fin n // T.singularValues i ≠ 0} =>
        T.leftSingularVector hn i.1)) ⊆ ↑w ∧ ⇑b = ((↑) : w → F) := by
  have horth : Orthonormal 𝕜
      ((↑) : (Set.range (fun i : {i : Fin n // T.singularValues i ≠ 0} =>
        T.leftSingularVector hn i.1)) → F) := by
    rw [orthonormal_subtype_range]
    · exact orthonormal_leftSingularVector_subtype
    · exact (orthonormal_leftSingularVector_subtype).linearIndependent.injective
  obtain ⟨w, b, hsub, hb⟩ := horth.exists_orthonormalBasis_extension
  exact ⟨w, b, hsub, hb⟩

variable (T hn)

/-- **(M2c) the right isometry `V`.** The right singular basis `v` provides a linear isometry
`V : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n)` (the domain side of the SVD), namely the inverse of the
representation isometry of the orthonormal basis `v`. -/
noncomputable def rightIsometry : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  (T.rightSingularBasis hn).repr

variable {T hn}

/-- `V` sends the `i`-th right singular vector to the `i`-th standard basis vector. -/
theorem rightIsometry_apply_basis (i : Fin n) :
    T.rightIsometry hn (T.rightSingularBasis hn i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [rightIsometry, OrthonormalBasis.repr_self]

/-- **(M2c) factorization on basis vectors via `V`.** Applying `T` to `v j` and reading off the
`i`-th coordinate (inner product with `u i`) recovers the diagonal singular-value matrix. This is
the SVD factorization `T = U Σ V*` evaluated at basis vectors, in coordinate form. -/
theorem factorization_coord {i j : Fin n}
    (hi : T.singularValues i ≠ 0) (hj : T.singularValues j ≠ 0) :
    ⟪T.leftSingularVector hn i, T ((T.rightIsometry hn).symm (EuclideanSpace.single j (1 : 𝕜)))⟫_𝕜
      = if i = j then (T.singularValues j : 𝕜) else 0 := by
  have hv : (T.rightIsometry hn).symm (EuclideanSpace.single j (1 : 𝕜))
      = T.rightSingularBasis hn j := by
    rw [← rightIsometry_apply_basis (T := T) (hn := hn) j, LinearIsometryEquiv.symm_apply_apply]
  rw [hv, matrixEntry_diagonal hi hj]

/-! ## Milestone M2d — corollaries -/

/-- **(M2d a) operator norm equals the top singular value (LinearMap packaging).**
Re-derivation of `‖T‖ = σ₀(T)` for the continuous linear map underlying `T`, cross-checked
against the Milestone M1 result `ContinuousLinearMap.norm_eq_singularValues_zero`. -/
theorem norm_toContinuousLinearMap_eq_singularValues_zero [Nontrivial E] (T : E →ₗ[𝕜] F)
    {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  haveI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have h := ContinuousLinearMap.norm_eq_singularValues_zero T.toContinuousLinearMap hn hn0
  have hcoe : ((T.toContinuousLinearMap : E →L[𝕜] F) : E →ₗ[𝕜] F) = T := rfl
  rw [hcoe] at h
  exact h

variable (T hn)

/-- The summand of the SVD reconstruction at index `i`: `σ i • ⟪v i, x⟫ • u i`. -/
noncomputable def svdTerm (i : Fin n) (x : E) : F :=
  (T.singularValues i : 𝕜) • (⟪T.rightSingularBasis hn i, x⟫_𝕜) • T.leftSingularVector hn i

/-- **(M2d b) rank-`k` truncation.** `A_k x = ∑_{i < k} σ i • ⟪v i, x⟫ • u i`. -/
@[expose] noncomputable def truncation (k : ℕ) : E →ₗ[𝕜] F where
  toFun x := ∑ i : Fin n, if (i : ℕ) < k then T.svdTerm hn i x else 0
  map_add' x y := by
    simp only [svdTerm, inner_add_right, add_smul, smul_add]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  map_smul' c x := by
    simp only [svdTerm, inner_smul_right, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · rw [smul_smul, smul_smul, smul_smul]; ring_nf
    · rw [smul_zero]

variable {T hn}

@[simp] theorem truncation_apply (k : ℕ) (x : E) :
    T.truncation hn k x = ∑ i : Fin n, if (i : ℕ) < k then T.svdTerm hn i x else 0 := rfl

/-- The reconstruction sum, repackaged in terms of `svdTerm`: `T x = ∑ i, svdTerm i x`. -/
theorem reconstruction_svdTerm (x : E) : T x = ∑ i : Fin n, T.svdTerm hn i x := by
  rw [reconstruction (T := T) (hn := hn)]
  rfl

/-- **(M2d) the residual is the tail sum.** `(T - A_k) x = ∑_{i ≥ k} σ i • ⟪v i, x⟫ • u i`. -/
theorem sub_truncation_apply (k : ℕ) (x : E) :
    T x - T.truncation hn k x = ∑ i : Fin n, if k ≤ (i : ℕ) then T.svdTerm hn i x else 0 := by
  rw [reconstruction_svdTerm (T := T) (hn := hn), truncation_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : (i : ℕ) < k
  · rw [if_pos h, if_neg (by omega), sub_self]
  · rw [if_neg h, if_pos (by omega), sub_zero]

/-- **(M2d) inner product of two singular summands.** For nonequal indices the summands are
orthogonal; on the diagonal the inner product is the real number `σ i ² · ‖⟪v i, x⟫‖²`. -/
theorem inner_svdTerm (i j : Fin n) (x : E) :
    ⟪T.svdTerm hn i x, T.svdTerm hn j x⟫_𝕜
      = if i = j then ((T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜)
        else 0 := by
  rcases eq_or_ne (T.singularValues i) 0 with hi | hi
  · have hz : (T.singularValues i : 𝕜) = 0 := by exact_mod_cast hi
    rw [svdTerm, hz, zero_smul, inner_zero_left, hi]
    split_ifs <;> simp
  rcases eq_or_ne (T.singularValues j) 0 with hj | hj
  · have hz : (T.singularValues j : 𝕜) = 0 := by exact_mod_cast hj
    rw [svdTerm, svdTerm, hz, zero_smul, inner_zero_right]
    by_cases h : i = j
    · exfalso; rw [h] at hi; exact hi hj
    · rw [if_neg h]
  rw [svdTerm, svdTerm, inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
    orthonormal_u hi hj]
  split_ifs with h
  · subst h
    rw [RCLike.conj_ofReal, mul_one, RCLike.conj_mul]
    push_cast
    ring
  · simp

/-- **(M2d) masked inner product.** Inner product of two masked summands of the tail sum. -/
theorem inner_svdTerm_masked (k : ℕ) (x : E) (i j : Fin n) :
    ⟪(if k ≤ (i : ℕ) then T.svdTerm hn i x else 0),
      (if k ≤ (j : ℕ) then T.svdTerm hn j x else 0)⟫_𝕜
      = if i = j then ((if k ≤ (i : ℕ) then
          (T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2) else 0 : ℝ) : 𝕜)
        else 0 := by
  by_cases hik : k ≤ (i : ℕ)
  · by_cases hjk : k ≤ (j : ℕ)
    · rw [if_pos hik, if_pos hjk, inner_svdTerm]
      split_ifs with h
      · subst h; simp
      · rfl
    · rw [if_neg hjk, inner_zero_right]
      split_ifs with h
      · subst h; exact absurd hik hjk
      · rfl
  · rw [if_neg hik, inner_zero_left]
    split_ifs with h
    · subst h; simp
    · rfl

/-- **(M2d) Pythagoras for the tail.** The squared norm of the residual `(T - A_k) x` equals the
sum of the squared magnitudes of the discarded singular components. -/
theorem normSq_sub_truncation (k : ℕ) (x : E) :
    ‖T x - T.truncation hn k x‖ ^ 2
      = ∑ i : Fin n, if k ≤ (i : ℕ) then
          (T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2) else 0 := by
  rw [sub_truncation_apply (T := T) (hn := hn)]
  set g : Fin n → F := fun i => if k ≤ (i : ℕ) then T.svdTerm hn i x else 0 with hg
  set c : Fin n → ℝ := fun i => if k ≤ (i : ℕ) then
      (T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2) else 0 with hc
  have hgc : ∀ i j, ⟪g i, g j⟫_𝕜 = if i = j then (c i : 𝕜) else 0 := by
    intro i j; rw [hg, hc]; exact inner_svdTerm_masked k x i j
  have key : (⟪∑ i, g i, ∑ i, g i⟫_𝕜 : 𝕜) = ((∑ i, c i : ℝ) : 𝕜) := by
    rw [sum_inner]
    have hcoord : ∀ i, ⟪g i, ∑ j, g j⟫_𝕜 = (c i : 𝕜) := by
      intro i; rw [inner_sum, Finset.sum_eq_single i]
      · rw [hgc i i, if_pos rfl]
      · intro j _ hji; rw [hgc i j, if_neg (fun h => hji h.symm)]
      · intro h; exact absurd (Finset.mem_univ i) h
    simp_rw [hcoord]; push_cast; rfl
  have h2 : (‖∑ i, g i‖ : 𝕜) ^ 2 = ((∑ i, c i : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K]; exact key
  exact_mod_cast h2

/-- **(M2d) pointwise residual bound.** `‖(T - A_k) x‖ ≤ σ_k · ‖x‖`. -/
theorem norm_sub_truncation_apply_le (k : ℕ) (x : E) :
    ‖T x - T.truncation hn k x‖ ≤ T.singularValues k * ‖x‖ := by
  have hsq : ‖T x - T.truncation hn k x‖ ^ 2 ≤ (T.singularValues k * ‖x‖) ^ 2 := by
    rw [normSq_sub_truncation (T := T) (hn := hn)]
    have hsum : ∑ i : Fin n, ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 :=
      (T.rightSingularBasis hn).sum_sq_norm_inner_right x
    have hbound : (∑ i : Fin n, if k ≤ (i : ℕ) then
        (T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2) else 0)
        ≤ T.singularValues k ^ 2 * ‖x‖ ^ 2 := by
      rw [← hsum, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      by_cases hik : k ≤ (i : ℕ)
      · rw [if_pos hik]
        have hmono : T.singularValues i ≤ T.singularValues k := T.singularValues_antitone hik
        have hi2 : T.singularValues i ^ 2 ≤ T.singularValues k ^ 2 := by
          apply sq_le_sq'
          · nlinarith [T.singularValues_nonneg i, T.singularValues_nonneg k]
          · exact hmono
        nlinarith [hi2, sq_nonneg (‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖),
          norm_nonneg (⟪T.rightSingularBasis hn i, x⟫_𝕜)]
      · rw [if_neg hik]; positivity
    calc (∑ i : Fin n, if k ≤ (i : ℕ) then
          (T.singularValues i ^ 2 * ‖⟪T.rightSingularBasis hn i, x⟫_𝕜‖ ^ 2) else 0)
        ≤ T.singularValues k ^ 2 * ‖x‖ ^ 2 := hbound
      _ = (T.singularValues k * ‖x‖) ^ 2 := by ring
  have hnn : (0 : ℝ) ≤ T.singularValues k * ‖x‖ :=
    mul_nonneg (T.singularValues_nonneg k) (norm_nonneg x)
  nlinarith [hsq, norm_nonneg (T x - T.truncation hn k x), hnn,
    sq_nonneg (‖T x - T.truncation hn k x‖ - T.singularValues k * ‖x‖)]

/-- **(M2d b) Eckart–Young, upper inequality.** The operator norm of the rank-`k` truncation error
is at most the `k`-th singular value:
`‖(T - A_k).toContinuousLinearMap‖ ≤ T.singularValues k`. -/
theorem norm_sub_truncation_le (k : ℕ) :
    ‖(T - T.truncation hn k).toContinuousLinearMap‖ ≤ T.singularValues k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg k) (fun x => ?_)
  have happ : (T - T.truncation hn k).toContinuousLinearMap x = T x - T.truncation hn k x := by
    rw [LinearMap.toContinuousLinearMap]; rfl
  rw [happ]
  exact norm_sub_truncation_apply_le (T := T) (hn := hn) k x

/-- **(M2d) the residual evaluated at the `k`-th right singular vector has norm `σ_k`.**
Plugging `v_k` into `T - A_k` discards every component except the `k`-th, which survives because
`k ≤ k`; orthonormality of `v` collapses the tail sum to the single term `σ_k²`. -/
theorem normSq_sub_truncation_rightSingularBasis {k : ℕ} (hk : k < n) :
    ‖T (T.rightSingularBasis hn ⟨k, hk⟩) - T.truncation hn k (T.rightSingularBasis hn ⟨k, hk⟩)‖ ^ 2
      = T.singularValues k ^ 2 := by
  rw [normSq_sub_truncation (T := T) (hn := hn)]
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
  · rw [if_pos (le_refl k),
      (orthonormal_iff_ite.mp rightSingularBasis_orthonormal ⟨k, hk⟩ ⟨k, hk⟩), if_pos rfl]
    simp
  · intro j _ hjk
    by_cases hkj : k ≤ (j : ℕ)
    · rw [if_pos hkj,
        (orthonormal_iff_ite.mp rightSingularBasis_orthonormal j ⟨k, hk⟩),
        if_neg (fun h => hjk h)]
      simp
    · rw [if_neg hkj]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **(M2d b) Eckart–Young, lower inequality.** The `k`-th singular value is a lower bound for the
operator norm of the truncation error. The witness is the `k`-th right singular vector. -/
theorem singularValues_le_norm_sub_truncation (k : ℕ) :
    T.singularValues k ≤ ‖(T - T.truncation hn k).toContinuousLinearMap‖ := by
  by_cases hk : k < n
  · -- evaluate at the unit vector `v_k`
    set v := T.rightSingularBasis hn ⟨k, hk⟩ with hv
    have hvnorm : ‖v‖ = 1 := rightSingularBasis_orthonormal.norm_eq_one ⟨k, hk⟩
    have happ : (T - T.truncation hn k).toContinuousLinearMap v = T v - T.truncation hn k v := by
      rw [LinearMap.toContinuousLinearMap]; rfl
    have hres : ‖T v - T.truncation hn k v‖ = T.singularValues k := by
      have hsq := normSq_sub_truncation_rightSingularBasis (T := T) (hn := hn) hk
      rw [← hv] at hsq
      have hnn1 : (0 : ℝ) ≤ ‖T v - T.truncation hn k v‖ := norm_nonneg _
      have hnn2 : (0 : ℝ) ≤ T.singularValues k := T.singularValues_nonneg k
      nlinarith [hsq, hnn1, hnn2,
        sq_nonneg (‖T v - T.truncation hn k v‖ - T.singularValues k)]
    have hle := (T - T.truncation hn k).toContinuousLinearMap.le_opNorm v
    rw [happ, hres, hvnorm, mul_one] at hle
    exact hle
  · -- `k ≥ n` ⇒ `σ_k = 0`
    have : T.singularValues k = 0 := T.singularValues_of_finrank_le (by rw [hn]; omega)
    rw [this]; positivity

/-- **(M2d b) Eckart–Young identity (operator norm).** The operator norm of the rank-`k`
truncation error equals the `k`-th singular value:
`‖(T - A_k).toContinuousLinearMap‖ = T.singularValues k`. -/
theorem norm_sub_truncation_eq (k : ℕ) :
    ‖(T - T.truncation hn k).toContinuousLinearMap‖ = T.singularValues k :=
  le_antisymm (norm_sub_truncation_le (T := T) (hn := hn) k)
    (singularValues_le_norm_sub_truncation (T := T) (hn := hn) k)

end LinearMap
