/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.CourantFischerSingularValues
public import Mathlib.Analysis.InnerProductSpace.MatrixSVD

/-!
# Perturbation bounds for singular values

This file proves additive Weyl inequalities and the operator-norm Lipschitz continuity of each
singular value. Matrix versions follow by transport through `Matrix.toEuclideanLin`.
-/

public section

open Module

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]
  {T S : E →ₗ[𝕜] F} {n : ℕ}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Additive Weyl inequality for singular values.** The `(i+j)`th singular value of a sum is
bounded by the sum of the `i`th and `j`th singular values of the summands. -/
theorem singularValues_add_le_add (hn : finrank 𝕜 E = n) {i j : ℕ} (hij : i + j < n) :
    (T + S).singularValues (i + j) ≤ T.singularValues i + S.singularValues j := by
  let B := T.truncation hn i + S.truncation hn j
  let RT := LinearMap.range (T.truncation hn i)
  let RS := LinearMap.range (S.truncation hn j)
  have hrange : LinearMap.range B ≤ RT ⊔ RS :=
    LinearMap.range_add_le _ _
  have hTi := finrank_range_truncation_le_public hn T i
  have hSj := finrank_range_truncation_le_public hn S j
  haveI : Module.Finite 𝕜 ↥RT := inferInstance
  haveI : Module.Finite 𝕜 ↥RS := inferInstance
  haveI : Module.Finite 𝕜 ↥(RT ⊔ RS) := Submodule.finite_sup _ _
  have hB : finrank 𝕜 (LinearMap.range B) ≤ i + j := by
    calc
      finrank 𝕜 (LinearMap.range B) ≤ finrank 𝕜 ↥(RT ⊔ RS) :=
        Submodule.finrank_mono hrange
      _ ≤ finrank 𝕜 ↥RT + finrank 𝕜 ↥RS :=
        Submodule.finrank_add_le_finrank_add_finrank RT RS
      _ ≤ i + j := Nat.add_le_add hTi hSj
  have hEY := eckart_young_mirsky (T := T + S) (hn := hn) B hB hij
  have hdecomp : T + S - B =
      (T - T.truncation hn i) + (S - S.truncation hn j) := by
    dsimp [B]
    abel
  rw [hdecomp] at hEY
  calc
    (T + S).singularValues (i + j)
        ≤ ‖((T - T.truncation hn i) +
            (S - S.truncation hn j)).toContinuousLinearMap‖ := hEY
    _ ≤ ‖(T - T.truncation hn i).toContinuousLinearMap‖ +
          ‖(S - S.truncation hn j).toContinuousLinearMap‖ := by
      change ‖(T - T.truncation hn i).toContinuousLinearMap +
          (S - S.truncation hn j).toContinuousLinearMap‖ ≤ _
      exact norm_add_le _ _
    _ = T.singularValues i + S.singularValues j := by
      rw [norm_sub_truncation_eq (T := T) (hn := hn),
        norm_sub_truncation_eq (T := S) (hn := hn)]

omit [CompleteSpace E] [CompleteSpace F] in
/-- One-sided operator-norm perturbation bound for an individual singular value. -/
theorem singularValues_le_add_norm_sub (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    T.singularValues k ≤ S.singularValues k + ‖(T - S).toContinuousLinearMap‖ := by
  let B := S.truncation hn k
  have hB := finrank_range_truncation_le_public hn S k
  have hEY := eckart_young_mirsky (T := T) (hn := hn) B hB hk
  have hdecomp : T - B = (T - S) + (S - S.truncation hn k) := by
    dsimp [B]
    abel
  rw [hdecomp] at hEY
  calc
    T.singularValues k
        ≤ ‖((T - S) + (S - S.truncation hn k)).toContinuousLinearMap‖ := hEY
    _ ≤ ‖(T - S).toContinuousLinearMap‖ +
          ‖(S - S.truncation hn k).toContinuousLinearMap‖ := by
      change ‖(T - S).toContinuousLinearMap +
          (S - S.truncation hn k).toContinuousLinearMap‖ ≤ _
      exact norm_add_le _ _
    _ = S.singularValues k + ‖(T - S).toContinuousLinearMap‖ := by
      rw [norm_sub_truncation_eq (T := S) (hn := hn)]
      exact add_comm _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Singular values are 1-Lipschitz in operator norm.** -/
theorem abs_singularValues_sub_le_norm_sub (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    |T.singularValues k - S.singularValues k| ≤ ‖(T - S).toContinuousLinearMap‖ := by
  rw [abs_le]
  constructor
  · have h := singularValues_le_add_norm_sub (T := S) (S := T) hn hk
    have hnorm : ‖(S - T).toContinuousLinearMap‖ = ‖(T - S).toContinuousLinearMap‖ := by
      have heq : (S - T).toContinuousLinearMap = -(T - S).toContinuousLinearMap := by
        ext x
        simp
      rw [heq, norm_neg]
    rw [hnorm] at h
    linarith
  · have h := singularValues_le_add_norm_sub (T := T) (S := S) hn hk
    linarith

omit [CompleteSpace E] [CompleteSpace F] in
/-- Two-sided interval form of singular-value stability. -/
theorem singularValues_mem_closedInterval (hn : finrank 𝕜 E = n) {k : ℕ} (hk : k < n) :
    T.singularValues k ∈ Set.Icc
      (S.singularValues k - ‖(T - S).toContinuousLinearMap‖)
      (S.singularValues k + ‖(T - S).toContinuousLinearMap‖) := by
  have h := abs_singularValues_sub_le_norm_sub (T := T) (S := S) hn hk
  rw [abs_le] at h
  constructor <;> linarith

omit [CompleteSpace E] [CompleteSpace F] in
/-- Aggregate squared perturbation bound obtained by summing the pointwise Lipschitz estimate.
This deliberately does not claim the sharper Hoffman--Wielandt Hilbert--Schmidt bound. -/
theorem sum_sq_singularValues_sub_le_finrank_mul_norm_sub_sq
    (hn : finrank 𝕜 E = n) :
    (∑ k : Fin n, (T.singularValues k - S.singularValues k) ^ 2) ≤
      n * ‖(T - S).toContinuousLinearMap‖ ^ 2 := by
  have hterm : ∀ k : Fin n,
      (T.singularValues k - S.singularValues k) ^ 2 ≤
        ‖(T - S).toContinuousLinearMap‖ ^ 2 := by
    intro k
    have h := abs_singularValues_sub_le_norm_sub (T := T) (S := S) hn k.isLt
    have hnrm : 0 ≤ ‖(T - S).toContinuousLinearMap‖ := norm_nonneg _
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hnrm).2 h
  calc
    (∑ k : Fin n, (T.singularValues k - S.singularValues k) ^ 2)
        ≤ ∑ _k : Fin n, ‖(T - S).toContinuousLinearMap‖ ^ 2 :=
      Finset.sum_le_sum fun k _ ↦ hterm k
    _ = n * ‖(T - S).toContinuousLinearMap‖ ^ 2 := by simp

end LinearMap

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Additive Weyl inequality for matrices, stated through their Euclidean linear maps. -/
theorem singularValues_toEuclideanLin_add_le_add {A B : Matrix m n 𝕜} {i j : ℕ}
    (hij : i + j < Fintype.card n) :
    ((A + B).toEuclideanLin).singularValues (i + j) ≤
      A.toEuclideanLin.singularValues i + B.toEuclideanLin.singularValues j := by
  simpa only [map_add] using
    LinearMap.singularValues_add_le_add (T := A.toEuclideanLin) (S := B.toEuclideanLin)
      finrank_euclideanSpace hij

/-- Matrix singular values are 1-Lipschitz in the induced operator norm. -/
theorem abs_singularValues_toEuclideanLin_sub_le_norm_sub {A B : Matrix m n 𝕜} {k : ℕ}
    (hk : k < Fintype.card n) :
    |A.toEuclideanLin.singularValues k - B.toEuclideanLin.singularValues k| ≤
      ‖(A - B).toEuclideanLin.toContinuousLinearMap‖ := by
  simpa only [map_sub] using
    LinearMap.abs_singularValues_sub_le_norm_sub
      (T := A.toEuclideanLin) (S := B.toEuclideanLin) finrank_euclideanSpace hk

/-- One-sided matrix singular-value perturbation bound. -/
theorem singularValues_toEuclideanLin_le_add_norm_sub {A B : Matrix m n 𝕜} {k : ℕ}
    (hk : k < Fintype.card n) :
    A.toEuclideanLin.singularValues k ≤ B.toEuclideanLin.singularValues k +
      ‖(A - B).toEuclideanLin.toContinuousLinearMap‖ := by
  simpa only [map_sub] using
    LinearMap.singularValues_le_add_norm_sub
      (T := A.toEuclideanLin) (S := B.toEuclideanLin) finrank_euclideanSpace hk

/-- Aggregate squared singular-value stability for matrices. -/
theorem sum_sq_singularValues_toEuclideanLin_sub_le_card_mul_norm_sub_sq
    {A B : Matrix m n 𝕜} :
    (∑ k : Fin (Fintype.card n),
      (A.toEuclideanLin.singularValues k - B.toEuclideanLin.singularValues k) ^ 2) ≤
      Fintype.card n * ‖(A - B).toEuclideanLin.toContinuousLinearMap‖ ^ 2 := by
  simpa only [map_sub] using
    LinearMap.sum_sq_singularValues_sub_le_finrank_mul_norm_sub_sq
      (T := A.toEuclideanLin) (S := B.toEuclideanLin) finrank_euclideanSpace

end Matrix

#print axioms LinearMap.singularValues_add_le_add
#print axioms LinearMap.abs_singularValues_sub_le_norm_sub
#print axioms LinearMap.sum_sq_singularValues_sub_le_finrank_mul_norm_sub_sq
#print axioms Matrix.abs_singularValues_toEuclideanLin_sub_le_norm_sub
