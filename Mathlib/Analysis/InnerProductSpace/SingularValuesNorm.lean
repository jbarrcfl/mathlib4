/-
Copyright (c) 2026 Jacob Barr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Barr
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Operator norm and the top singular value

For a continuous linear map `T` between finite-dimensional inner product spaces, this file proves
that the operator norm equals the largest singular value:
`‖T‖ = (T : E →ₗ[𝕜] F).singularValues 0`, building on the singular-values API of
`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`.

The argument goes through the positive self-adjoint operator `S := T† ∘L T`:
`‖T‖² = ‖S‖` (C*-identity), `‖S‖ = λ_max(S)` (the rank-0 / top-eigenvalue case for a PSD operator,
via the spectral theorem and the Rayleigh quotient), and `σ₀² = λ_max(S)` from the definition of
singular values.

## Main statements

- `ContinuousLinearMap.norm_eq_eigenvalues_zero_of_isPositive`: `‖T‖ = λ_max(T)` for a PSD operator.
- `ContinuousLinearMap.norm_eq_singularValues_zero`: `‖T‖ = σ₀(T)`.

NOTE (pre-PR): imports are minimized (verified against Mathlib v4.31.0); the exact lemma names /
namespacing are subject to reviewer preference.
-/

public section

open InnerProductSpace Module RCLike LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 E] in
/-- For a positive (PSD) self-adjoint operator `T`, every Rayleigh quotient is `≥ 0`. -/
private theorem rayleighQuotient_nonneg (T : E →L[𝕜] E) (hpos : T.IsPositive) (x : E) :
    0 ≤ T.rayleighQuotient x := by
  rw [rayleighQuotient, reApplyInnerSelf_apply]
  exact div_nonneg (RCLike.nonneg_iff.mp (hpos.inner_nonneg_left x)).1 (by positivity)

/-- Any eigenvalue of a symmetric operator is `≤` the top (0th) eigenvalue. -/
private theorem eigenvalue_le_top [Nontrivial E] {T : E →ₗ[𝕜] E} (hsym : T.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue T (μ : 𝕜)) :
    μ ≤ hsym.eigenvalues hn ⟨0, hn0⟩ := by
  obtain ⟨i, hi⟩ := hsym.exists_eigenvalues_eq hn hμ
  have hr : hsym.eigenvalues hn i = μ := by exact_mod_cast hi
  rw [← hr]
  exact hsym.eigenvalues_antitone hn (Fin.mk_le_of_le_val (Nat.zero_le _))

omit [FiniteDimensional 𝕜 E] in
/-- The Rayleigh quotient at an eigenvector equals its (real) eigenvalue. -/
private theorem rayleighQuotient_eigenvector {T : E →L[𝕜] E} {μ : ℝ} {v : E} (hv : v ≠ 0)
    (heig : T v = (μ : 𝕜) • v) : T.rayleighQuotient v = μ := by
  rw [rayleighQuotient, reApplyInnerSelf_apply, heig, inner_smul_left, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  field_simp

/-- For a positive (PSD) self-adjoint operator `T` on a nontrivial finite-dimensional inner product
space, the operator norm equals the largest eigenvalue. (The rank-0 case of Eckart–Young.) -/
theorem norm_eq_eigenvalues_zero_of_isPositive [Nontrivial E] (T : E →L[𝕜] E) (hpos : T.IsPositive)
    {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    ‖T‖ = hpos.isSymmetric.eigenvalues hn ⟨0, hn0⟩ := by
  have hsym := hpos.isSymmetric
  set lam0 := hsym.eigenvalues hn ⟨0, hn0⟩ with hlam0
  have hbddE : BddAbove (Set.range fun x : E => T.rayleighQuotient x) := by
    obtain ⟨C, hC⟩ := T.bddAbove_rayleighQuotient
    exact ⟨C, fun y ⟨x, hx⟩ => hx ▸ ((le_abs_self _).trans (hC ⟨x, rfl⟩))⟩
  have hbddS : BddAbove (Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient x.1) := by
    obtain ⟨C, hC⟩ := T.bddAbove_rayleighQuotient
    exact ⟨C, fun y ⟨x, hx⟩ => hx ▸ ((le_abs_self _).trans (hC ⟨x.1, rfl⟩))⟩
  obtain ⟨z, hz⟩ := exists_ne (0 : E)
  haveI hne : Nonempty {x : E // x ≠ 0} := ⟨⟨z, hz⟩⟩
  have hlam0_nonneg : 0 ≤ lam0 := by
    have hv := hsym.apply_eigenvectorBasis hn ⟨0, hn0⟩
    set v := hsym.eigenvectorBasis hn ⟨0, hn0⟩ with hvdef
    have hvnorm : ‖v‖ = 1 := (hsym.eigenvectorBasis hn).orthonormal.1 _
    have hvne : v ≠ 0 := by
      intro h; rw [h, norm_zero] at hvnorm; norm_num at hvnorm
    have hray : T.rayleighQuotient v = lam0 := rayleighQuotient_eigenvector hvne hv
    rw [← hray]; exact rayleighQuotient_nonneg T hpos v
  refine le_antisymm ?_ ?_
  · rw [T.norm_eq_iSup_rayleighQuotient hsym]
    have hR_nonneg := rayleighQuotient_nonneg T hpos
    have e1 : (⨆ x, |T.rayleighQuotient x|) = ⨆ x : E, T.rayleighQuotient x := by
      congr 1; ext x; exact abs_of_nonneg (hR_nonneg x)
    have e2 : (⨆ x : E, T.rayleighQuotient x)
        = (⨆ x : {x : E // x ≠ 0}, T.rayleighQuotient x.1) := by
      apply le_antisymm
      · apply ciSup_le; intro x
        rcases eq_or_ne x 0 with rfl | hx
        · rw [rayleighQuotient_apply_zero]
          exact le_ciSup_of_le hbddS ⟨z, hz⟩ (hR_nonneg z)
        · exact le_ciSup_of_le hbddS ⟨x, hx⟩ (le_refl _)
      · apply ciSup_le; intro x
        exact le_ciSup_of_le hbddE x.1 (le_refl _)
    rw [e1, e2]
    have heig := hsym.hasEigenvalue_iSup_of_finiteDimensional
    have hform : (⨆ x : {x : E // x ≠ 0}, T.rayleighQuotient x.1)
        = (⨆ x : {x : E // x ≠ 0}, RCLike.re ⟪(T : E →ₗ[𝕜] E) ↑x, ↑x⟫_𝕜 / ‖(x : E)‖ ^ 2) := rfl
    rw [hform]
    refine eigenvalue_le_top hsym hn hn0 ?_
    exact_mod_cast heig
  · have hv := hsym.apply_eigenvectorBasis hn ⟨0, hn0⟩
    set v := hsym.eigenvectorBasis hn ⟨0, hn0⟩ with hvdef
    have hvnorm : ‖v‖ = 1 := (hsym.eigenvectorBasis hn).orthonormal.1 _
    have hvne : v ≠ 0 := by
      intro h; rw [h, norm_zero] at hvnorm; norm_num at hvnorm
    have hray : T.rayleighQuotient v = lam0 := rayleighQuotient_eigenvector hvne hv
    have hle := T.rayleighQuotient_le_norm v
    rw [hray] at hle
    exact (le_abs_self _).trans hle

variable [CompleteSpace E] [CompleteSpace F]

/-- **The operator norm equals the top singular value.**
For a continuous linear map `T` between nontrivial finite-dimensional inner product spaces,
`‖T‖ = σ₀(T)`, the largest singular value. -/
theorem norm_eq_singularValues_zero [Nontrivial E] (T : E →L[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    ‖T‖ = (T : E →ₗ[𝕜] F).singularValues 0 := by
  set S : E →L[𝕜] E := ContinuousLinearMap.adjoint T ∘L T with hS
  have hpos : S.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self T
  have hC : ‖T‖ ^ 2 = ‖S‖ := by
    rw [hS, sq]; exact (norm_adjoint_comp_self T).symm
  have hrank0 := norm_eq_eigenvalues_zero_of_isPositive S hpos hn hn0
  set TL : E →ₗ[𝕜] F := (T : E →ₗ[𝕜] F) with hTL
  have hsig : TL.singularValues 0 ^ 2
      = TL.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨0, hn0⟩ :=
    TL.sq_singularValues_of_lt hn hn0
  have heig : hpos.isSymmetric.eigenvalues hn ⟨0, hn0⟩
      = TL.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨0, hn0⟩ := by
    congr 1
  have hsq : ‖T‖ ^ 2 = TL.singularValues 0 ^ 2 := by
    rw [hC, hrank0, heig, ← hsig]
  have hT0 : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  have hσ0 : (0 : ℝ) ≤ TL.singularValues 0 := TL.singularValues_nonneg 0
  nlinarith [hsq, hT0, hσ0, sq_nonneg (‖T‖ - TL.singularValues 0),
    sq_nonneg (‖T‖ + TL.singularValues 0)]

end ContinuousLinearMap
