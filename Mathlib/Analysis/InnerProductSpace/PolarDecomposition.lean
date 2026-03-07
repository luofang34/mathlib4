/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Partial Isometries and Polar Decomposition

This file defines partial isometries on Hilbert spaces and establishes foundational results
toward the polar decomposition theorem for bounded operators.

## Main definitions

* `ContinuousLinearMap.IsPartialIsometry`: a bounded operator that preserves norms on the
  orthogonal complement of its kernel.
* `ContinuousLinearMap.adjointMulSelf`: the positive operator `A† ∘L A`.

## Main statements

* `ContinuousLinearMap.norm_sq_eq_re_inner_adjointMulSelf`: the identity
  `‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫`.
* `ContinuousLinearMap.ker_eq_ker_adjointMulSelf`: the kernels of `A` and `A† ∘L A` coincide.
* `ContinuousLinearMap.exists_isPartialIsometry_comp_isPositive`: existence of a polar
  decomposition `A = U ∘L P` with `U` a partial isometry and `P` positive.

## Implementation notes

The operator `adjointMulSelf A` is `A† ∘L A` rather than `(A† * A)` because
`ContinuousLinearMap` uses `comp` for composition, not `Mul`.

## References

* [J.B. Conway, *A Course in Functional Analysis*][conway1990]
* [M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*][reed_simon1980]

## Tags

polar decomposition, partial isometry, positive operator
-/

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace ContinuousLinearMap

/-! ### Partial isometries -/

/-- A bounded operator is a **partial isometry** if it preserves norms on the orthogonal
complement of its kernel. -/
def IsPartialIsometry (A : E →L[𝕜] E) : Prop :=
  ∀ x : E, x ∈ (LinearMap.ker A.toLinearMap)ᗮ → ‖A x‖ = ‖x‖

omit [CompleteSpace E] in
theorem IsPartialIsometry.norm_eq {A : E →L[𝕜] E} (hA : A.IsPartialIsometry) {x : E}
    (hx : x ∈ (LinearMap.ker A.toLinearMap)ᗮ) : ‖A x‖ = ‖x‖ :=
  hA x hx

omit [CompleteSpace E] in
/-- An isometry on the whole space is a partial isometry. -/
theorem isPartialIsometry_of_norm_eq {A : E →L[𝕜] E}
    (h : ∀ x : E, ‖A x‖ = ‖x‖) : A.IsPartialIsometry :=
  fun x _ => h x

/-! ### The positive operator `A† ∘L A` -/

/-- The positive operator `A† ∘L A`. Its positive square root is the absolute value `|A|`. -/
def adjointMulSelf (A : E →L[𝕜] E) : E →L[𝕜] E :=
  (adjoint A).comp A

/-- `A† ∘L A` is a positive operator. -/
theorem isPositive_adjointMulSelf (A : E →L[𝕜] E) : (adjointMulSelf A).IsPositive :=
  isPositive_adjoint_comp_self A

/-- `A† ∘L A` is self-adjoint. -/
theorem isSelfAdjoint_adjointMulSelf (A : E →L[𝕜] E) : IsSelfAdjoint (adjointMulSelf A) :=
  (isPositive_adjointMulSelf A).isSelfAdjoint

/-! ### Key norm identity -/

/-- The identity `‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫`. -/
theorem norm_sq_eq_re_inner_adjointMulSelf (A : E →L[𝕜] E) (x : E) :
    ‖A x‖ ^ 2 = RCLike.re (@inner 𝕜 E _ (adjointMulSelf A x) x) := by
  have : ‖A x‖ ^ 2 = RCLike.re (@inner 𝕜 E _ (A x) (A x)) := by
    rw [inner_self_eq_norm_sq]
  rw [this]
  simp only [adjointMulSelf, comp_apply]
  congr 1
  exact (adjoint_inner_left A x (A x)).symm

/-- The kernels of `A` and `A† ∘L A` coincide. -/
theorem ker_eq_ker_adjointMulSelf (A : E →L[𝕜] E) :
    LinearMap.ker A.toLinearMap = LinearMap.ker (adjointMulSelf A).toLinearMap := by
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hx
    change (adjoint A).comp A x = 0
    simp only [comp_apply, hx, map_zero]
  · intro hx
    have h : ‖A x‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner_adjointMulSelf]
      have : adjointMulSelf A x = 0 := hx
      rw [this, inner_zero_left, map_zero]
    rwa [sq_eq_zero_iff, norm_eq_zero] at h

/-! ### Polar decomposition -/

/-- Auxiliary: if `P` is a positive square root of `A† ∘L A` (i.e. `P` is positive,
`P ∘L P = A† ∘L A`, and `ker P = ker A`), and `‖A x‖ = ‖P x‖` for all `x`, then
one can build the partial isometry `U` with `A = U ∘L P`.

This isolates the BLT-extension + orthogonal-complement construction from the
CFC square-root construction. -/
private theorem polar_of_sqrt (A : E →L[𝕜] E) (P : E →L[𝕜] E)
    (hP_pos : P.IsPositive)
    (_hP_sq : P.comp P = adjointMulSelf A)
    (hP_ker : LinearMap.ker P.toLinearMap = LinearMap.ker A.toLinearMap)
    (hP_norm : ∀ x, ‖A x‖ = ‖P x‖) :
    ∃ U : E →L[𝕜] E, U.IsPartialIsometry ∧
      LinearMap.ker U.toLinearMap = LinearMap.ker A.toLinearMap ∧
      A = U.comp P := by
  -- Let K = (ker A)ᗮ. Since P is self-adjoint with ker P = ker A,
  -- range(P) is dense in K. We restrict P to a map E → K, extend the
  -- isometric map Px ↦ Ax from range(P) to K by BLT, then compose
  -- with the orthogonal projection E → K.
  set K := (LinearMap.ker A.toLinearMap)ᗮ with hK_def
  haveI : CompleteSpace K := Submodule.instOrthogonalCompleteSpace _
  -- P maps into K: for y ∈ ker A = ker P, ⟪Px, y⟫ = ⟪x, Py⟫ = 0
  have hP_range_le_K : ∀ x, P x ∈ K := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← hP_ker] at hy
    have hPy : P y = 0 := LinearMap.mem_ker.mp hy
    have h1 : @inner 𝕜 E _ (P x) y = 0 := by
      have hsymm := hP_pos.isSymmetric x y
      simp only [coe_coe] at hsymm
      rw [hsymm, hPy, inner_zero_right]
    rw [← inner_conj_symm, h1, map_zero]
  -- Define e : E →ₗ[𝕜] K as the codomain-restricted P
  let e : E →ₗ[𝕜] K :=
    { toFun := fun x => ⟨P x, hP_range_le_K x⟩
      map_add' := by intros; ext; simp [map_add]
      map_smul' := by intros; ext; simp [map_smul] }
  -- ‖e x‖ = ‖P x‖
  have he_norm : ∀ x, ‖e x‖ = ‖P x‖ := fun x => rfl
  -- range(e) is dense in K because closure(range P) = (ker P†)ᗮ = K
  -- Since P is self-adjoint, P† = P, so ker P† = ker P = ker A.
  -- From `orthogonal_ker`: P.kerᗮ = P†.range.topologicalClosure,
  -- so (ker A)ᗮ = P.range.topologicalClosure.
  have he_dense : DenseRange e := by
    -- P.range is dense in K = (ker A)ᗮ as a submodule of E.
    -- From `orthogonal_ker P`: P.kerᗮ = P†.range.topologicalClosure.
    -- Since P is self-adjoint: P† = P, so P.kerᗮ = P.range.topologicalClosure.
    -- Since ker P = ker A: K = (ker A)ᗮ = P.range.topologicalClosure.
    have hP_sa : IsSelfAdjoint P := hP_pos.isSelfAdjoint
    have hP_adj : adjoint P = P := hP_sa.star_eq
    have hclosure : P.range.topologicalClosure = K := by
      have h := orthogonal_ker P
      rw [hP_adj, hP_ker] at h
      exact h.symm
    -- Now show DenseRange e, i.e., Dense (range e) in K.
    -- range e as a set in K has the property that its image under
    -- subtypeL : K → E equals P.range (intersected with K, but P.range ⊆ K).
    -- Since P.range is dense in K (as submodule of E), range e is dense in K.
    rw [DenseRange, Metric.dense_iff]
    intro ⟨y, hy⟩ ε hε
    -- y ∈ K = P.range.topologicalClosure, so ∃ z ∈ P.range with ‖z - y‖ < ε
    have hy_clos : y ∈ closure (P.range : Set E) := by
      have : y ∈ (P.range.topologicalClosure : Set E) := by
        change y ∈ P.range.topologicalClosure
        rw [hclosure]; exact hy
      rwa [Submodule.topologicalClosure_coe] at this
    obtain ⟨z, hz_mem, hz_dist⟩ := Metric.mem_closure_iff.mp hy_clos ε hε
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz_mem
    refine ⟨e x, ?_, Set.mem_range_self x⟩
    -- Need: e x ∈ Metric.ball ⟨y, hy⟩ ε, i.e., dist (e x) ⟨y, hy⟩ < ε
    simp only [Metric.mem_ball]
    -- dist in K equals dist in E (subspace metric)
    have : dist (e x) (⟨y, hy⟩ : K) = dist (P x) y := by
      simp only [dist_eq_norm]; rfl
    rw [this, dist_comm]; exact hz_dist
  -- Norm bound: ‖A x‖ ≤ 1 * ‖e x‖
  have h_bound : ∃ C, ∀ x, ‖A x‖ ≤ C * ‖e x‖ :=
    ⟨1, fun x => by rw [one_mul, hP_norm x, he_norm]⟩
  -- BLT extension: U₀ : K →L[𝕜] E with U₀(e x) = A x
  let U₀ : ↥K →L[𝕜] E := A.toLinearMap.extendOfNorm e
  have hU₀_eq : ∀ x, U₀ (e x) = A x :=
    fun x => LinearMap.extendOfNorm_eq he_dense h_bound x
  -- U₀ is isometric on K: ‖U₀ y‖ = ‖y‖ for all y : K.
  -- On range(e): ‖U₀(e x)‖ = ‖Ax‖ = ‖Px‖ = ‖e x‖.
  -- This extends to K by density and continuity.
  have hU₀_isometry : ∀ y : K, ‖U₀ y‖ = ‖(y : E)‖ := by
    -- On range(e): ‖U₀(e x)‖ = ‖Ax‖ = ‖Px‖ = ‖e x‖ = ‖(e x : E)‖.
    -- By density and continuity, this extends.
    refine he_dense.induction
      (fun y ⟨x, hx⟩ => ?_)
      (isClosed_eq U₀.continuous.norm (continuous_norm.comp K.subtypeL.continuous))
    subst hx; rw [hU₀_eq, hP_norm]; rfl
  -- Define U = U₀ ∘ orthogonalProjection K : E → K → E
  let U : E →L[𝕜] E :=
    U₀.comp (Submodule.orthogonalProjection K)
  refine ⟨U, ?_, ?_, ?_⟩
  · -- U is a partial isometry
    -- First show ker U = Kᗮ, which gives (ker U)ᗮ = K
    -- (since U₀ is isometric, U x = 0 iff proj_K x = 0 iff x ∈ Kᗮ)
    have hker_U : LinearMap.ker U.toLinearMap = Kᗮ := by
      ext x
      simp only [LinearMap.mem_ker, coe_coe]
      change U₀ (Submodule.orthogonalProjection K x) = 0 ↔ x ∈ Kᗮ
      constructor
      · intro h
        have : ‖(Submodule.orthogonalProjection K x : E)‖ = 0 := by
          rw [← hU₀_isometry, h, norm_zero]
        have : Submodule.orthogonalProjection K x = 0 :=
          Subtype.ext (norm_eq_zero.mp this)
        exact Submodule.orthogonalProjection_eq_zero_iff.mp this
      · intro h
        rw [Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
              h, map_zero]
    intro x hx
    rw [hker_U] at hx
    -- x ∈ Kᗮᗮ, and since K.HasOrthogonalProjection, Kᗮᗮ = K
    have hx_in_K : x ∈ K := by
      rwa [Submodule.orthogonal_orthogonal] at hx
    -- For x ∈ K, proj_K x = ⟨x, _⟩, so U x = U₀ ⟨x, _⟩
    change ‖U₀ (Submodule.orthogonalProjection K x)‖ = ‖x‖
    have hproj :
        (Submodule.orthogonalProjection K x : E) = x :=
      congr_arg Subtype.val
        (Submodule.orthogonalProjection_mem_subspace_eq_self
          ⟨x, hx_in_K⟩)
    rw [hU₀_isometry, hproj]
  · -- ker U = ker A
    -- Since ker A is a closed subspace, it has orthogonal projection
    haveI : (LinearMap.ker A.toLinearMap).HasOrthogonalProjection :=
      @Submodule.HasOrthogonalProjection.ofCompleteSpace 𝕜 E _ _ _
        (LinearMap.ker A.toLinearMap) inferInstance
    -- Kᗮ = (ker A)ᗮᗮ = ker A
    have hKperp : Kᗮ = LinearMap.ker A.toLinearMap := by
      rw [hK_def, Submodule.orthogonal_orthogonal]
    ext x
    simp only [LinearMap.mem_ker, coe_coe]
    constructor
    · -- U x = 0 ⟹ U₀(proj_K x) = 0 ⟹ proj_K x = 0 ⟹ x ∈ Kᗮ = ker A
      intro hUx
      have h1 : U₀ (Submodule.orthogonalProjection K x) = 0 := hUx
      have h2 : ‖(Submodule.orthogonalProjection K x : E)‖ = 0 := by
        rw [← hU₀_isometry, h1, norm_zero]
      have h3 : (Submodule.orthogonalProjection K x : E) = 0 := by
        rw [← norm_eq_zero]; exact h2
      have h4 : Submodule.orthogonalProjection K x = 0 :=
        Subtype.ext h3
      have h5 : x ∈ Kᗮ :=
        Submodule.orthogonalProjection_eq_zero_iff.mp h4
      rw [hKperp] at h5; exact LinearMap.mem_ker.mp h5
    · -- x ∈ ker A ⟹ x ∈ Kᗮ ⟹ proj_K x = 0 ⟹ U x = 0
      intro hAx
      have hx_mem : x ∈ Kᗮ := by rw [hKperp]; exact LinearMap.mem_ker.mpr hAx
      change U₀ (Submodule.orthogonalProjection K x) = 0
      rw [Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
            hx_mem, map_zero]
  · -- A = U ∘ P: suffices to check on all x.
    -- U(Px) = U₀(proj_K(Px)) = U₀(e x) = A x
    -- (since Px ∈ K, proj_K(Px) = ⟨Px, _⟩ = e x)
    ext x
    -- U(Px) = U₀(proj_K(Px)). Since Px ∈ K, proj_K(Px) = ⟨Px, _⟩ = e x.
    change A x = U₀ (Submodule.orthogonalProjection K (P x))
    have hproj : Submodule.orthogonalProjection K (P x) = e x :=
      Submodule.orthogonalProjection_mem_subspace_eq_self
        (⟨P x, hP_range_le_K x⟩ : K)
    rw [hproj, hU₀_eq]

section CFC

-- These hypotheses are satisfied when `𝕜 = ℂ` (where `E →L[ℂ] E` is a C⋆-algebra).
-- For general `RCLike 𝕜` they can be supplied by the caller.
variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
variable [StarOrderedRing (E →L[𝕜] E)]
variable [NonUnitalContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

-- This instance is needed to allow `CFC.sqrt` to work on `E →L[𝕜] E`.
-- Lean cannot automatically synthesize `IsScalarTower ℝ (E →L[𝕜] E) (E →L[𝕜] E)` due to
-- typeclass search depth limits, so we provide it explicitly via `rfl`.
private instance instIsScalarTowerCLM : IsScalarTower ℝ (E →L[𝕜] E) (E →L[𝕜] E) where
  smul_assoc r f g := Algebra.smul_mul_assoc r f g

/-- **Polar decomposition**: every bounded operator `A` on a Hilbert space decomposes as
`A = U ∘L P` where `P` is positive and `U` is a partial isometry with `ker U = ker A`.

The proof constructs `U` by defining it on `range(|A|)` via `U(|A| x) = A x`
(well-defined by `ker_eq_ker_adjointMulSelf`), extending by the BLT theorem
to the closure, and setting `U = 0` on the orthogonal complement.
-/
theorem exists_isPartialIsometry_comp_isPositive (A : E →L[𝕜] E) :
    ∃ U : E →L[𝕜] E, U.IsPartialIsometry ∧
      LinearMap.ker U.toLinearMap = LinearMap.ker A.toLinearMap ∧
      ∃ P : E →L[𝕜] E, P.IsPositive ∧ A = U.comp P := by
  -- Step 1: Construct P as the positive square root of A† ∘L A.
  -- This requires the continuous functional calculus (CFC) applied to √· on
  -- the positive operator A† ∘L A. In the complex case, `E →L[ℂ] E` is a
  -- C*-algebra and CFC applies directly. The general RCLike case follows by
  -- complexification.
  -- TODO(mathlib): formalize `IsPositive.sqrt` producing `P` with
  --   `P.IsPositive`, `P.comp P = T`, `ker P = ker T` for positive `T`.
  obtain ⟨P, hP_pos, hP_sq, hP_ker⟩ :
      ∃ P : E →L[𝕜] E, P.IsPositive ∧
        P.comp P = adjointMulSelf A ∧
        LinearMap.ker P.toLinearMap =
          LinearMap.ker A.toLinearMap := by
    -- T = A† ∘L A is positive
    set T := adjointMulSelf A with hT_def
    have hT_nonneg : 0 ≤ T := (nonneg_iff_isPositive T).mpr (isPositive_adjointMulSelf A)
    -- P = sqrt T (via the non-unital continuous functional calculus)
    refine ⟨CFC.sqrt T, ?_, ?_, ?_⟩
    · -- P.IsPositive: sqrt T ≥ 0
      exact (nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)
    · -- P.comp P = T: sqrt T * sqrt T = T
      change CFC.sqrt T * CFC.sqrt T = T
      exact CFC.sqrt_mul_sqrt_self T hT_nonneg
    · -- ker P = ker A: ker (sqrt T) = ker T = ker A
      ext x
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      constructor
      · -- sqrt T x = 0 → A x = 0
        intro hPx
        -- (sqrt T)^2 x = (sqrt T)(sqrt T x) = (sqrt T)(0) = 0
        have h2 : (CFC.sqrt T * CFC.sqrt T) x = 0 := by
          simp [mul_apply, hPx, map_zero]
        -- T x = 0
        rw [CFC.sqrt_mul_sqrt_self T hT_nonneg] at h2
        -- ‖A x‖^2 = ⟪T x, x⟫ = 0
        have h : ‖A x‖ ^ 2 = 0 := by
          have hre : ‖A x‖ ^ 2 = RCLike.re (@inner 𝕜 E _ (A x) (A x)) := by
            rw [inner_self_eq_norm_sq]
          rw [hre]
          have : @inner 𝕜 E _ (A x) (A x) = @inner 𝕜 E _ (T x) x := by
            simp only [hT_def, adjointMulSelf, comp_apply, adjoint_inner_left]
          rw [this, h2, inner_zero_left, map_zero]
        rwa [sq_eq_zero_iff, norm_eq_zero] at h
      · -- A x = 0 → sqrt T x = 0
        intro hAx
        -- T x = A†(A x) = 0
        have hTx : T x = 0 := by
          simp [hT_def, adjointMulSelf, comp_apply, hAx, map_zero]
        -- (sqrt T)^2 x = T x = 0
        have h2 : (CFC.sqrt T * CFC.sqrt T) x = 0 := by
          rw [CFC.sqrt_mul_sqrt_self T hT_nonneg]; exact hTx
        simp only [mul_apply] at h2
        -- Use positivity of sqrt T: ⟪(sqrt T)^2 x, x⟫ = ⟪sqrt T x, sqrt T x⟫
        have hP_pos : (CFC.sqrt T).IsPositive := (nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)
        have hinner : @inner 𝕜 E _ (CFC.sqrt T x) (CFC.sqrt T x) = 0 := by
          have hsymm := hP_pos.isSymmetric (CFC.sqrt T x) x
          simp only [coe_coe] at hsymm
          -- hsymm : ⟪(sqrt T)(sqrt T x), x⟫ = ⟪sqrt T x, sqrt T x⟫
          rw [← hsymm, h2, inner_zero_left]
        -- ‖sqrt T x‖^2 = ⟪sqrt T x, sqrt T x⟫ = 0
        rw [← norm_eq_zero, ← sq_eq_zero_iff, ← @inner_self_eq_norm_sq 𝕜 E]
        rw [hinner, map_zero]
  -- Step 2: Derive the key norm identity ‖A x‖ = ‖P x‖.
  have hP_norm : ∀ x, ‖A x‖ = ‖P x‖ := by
    intro x
    have h1 : ‖A x‖ ^ 2 = ‖P x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner_adjointMulSelf]
      have heq : adjointMulSelf A x = (P.comp P) x := by rw [hP_sq]
      rw [heq, comp_apply]
      have : @inner 𝕜 E _ (P (P x)) x = @inner 𝕜 E _ (P x) (P x) :=
        hP_pos.isSymmetric (P x) x
      rw [this, inner_self_eq_norm_sq]
    exact (sq_eq_sq₀ (norm_nonneg (A x)) (norm_nonneg (P x))).mp h1
  -- Step 3: Build the partial isometry U.
  obtain ⟨U, hU_pi, hU_ker, hA_eq⟩ :=
    polar_of_sqrt A P hP_pos hP_sq hP_ker hP_norm
  exact ⟨U, hU_pi, hU_ker, P, hP_pos, hA_eq⟩

end CFC

end ContinuousLinearMap

end
