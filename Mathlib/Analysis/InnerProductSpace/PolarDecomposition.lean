/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

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

theorem IsPartialIsometry.norm_eq {A : E →L[𝕜] E} (hA : A.IsPartialIsometry) {x : E}
    (hx : x ∈ (LinearMap.ker A.toLinearMap)ᗮ) : ‖A x‖ = ‖x‖ :=
  hA x hx

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
    show (adjoint A).comp A x = 0
    simp only [comp_apply, hx, map_zero]
  · intro hx
    have h : ‖A x‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner_adjointMulSelf]
      have : adjointMulSelf A x = 0 := hx
      rw [this, inner_zero_left, map_zero]
    rwa [sq_eq_zero_iff, norm_eq_zero] at h

/-! ### Polar decomposition -/

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
  sorry

end ContinuousLinearMap

end
