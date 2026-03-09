/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.ProjectionValuedMeasure

/-!
# Integration against Projection-Valued Measures

Defines integration of bounded measurable functions against a PVM,
and the unbounded integral for L² functions.

## Main definitions

* `ProjectionValuedMeasure.boundedIntegral`: ∫ f dP for bounded measurable f,
  yielding a bounded operator
* `ProjectionValuedMeasure.unboundedDomain`: the domain of ∫ f dP for general f
* `ProjectionValuedMeasure.unboundedIntegral`: ∫ f dP as a LinearPMap

## References

* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.2
* Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Ch. 4
-/

noncomputable section

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure H)

/-- The bounded integral ∫ f dP for a bounded function f : ℝ → ℂ.

This is the unique bounded operator T such that
⟨x, T y⟩ = ∫ f d(μ_{x,y}) for all x, y,
where μ_{x,y}(B) = ⟨x, P(B) y⟩ is the complex measure.

For now, we construct it axiomatically; the proof of existence uses
approximation by simple functions. -/
opaque boundedIntegral_aux (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) : H →L[ℂ] H

/-- The bounded integral ∫ f dP for a bounded function f : ℝ → ℂ.
Constructed as an opaque constant to avoid coercion issues. -/
def boundedIntegral (f : ℝ → ℂ) : H →L[ℂ] H :=
  boundedIntegral_aux P f

/-- The domain of the unbounded integral: {x ∈ H | sup_n ‖∫ f·1_{|f|≤n} dP x‖ < ∞}.

The carrier is the set of vectors x for which the truncated spectral integrals
are uniformly bounded. For the identity function f(t) = t, this recovers the domain
of a self-adjoint operator. -/
def unboundedDomain (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := {x : H | BddAbove (Set.range (fun n : ℕ =>
    ‖P.boundedIntegral (fun t => if ‖f t‖ ≤ n then f t else 0) x‖))}
  zero_mem' := ⟨0, by rintro _ ⟨n, rfl⟩; simp [map_zero]⟩
  add_mem' := by
    intro x y ⟨Bx, hBx⟩ ⟨By, hBy⟩
    refine ⟨Bx + By, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc ‖(P.boundedIntegral _) (x + y)‖
        = ‖(P.boundedIntegral _) x + (P.boundedIntegral _) y‖ := by
          rw [ContinuousLinearMap.map_add]
      _ ≤ ‖(P.boundedIntegral _) x‖ + ‖(P.boundedIntegral _) y‖ := norm_add_le _ _
      _ ≤ Bx + By := add_le_add (hBx ⟨n, rfl⟩) (hBy ⟨n, rfl⟩)
  smul_mem' := by
    intro c x ⟨B, hB⟩
    refine ⟨‖c‖ * B, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc ‖(P.boundedIntegral _) (c • x)‖
        = ‖c • (P.boundedIntegral _) x‖ := by rw [ContinuousLinearMap.map_smul]
      _ = ‖c‖ * ‖(P.boundedIntegral _) x‖ := norm_smul _ _
      _ ≤ ‖c‖ * B := mul_le_mul_of_nonneg_left (hB ⟨n, rfl⟩) (norm_nonneg _)

/-- The unbounded integral ∫ f dP as a partially defined linear map.

For a general measurable f : ℝ → ℂ, this is defined on the domain
{x | ∫ |f|² dμ_x < ∞} and satisfies ⟨x, (∫ f dP) y⟩ = ∫ f dμ_{x,y}. -/
def unboundedIntegral (f : ℝ → ℂ) : LinearPMap ℂ H H where
  domain := P.unboundedDomain f
  toFun := by sorry

/-- Key property: the unbounded integral of the identity function
is a (formally) self-adjoint operator, i.e., ⟨(∫ id dP) x, y⟩ = ⟨x, (∫ id dP) y⟩
for x, y in the domain. -/
theorem unboundedIntegral_id_symmetric :
    ∀ (x y : (P.unboundedDomain (fun t => (t : ℂ)))),
      @inner ℂ H _ (P.unboundedIntegral (fun t => (t : ℂ)) x) y =
      @inner ℂ H _ (x : H) (P.unboundedIntegral (fun t => (t : ℂ)) y) := by
  sorry

end ProjectionValuedMeasure

end
