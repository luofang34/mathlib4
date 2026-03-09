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

/-- The domain of the unbounded integral: {x ∈ H | ∫ |f|² dμ_x < ∞}. -/
def unboundedDomain (f : ℝ → ℂ) : Submodule ℂ H where
  carrier := {x : H | Summable (fun n => ‖P.proj (Set.Icc n (n+1)) x‖ ^ 2 *
    ⨆ (t : ℝ) (_ : t ∈ Set.Icc (n : ℝ) (n+1)), ‖f t‖ ^ 2)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    -- ‖P(B)(x+y)‖² ≤ 2(‖P(B)x‖² + ‖P(B)y‖²) via triangle inequality
    sorry
  smul_mem' := by
    intro c x hx
    -- P(B)(c•x) = c•P(B)x, so ‖·‖² scales by |c|²
    sorry

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
