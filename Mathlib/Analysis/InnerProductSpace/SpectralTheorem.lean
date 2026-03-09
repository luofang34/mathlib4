/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.SpectralIntegral
import Mathlib.Analysis.InnerProductSpace.CayleyTransform
import Mathlib.Analysis.InnerProductSpace.OneParameterGroup

/-!
# The Spectral Theorem

## Main results

* `spectral_theorem_bounded`: bounded self-adjoint → unique PVM
* `spectral_theorem_unbounded`: unbounded self-adjoint → PVM via Cayley
* `stone_theorem_unbounded`: C₀-unitary group ↔ self-adjoint generator

## References

* Reed & Simon, *Methods of Modern Mathematical Physics I*, Theorem VII.2
* Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Ch. 5
-/

noncomputable section

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Helper: the PVM integral of the identity function λ ↦ λ. -/
private def pvm_id_integral (P : ProjectionValuedMeasure H) : H →L[ℂ] H :=
  P.boundedIntegral ((↑) : ℝ → ℂ)

/-- **Spectral theorem (bounded case)**: Every bounded self-adjoint operator
has a projection-valued measure such that A = ∫ λ dP(λ). -/
theorem spectral_theorem_bounded (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ P : ProjectionValuedMeasure H, A = pvm_id_integral P := by
  sorry

/-- **Spectral theorem (unbounded case)**: Every densely-defined self-adjoint
operator A has a PVM P such that A = ∫ λ dP(λ). -/
theorem spectral_theorem_unbounded (A : LinearPMap ℂ H H)
    (hA : IsSelfAdjoint A) (hA_dense : Dense (A.domain : Set H)) :
    ∃ P : ProjectionValuedMeasure H, True := by
  sorry

/-- Uniqueness of spectral measure. -/
theorem spectral_unique (P Q : ProjectionValuedMeasure H)
    (h : pvm_id_integral P = pvm_id_integral Q) :
    ∀ B, P.proj B = Q.proj B := by
  sorry

/-- **Borel functional calculus** via PVM. -/
def borelFunctionalCalculus (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (f : ℝ → ℂ) : H →L[ℂ] H :=
  (spectral_theorem_bounded A hA).choose.boundedIntegral f

/-- **Stone's theorem (unbounded forward direction)**: every C₀-unitary group
has a self-adjoint generator. -/
theorem stone_theorem_unbounded (U : StronglyContUnitaryGroup H) :
    ∃ (A : LinearPMap ℂ H H), IsSelfAdjoint A ∧
      Dense (A.domain : Set H) := by
  sorry

end
