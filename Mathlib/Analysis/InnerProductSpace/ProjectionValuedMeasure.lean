/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Projection-Valued Measures

A **projection-valued measure** (PVM), also called a **spectral measure**, on a
Hilbert space `H` assigns to each measurable subset of `ℝ` an orthogonal projection
on `H`, satisfying σ-additivity in the strong operator topology.

## Main definitions

* `ProjectionValuedMeasure H`: a PVM on the Hilbert space H

## References

* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.2
* Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Ch. 4
-/

noncomputable section

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projection-valued measure (spectral measure) on a Hilbert space H.

Assigns to each measurable subset B ⊆ ℝ an orthogonal projection P(B) on H,
with σ-additivity in the strong operator topology (SOT). -/
structure ProjectionValuedMeasure (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The map assigning a bounded operator to each measurable set. -/
  proj : Set ℝ → H →L[ℂ] H
  /-- Each P(B) is idempotent: P(B)² = P(B). -/
  proj_idempotent : ∀ B, proj B * proj B = proj B
  /-- Each P(B) is self-adjoint: P(B)* = P(B). -/
  proj_selfAdjoint : ∀ B, star (proj B) = proj B
  /-- P(∅) = 0. -/
  proj_empty : proj ∅ = 0
  /-- P(Set.univ) = 1. -/
  proj_univ : proj Set.univ = 1
  /-- Multiplicativity: P(A ∩ B) = P(A) * P(B). -/
  proj_inter : ∀ A B, proj (A ∩ B) = proj A * proj B
  /-- σ-additivity in SOT: for pairwise disjoint sets,
      P(⋃ₙ Aₙ) x = ∑ₙ P(Aₙ) x for all x. -/
  proj_iUnion :
    ∀ (f : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      ∀ x : H, HasSum (fun n => proj (f n) x) (proj (⋃ n, f n) x)

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure H)

/-- For disjoint sets, projections are orthogonal: P(A) * P(B) = 0. -/
theorem proj_disjoint_mul {A B : Set ℝ} (h : Disjoint A B) :
    P.proj A * P.proj B = 0 := by
  rw [← P.proj_inter A B]
  have : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp h
  rw [this, P.proj_empty]

/-- The scalar measure μ_x(B) = Re⟨x, P(B) x⟩ is real-valued and nonneg. -/
def scalarMeasure (x : H) : Set ℝ → ℝ :=
  fun B => Complex.re (@inner ℂ H _ x (P.proj B x))

/-- The scalar measure is nonneg (P(B) is a positive operator). -/
theorem scalarMeasure_nonneg (x : H) (B : Set ℝ) :
    0 ≤ P.scalarMeasure x B := by
  sorry

/-- The scalar measure of univ equals ‖x‖². -/
theorem scalarMeasure_univ (x : H) :
    P.scalarMeasure x Set.univ = ‖x‖ ^ 2 := by
  sorry

end ProjectionValuedMeasure

end
