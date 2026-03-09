/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
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

/-- P(B) is a positive operator: ⟨x, P(B)x⟩ ≥ 0.
Proof: P = P*P, so ⟨x, Px⟩ = ⟨P†x, Px⟩ = ⟨Px, Px⟩ = ‖Px‖² ≥ 0. -/
theorem proj_isPositive (B : Set ℝ) : (P.proj B).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · -- Symmetric: ⟨Px, y⟩ = ⟨x, Py⟩ since P = P*
    have h := P.proj_selfAdjoint B
    have : IsSelfAdjoint (P.proj B) := h
    exact this.isSymmetric x y
  · -- Nonneg: re⟨Px, x⟩ ≥ 0. P = P*P so P is conj_adjoint of id.
    have h_sa := P.proj_selfAdjoint B
    rw [ContinuousLinearMap.star_eq_adjoint] at h_sa
    show 0 ≤ (P.proj B).reApplyInnerSelf x
    -- P² = P and P† = P, so Px = P†(Px) and
    -- re⟪Px, x⟫ = re⟪P†(Px), x⟫ = re⟪Px, Px⟫ = ‖Px‖² ≥ 0
    -- Use: adjoint_inner_left says re⟪T†y, x⟫ = re⟪y, Tx⟫
    have key : (P.proj B).reApplyInnerSelf x =
        RCLike.re (@inner ℂ H _ (P.proj B x) (P.proj B x)) := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      congr 1
      have h_idem := P.proj_idempotent B
      calc @inner ℂ H _ (P.proj B x) x
          = @inner ℂ H _ ((P.proj B * P.proj B) x) x := by rw [h_idem]
        _ = @inner ℂ H _ (P.proj B (P.proj B x)) x := by
            rw [ContinuousLinearMap.mul_apply]
        _ = @inner ℂ H _ (ContinuousLinearMap.adjoint (P.proj B) (P.proj B x)) x := by
            rw [h_sa]
        _ = @inner ℂ H _ (P.proj B x) (P.proj B x) := by
            rw [ContinuousLinearMap.adjoint_inner_left]
    rw [key]
    exact inner_self_nonneg

/-- The scalar measure is nonneg (P(B) is positive). -/
theorem scalarMeasure_nonneg (x : H) (B : Set ℝ) :
    0 ≤ P.scalarMeasure x B := by
  unfold scalarMeasure
  exact (proj_isPositive P B).re_inner_nonneg_right x

/-- The scalar measure of univ equals ‖x‖²: ⟨x, P(univ)x⟩ = ⟨x, x⟩ = ‖x‖². -/
theorem scalarMeasure_univ (x : H) :
    P.scalarMeasure x Set.univ = ‖x‖ ^ 2 := by
  unfold scalarMeasure
  rw [P.proj_univ, ContinuousLinearMap.one_apply]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

end ProjectionValuedMeasure

end
