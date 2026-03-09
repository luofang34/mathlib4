/-
Copyright (c) 2025 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Projection-Valued Measures

This file defines projection-valued measures (PVMs), also known as spectral measures,
on a Hilbert space `H` indexed by Borel sets of `ℝ`.

A projection-valued measure assigns to each Borel set `B ⊆ ℝ` an orthogonal projection `P(B)`
on `H` such that:
- `P(∅) = 0` and `P(ℝ) = 1`
- `P(A ∩ B) = P(A) * P(B)` (multiplicativity)
- For disjoint sequences, `P(⋃ₙ Bₙ) = ∑ₙ P(Bₙ)` in the strong operator topology

## Main definitions

- `ProjectionValuedMeasure H`: a projection-valued measure on `H`
- `ProjectionValuedMeasure.scalarMeasure`: the scalar measure `B ↦ ⟨x, P(B) x⟩`

## Main results

- `ProjectionValuedMeasure.proj_mul_self`: `P(B) ^ 2 = P(B)`
- `ProjectionValuedMeasure.proj_adjoint`: `adjoint P(B) = P(B)`
- `ProjectionValuedMeasure.proj_compl`: `P(Bᶜ) = 1 - P(B)`
-/

noncomputable section

open scoped ComplexInnerProductSpace
open ContinuousLinearMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projection-valued measure (spectral measure) on a Hilbert space `H`.
Each Borel set `B ⊆ ℝ` is assigned an orthogonal projection `P(B)` satisfying
σ-additivity in the strong operator topology and multiplicativity. -/
structure ProjectionValuedMeasure (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection assigned to each measurable set. -/
  proj : Set ℝ → H →L[ℂ] H
  /-- Each `proj B` is a star projection (self-adjoint idempotent). -/
  isStarProjection : ∀ B, IsStarProjection (proj B)
  /-- The projection of the empty set is zero. -/
  empty : proj ∅ = 0
  /-- The projection of the whole space is the identity. -/
  univ : proj Set.univ = 1
  /-- σ-additivity in the strong operator topology: for pairwise disjoint measurable sets,
  `P(⋃ₙ Bₙ) x = ∑ₙ P(Bₙ) x` for all `x`. -/
  countably_additive :
    ∀ (f : ℕ → Set ℝ), Pairwise (Function.onFun Disjoint f) →
      ∀ x, HasSum (fun n => proj (f n) x) (proj (⋃ n, f n) x)
  /-- Multiplicativity: `P(A ∩ B) = P(A) * P(B)`. -/
  multiplicative : ∀ A B, proj (A ∩ B) = proj A * proj B

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure H)

/-! ### Basic properties -/

theorem proj_mul_self (B : Set ℝ) : P.proj B * P.proj B = P.proj B :=
  (P.isStarProjection B).isIdempotentElem

theorem proj_adjoint (B : Set ℝ) : adjoint (P.proj B) = P.proj B :=
  (P.isStarProjection B).isSelfAdjoint

theorem proj_isSelfAdjoint (B : Set ℝ) : IsSelfAdjoint (P.proj B) :=
  (P.isStarProjection B).isSelfAdjoint

theorem proj_isIdempotentElem (B : Set ℝ) : IsIdempotentElem (P.proj B) :=
  (P.isStarProjection B).isIdempotentElem

/-! ### Set-theoretic properties -/

theorem proj_compl (B : Set ℝ) : P.proj Bᶜ = 1 - P.proj B := by
  sorry

theorem proj_union_disjoint {A B : Set ℝ} (h : Disjoint A B) :
    P.proj (A ∪ B) = P.proj A + P.proj B := by
  sorry

theorem proj_mono {A B : Set ℝ} (h : A ⊆ B) (x : H) :
    (inner (𝕜 := ℂ) x (P.proj A x)).re ≤ (inner (𝕜 := ℂ) x (P.proj B x)).re := by
  sorry

theorem proj_comm (A B : Set ℝ) : P.proj A * P.proj B = P.proj B * P.proj A := by
  have h1 := P.multiplicative A B
  have h2 := P.multiplicative B A
  rw [Set.inter_comm] at h2
  rw [← h1, h2]

/-! ### Scalar measure -/

/-- The complex scalar measure associated to vectors `x` and `y`: `B ↦ ⟪x, P(B) y⟫_ℂ`. -/
def complexScalarMeasure (x y : H) : Set ℝ → ℂ :=
  fun B => inner (𝕜 := ℂ) x (P.proj B y)

/-- The scalar measure associated to a vector `x`: `B ↦ ⟪x, P(B) x⟫_ℂ`.
This is a finite positive Borel measure on `ℝ`. -/
def scalarMeasure (x : H) : MeasureTheory.Measure ℝ :=
  sorry

theorem complexScalarMeasure_countably_additive (x y : H) (f : ℕ → Set ℝ)
    (hf : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun n => P.complexScalarMeasure x y (f n))
      (P.complexScalarMeasure x y (⋃ n, f n)) := by
  sorry

end ProjectionValuedMeasure

end
