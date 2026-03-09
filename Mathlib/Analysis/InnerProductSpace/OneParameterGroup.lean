/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.CayleyTransform
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Strongly Continuous One-Parameter Unitary Groups

A **strongly continuous one-parameter unitary group** (also called a `C₀`-group or
`C₀`-unitary group) on a Hilbert space `H` is a map `U : ℝ → H →L[ℂ] H` such that:
- Each `U(t)` is unitary
- `U(s + t) = U(s) * U(t)` (group homomorphism property)
- `U(0) = 1` (follows from the above with s = t = 0)
- `t ↦ U(t) x` is continuous for each `x : H` (strong continuity)

By Stone's theorem, these are in bijection with (densely-defined) self-adjoint operators A,
via `U(t) = e^{itA}`.

## Main definitions
- `StronglyContUnitaryGroup H`: the type of C₀-unitary groups on H
- `StronglyContUnitaryGroup.toFun`: the underlying map `ℝ → H →L[ℂ] H`
- `StronglyContUnitaryGroup.isUnitary`: each `U(t)` is unitary
- `StronglyContUnitaryGroup.map_add`: group homomorphism `U(s+t) = U(s) * U(t)`
- `StronglyContUnitaryGroup.stronglyContinuous`: `t ↦ U(t) x` is continuous for each `x`

## Main results
- `StronglyContUnitaryGroup.map_zero`: `U(0) = 1`
- `StronglyContUnitaryGroup.map_neg`: `U(-t) = U(t)⁻¹ = U(t)*`
- `StronglyContUnitaryGroup.norm_apply`: `‖U(t) x‖ = ‖x‖`

## References
- Reed & Simon, "Methods of Modern Mathematical Physics", Vol. 2, §VIII.4
- Rudin, "Functional Analysis", Chapter 13
-/

noncomputable section

open ContinuousLinearMap Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Definition -/

/-- A strongly continuous one-parameter unitary group on a Hilbert space H.

Each `U(t)` is unitary, the map `t ↦ U(t)` is a group homomorphism `(ℝ, +) → unitary (H →L[ℂ] H)`,
and the orbit maps `t ↦ U(t) x` are continuous for each `x : H`. -/
structure StronglyContUnitaryGroup (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The underlying map `ℝ → H →L[ℂ] H` -/
  toFun : ℝ → H →L[ℂ] H
  /-- Each `U(t)` is unitary -/
  isUnitary : ∀ t, toFun t ∈ unitary (H →L[ℂ] H)
  /-- Group homomorphism: `U(s + t) = U(s) * U(t)` -/
  map_add : ∀ s t, toFun (s + t) = toFun s * toFun t
  /-- Strong continuity: `t ↦ U(t) x` is continuous for each `x : H` -/
  stronglyContinuous : ∀ x : H, Continuous (fun t => toFun t x)

namespace StronglyContUnitaryGroup

variable (U : StronglyContUnitaryGroup H)

/-! ### Basic properties -/

/-- `U(0) = 1`: the group homomorphism property gives `U(0) = U(0) * U(0)`,
and since `U(0)` is unitary (hence left-cancellable), we cancel to get `1 = U(0)`. -/
theorem map_zero : U.toFun 0 = 1 := by
  -- U(0) * U(0) = U(0 + 0) = U(0) = U(0) * 1
  have h : U.toFun 0 * U.toFun 0 = U.toFun 0 * 1 := by
    rw [mul_one, ← U.map_add 0 0, add_zero]
  -- Cancel U(0) on the left using the unitary (hence left-cancellable) element
  exact ((Unitary.mul_right_inj ⟨U.toFun 0, U.isUnitary 0⟩).mp h.symm).symm

/-- `U(-t) = star (U(t))`: the inverse of a unitary is its star (adjoint). -/
theorem map_neg (t : ℝ) : U.toFun (-t) = star (U.toFun t) := by
  -- We have U(t) * U(-t) = U(t + (-t)) = U(0) = 1
  have h1 : U.toFun t * U.toFun (-t) = 1 := by
    rw [← U.map_add t (-t), add_neg_cancel, U.map_zero]
  -- For a unitary element u, u * star u = 1
  -- So U(t) * U(-t) = U(t) * star(U(t)), and cancel U(t) on the left
  have h2 : U.toFun t * U.toFun (-t) = U.toFun t * star (U.toFun t) := by
    rw [h1, mul_star_self_of_mem (U.isUnitary t)]
  exact (Unitary.mul_right_inj ⟨U.toFun t, U.isUnitary t⟩).mp h2

/-- `‖U(t) x‖ = ‖x‖`: unitaries preserve norms. -/
theorem norm_apply (t : ℝ) (x : H) : ‖U.toFun t x‖ = ‖x‖ :=
  norm_map_of_mem_unitary (U.isUnitary t) x

/-- Each `U(t)` is an isometry. -/
theorem isometry (t : ℝ) : Isometry (U.toFun t) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm, ← map_sub]
  exact U.norm_apply t _

/-- The map `(t, x) ↦ U(t) x` is jointly continuous.

We decompose as `U(t) x = U(t)(x - x₀) + U(t) x₀`. The second term converges to
`U(t₀) x₀` by strong continuity; the first term has norm `‖x - x₀‖ → 0` by the
isometry property, but completing the full argument requires more care. -/
theorem continuous_apply : Continuous (fun tx : ℝ × H => U.toFun tx.1 tx.2) := by
  rw [Metric.continuous_iff]
  intro ⟨t₀, x₀⟩ ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp
    (U.stronglyContinuous x₀).continuousAt (ε / 2) (half_pos hε)
  refine ⟨min δ₁ (ε / 2), lt_min hδ₁pos (half_pos hε), fun ⟨t, x⟩ htx => ?_⟩
  rw [Prod.dist_eq] at htx
  have ht : dist t t₀ < δ₁ :=
    (max_lt_iff.mp (lt_of_lt_of_le htx (min_le_left _ _))).1
  have hx : dist x x₀ < ε / 2 :=
    (max_lt_iff.mp (lt_of_lt_of_le htx (min_le_right _ _))).2
  calc dist (U.toFun t x) (U.toFun t₀ x₀)
      ≤ dist (U.toFun t x) (U.toFun t x₀) + dist (U.toFun t x₀) (U.toFun t₀ x₀) :=
        dist_triangle _ _ _
    _ = dist x x₀ + dist (U.toFun t x₀) (U.toFun t₀ x₀) := by
        rw [(U.isometry t).dist_eq]
    _ < ε / 2 + ε / 2 := add_lt_add hx (hδ₁ ht)
    _ = ε := add_halves ε

end StronglyContUnitaryGroup

end
