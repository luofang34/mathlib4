/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.CayleyTransform
import Mathlib.Analysis.InnerProductSpace.OneParameterGroup
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# Stone's Theorem: Forward Direction (Bounded Case)

Stone's theorem establishes a bijection between:
- Strongly continuous one-parameter unitary groups `{U(t)}_{t∈ℝ}` on a Hilbert space H
- (Possibly unbounded) self-adjoint operators A on H

via `U(t) = exp(itA)`.

## Main results (bounded case)

For a bounded self-adjoint operator `a : selfAdjoint (H →L[ℂ] H)`, we construct the
strongly continuous one-parameter unitary group `U(t) = exp(I * t * A)` as a
`StronglyContUnitaryGroup`:

- `BoundedStone.realSMul`: real scalar multiplication on `selfAdjoint (H →L[ℂ] H)`
- `BoundedStone.unitaryGroupFun`: the map `t ↦ (selfAdjoint.expUnitary (realSMul t a) : H →L[ℂ] H)`
- `BoundedStone.isUnitary`: each `U(t)` is unitary (by definition of `expUnitary`)
- `BoundedStone.map_add`: group homomorphism property from `Commute.expUnitary_add`
- `BoundedStone.map_zero`: `U(0) = 1` from `selfAdjoint.expUnitary_zero`
- `BoundedStone.norm_apply`: `‖U(t) x‖ = ‖x‖` from `Unitary.norm_map`
- `BoundedStone.continuous_unitaryGroupFun`: `t ↦ U(t)` is continuous in norm
- `BoundedStone.toStronglyContUnitaryGroup`: packages everything into a `StronglyContUnitaryGroup`

## Implementation notes

We define `realSMul r a` (real scalar multiplication on `selfAdjoint A`) via the explicit subtype
construction, using the fact that if `a` is self-adjoint then so is `(r : ℂ) • a` for any `r : ℝ`
(since `star ((r : ℂ) • a) = conj (r : ℂ) • star a = (r : ℂ) • a`).

The key computation for the group homomorphism:
`U(s + t) = exp(I(s+t)A) = exp(IsA) * exp(ItA) = U(s) * U(t)`
follows from `Commute.expUnitary_add`, valid because `realSMul s a` and `realSMul t a` commute.

## References
- Reed & Simon, "Methods of Modern Mathematical Physics", Vol. 2, §VIII.4
- Rudin, "Functional Analysis", Chapter 13
-/

noncomputable section

open NormedSpace Complex selfAdjoint Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace BoundedStone

/-! ### Real scalar multiplication on selfAdjoint operators -/

/-- Real scalar multiplication on `selfAdjoint (H →L[ℂ] H)`.

For `r : ℝ` and `a : selfAdjoint (H →L[ℂ] H)`, `realSMul r a` is defined as
`⟨(r : ℂ) • a.1, _⟩`, self-adjoint because:
`star ((r : ℂ) • a.1) = conj (r : ℂ) • star a.1 = (r : ℂ) • a.1`.
-/
def realSMul (r : ℝ) (a : selfAdjoint (H →L[ℂ] H)) : selfAdjoint (H →L[ℂ] H) :=
  ⟨(r : ℂ) • a.1, by
    change star ((r : ℂ) • a.1) = (r : ℂ) • a.1
    rw [star_smul, RCLike.star_def, Complex.conj_ofReal, a.prop.star_eq]⟩

@[simp]
theorem realSMul_val (r : ℝ) (a : selfAdjoint (H →L[ℂ] H)) :
    (realSMul r a).1 = (r : ℂ) • a.1 := rfl

theorem realSMul_add (s t : ℝ) (a : selfAdjoint (H →L[ℂ] H)) :
    realSMul (s + t) a = realSMul s a + realSMul t a := by
  ext1
  simp [add_smul]

theorem realSMul_zero (a : selfAdjoint (H →L[ℂ] H)) : realSMul 0 a = 0 := by
  ext1
  simp

/-- `realSMul s a` and `realSMul t a` commute for any `s t : ℝ`.

Both are `ℂ`-scalar multiples of `a.1`, so their product commutes via `smul_mul_smul_comm`. -/
theorem realSMul_commute (s t : ℝ) (a : selfAdjoint (H →L[ℂ] H)) :
    Commute (realSMul s a).1 (realSMul t a).1 := by
  simp only [realSMul_val]
  unfold Commute SemiconjBy
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (s : ℂ) (t : ℂ)]

/-! ### Construction of the unitary group -/

/-- The unitary operator `U(t) = exp(itA)` for a bounded self-adjoint operator `a`.

The underlying CLM of `selfAdjoint.expUnitary (realSMul t a)`. -/
def unitaryGroupFun (a : selfAdjoint (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  (selfAdjoint.expUnitary (realSMul t a) : H →L[ℂ] H)

/-- Each `U(t) = exp(itA)` is unitary. -/
theorem isUnitary (a : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    unitaryGroupFun a t ∈ unitary (H →L[ℂ] H) :=
  (selfAdjoint.expUnitary (realSMul t a)).prop

/-- `U(s + t) = U(s) * U(t)`: the group homomorphism property. -/
theorem map_add (a : selfAdjoint (H →L[ℂ] H)) (s t : ℝ) :
    unitaryGroupFun a (s + t) = unitaryGroupFun a s * unitaryGroupFun a t := by
  change (selfAdjoint.expUnitary (realSMul (s + t) a) : H →L[ℂ] H) =
       (selfAdjoint.expUnitary (realSMul s a) : H →L[ℂ] H) *
       (selfAdjoint.expUnitary (realSMul t a) : H →L[ℂ] H)
  rw [show realSMul (s + t) a = realSMul s a + realSMul t a from realSMul_add s t a]
  rw [(realSMul_commute s t a).expUnitary_add]
  rfl

/-- `U(0) = 1`: at time zero, the unitary group is the identity. -/
theorem map_zero (a : selfAdjoint (H →L[ℂ] H)) : unitaryGroupFun a 0 = 1 := by
  change (selfAdjoint.expUnitary (realSMul 0 a) : H →L[ℂ] H) = 1
  rw [show realSMul 0 a = 0 from realSMul_zero a, selfAdjoint.expUnitary_zero]
  rfl

/-- `‖U(t) x‖ = ‖x‖`: unitary operators preserve norms. -/
theorem norm_apply (a : selfAdjoint (H →L[ℂ] H)) (t : ℝ) (x : H) :
    ‖unitaryGroupFun a t x‖ = ‖x‖ :=
  Unitary.norm_map ⟨unitaryGroupFun a t, isUnitary a t⟩ x

/-- The map `t ↦ realSMul t a` is continuous from `ℝ` to `selfAdjoint (H →L[ℂ] H)`. -/
theorem continuous_realSMul (a : selfAdjoint (H →L[ℂ] H)) :
    Continuous (fun t : ℝ => realSMul t a) :=
  Continuous.subtype_mk (Complex.continuous_ofReal.smul continuous_const) _

/-- The map `t ↦ selfAdjoint.expUnitary (realSMul t a)` is continuous in `unitary (H →L[ℂ] H)`. -/
theorem continuous_unitaryGroup (a : selfAdjoint (H →L[ℂ] H)) :
    Continuous (fun t : ℝ => selfAdjoint.expUnitary (realSMul t a)) :=
  selfAdjoint.continuous_expUnitary.comp (continuous_realSMul a)

/-- The map `t ↦ U(t)` is continuous from `ℝ` to `H →L[ℂ] H` (in operator norm). -/
theorem continuous_unitaryGroupFun (a : selfAdjoint (H →L[ℂ] H)) :
    Continuous (unitaryGroupFun a) :=
  continuous_induced_dom.comp (continuous_unitaryGroup a)

/-- Strong continuity: `t ↦ U(t) x` is continuous for each `x : H`. -/
theorem stronglyContinuous (a : selfAdjoint (H →L[ℂ] H)) (x : H) :
    Continuous (fun t : ℝ => unitaryGroupFun a t x) :=
  (continuous_unitaryGroupFun a).clm_apply continuous_const

/-! ### Packaging as a StronglyContUnitaryGroup -/

/-- The strongly continuous one-parameter unitary group `t ↦ exp(itA)` associated to a bounded
self-adjoint operator `a : selfAdjoint (H →L[ℂ] H)`.

This is the forward direction of Stone's theorem for bounded operators. -/
def toStronglyContUnitaryGroup (a : selfAdjoint (H →L[ℂ] H)) : StronglyContUnitaryGroup H where
  toFun := unitaryGroupFun a
  isUnitary := isUnitary a
  map_add := map_add a
  stronglyContinuous := stronglyContinuous a

/-- **Stone's Theorem (Forward Direction, Bounded Case)**:
Every bounded self-adjoint operator `a : selfAdjoint (H →L[ℂ] H)` gives rise to a
strongly continuous one-parameter unitary group `U : StronglyContUnitaryGroup H` via
`U(t) = exp(itA)`.
-/
theorem stone_forward (a : selfAdjoint (H →L[ℂ] H)) :
    ∃ U : StronglyContUnitaryGroup H,
      U.toFun = unitaryGroupFun a := ⟨toStronglyContUnitaryGroup a, rfl⟩

end BoundedStone

end
