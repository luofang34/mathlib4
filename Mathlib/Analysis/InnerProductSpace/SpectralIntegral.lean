/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.ProjectionValuedMeasure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration against Projection-Valued Measures

Defines integration of bounded measurable functions against a PVM,
and the unbounded integral for L² functions.

## Main definitions

* `ProjectionValuedMeasure.scalarBorelMeasure`: the positive Borel measure
  `μ_x(B) = ‖P(B)x‖²` associated to each `x : H`
* `ProjectionValuedMeasure.boundedIntegral`: `∫ f dP` for bounded measurable `f`,
  yielding a bounded operator, axiomatized below and constructed via a concrete
  sesquilinear form + Riesz representation approach.
* `ProjectionValuedMeasure.unboundedDomain`: the domain of `∫ f dP` for general `f`
* `ProjectionValuedMeasure.unboundedIntegral`: `∫ f dP` as a `LinearPMap`

## Properties

The bounded integral satisfies the following properties (sorry'd pending
full construction via sesquilinear form and Riesz representation):

* `boundedIntegral_add`: linearity in f (addition)
* `boundedIntegral_smul`: linearity in f (scalar multiplication)
* `boundedIntegral_zero`: integral of zero function is zero
* `boundedIntegral_star`: *-homomorphism property: (∫ f dP)† = ∫ f̄ dP
* `boundedIntegral_mul`: multiplicativity: (∫ f dP)(∫ g dP) = ∫ fg dP
* `boundedIntegral_char`: integral of indicator = projection

## Construction

For each `x : H`, the map `B ↦ ‖P(B) x‖²` defines a positive Borel measure
`scalarBorelMeasure P x` with total mass `‖x‖²`. This follows from the Parseval-type
identity for PVMs (orthogonality of projections for disjoint sets).

The bounded integral `∫ f dP` is the unique bounded operator `T` satisfying
`‖T x‖² = ∫ |f|² d(scalarBorelMeasure P x)` for all `x : H`,
constructed via the sesquilinear form `(x, y) ↦ ∫ f d(polarization of scalarMeasures)`.

## References

* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.2
* Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Ch. 4
-/

noncomputable section

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjectionValuedMeasure

/-! ### The scalar Borel measure μ_x associated to the PVM -/

private theorem norm_sq_sum_of_orthogonal (s : Finset ℕ) (v : ℕ → H)
    (h_orth : ∀ i j, i ≠ j → @inner ℂ H _ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    have hz : @inner ℂ H _ (v a) (∑ x ∈ s, v x) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact h_orth a i (ne_of_mem_of_not_mem hi has).symm
    have step_eq : ‖v a + ∑ x ∈ s, v x‖ * ‖v a + ∑ x ∈ s, v x‖ = ‖v a‖ * ‖v a‖ + ‖∑ i ∈ s, v i‖ * ‖∑ i ∈ s, v i‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (v a) _ hz
    simp_rw [sq]
    rw [step_eq]

private theorem hasSum_norm_sq_of_orthogonal_hasSum (v : ℕ → H) (L : H)
    (h_sum : HasSum v L)
    (h_orth : ∀ i j, i ≠ j → @inner ℂ H _ (v i) (v j) = 0) :
    HasSum (fun n => ‖v n‖ ^ 2) (‖L‖ ^ 2) := by
  have h1 : Filter.Tendsto (fun s : Finset ℕ => ∑ i ∈ s, v i) Filter.atTop (nhds L) := h_sum
  have h2 : Filter.Tendsto (fun s : Finset ℕ => ‖∑ i ∈ s, v i‖ ^ 2) Filter.atTop (nhds (‖L‖ ^ 2)) :=
    (Filter.Tendsto.norm h1).pow 2
  have h3 : ∀ s : Finset ℕ, ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := fun s =>
    norm_sq_sum_of_orthogonal s v h_orth
  exact h2.congr h3

/-- For pairwise-disjoint measurable sets, the projections P(Bᵢ) are orthogonal, so
`‖∑ P(Bᵢ) x‖² = ∑ ‖P(Bᵢ) x‖²`. This is the Parseval identity for PVMs. -/
private theorem pvm_parseval (P : ProjectionValuedMeasure H) (f : ℕ → Set ℝ)
    (h_disj : ∀ i j, i ≠ j → Disjoint (f i) (f j)) (x : H) :
    HasSum (fun n => ‖P.proj (f n) x‖ ^ 2) (‖P.proj (⋃ n, f n) x‖ ^ 2) := by
  -- The PVM axiom gives σ-additivity in H: HasSum (fun n => P.proj (f n) x) (P.proj (⋃ n, f n) x)
  have hsum : HasSum (fun n => P.proj (f n) x) (P.proj (⋃ n, f n) x) :=
    P.proj_iUnion f h_disj x
  -- For i ≠ j, P(f i) * P(f j) = P(f i ∩ f j) = P(∅) = 0, so projections are orthogonal.
  have h_orth : ∀ i j, i ≠ j → @inner ℂ H _ (P.proj (f i) x) (P.proj (f j) x) = 0 := by
    intro i j hij
    have hmul : P.proj (f i) * P.proj (f j) = 0 := by
      rw [← P.proj_inter (f i) (f j),
          Set.disjoint_iff_inter_eq_empty.mp (h_disj i j hij), P.proj_empty]
    -- ⟨P(fi)x, P(fj)x⟩ = ⟨P(fi)x, P(fi)P(fj)x⟩ = ⟨P(fi)x, 0⟩ = 0
    -- Using: P(fi)† = P(fi), so ⟨P(fi)x, vy⟩ = ⟨x, P(fi)vy⟩
    have : @inner ℂ H _ (P.proj (f i) x) (P.proj (f j) x) =
        @inner ℂ H _ x ((P.proj (f i) * P.proj (f j)) x) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
          P.proj_selfAdjoint (f i), ← ContinuousLinearMap.mul_apply]
    rw [this, hmul, ContinuousLinearMap.zero_apply, inner_zero_right]
  -- For an orthogonal Cauchy series summing to L, ‖L‖² = ∑ ‖vᵢ‖²
  -- This is the orthogonal Parseval identity for HasSum.
  exact hasSum_norm_sq_of_orthogonal_hasSum (fun n => P.proj (f n) x) _ hsum h_orth

/-- The positive Borel measure `μ_x(B) = ‖P(B)x‖²` associated to `x : H`.

This is well-defined by the Parseval identity `pvm_parseval`:
for disjoint sets `{Bᵢ}`, `∑ ‖P(Bᵢ)x‖² = ‖P(⋃Bᵢ)x‖²`. -/
noncomputable def scalarBorelMeasure (P : ProjectionValuedMeasure H) (x : H) :
    MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.ofMeasurable
    (fun B _ => ENNReal.ofReal (‖P.proj B x‖ ^ 2))
    (by simp [P.proj_empty])
    (fun f h_meas h_disj => by
      -- h_disj : Pairwise (Function.onFun Disjoint f)
      -- Need to convert to the form: ∀ i j, i ≠ j → Disjoint (f i) (f j)
      have h_disj' : ∀ i j, i ≠ j → Disjoint (f i) (f j) :=
        fun i j hij => h_disj (fun heq => hij heq)
      -- Need: ENNReal.ofReal (‖P(⋃ f) x‖²) = ∑' n, ENNReal.ofReal (‖P(f n) x‖²)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
          (pvm_parseval P f h_disj' x).summable]
      exact congr_arg ENNReal.ofReal (pvm_parseval P f h_disj' x).tsum_eq.symm)

/-- The total mass of `scalarBorelMeasure P x` is `‖x‖²`. -/
theorem scalarBorelMeasure_univ (P : ProjectionValuedMeasure H) (x : H) :
    P.scalarBorelMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  simp only [scalarBorelMeasure, Measure.ofMeasurable_apply _ MeasurableSet.univ]
  rw [P.proj_univ, ContinuousLinearMap.one_apply]

/-- The scalar Borel measure is finite (total mass `‖x‖² < ∞`). -/
instance scalarBorelMeasure_isFinite (P : ProjectionValuedMeasure H) (x : H) :
    IsFiniteMeasure (P.scalarBorelMeasure x) :=
  ⟨by rw [scalarBorelMeasure_univ]; exact ENNReal.ofReal_lt_top⟩


/-! ### The bounded spectral integral -/

/-- The polarized complex integral over the four polar scalar measures. -/
noncomputable def polarizedIntegral (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) (x y : H) : ℂ :=
  let int_μ (z : H) := MeasureTheory.integral (P.scalarBorelMeasure z) f
  (1 / 4 : ℂ) * (int_μ (x + y) - int_μ (x - y) + Complex.I * int_μ (x - Complex.I • y) - Complex.I * int_μ (x + Complex.I • y))

/-- The sesquilinear form corresponding to `∫ f dP`. -/
noncomputable def spectralSesqForm (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun x =>
        { toFun := fun y => polarizedIntegral P (star f) x y
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
    (sorry)
    (sorry)

/-- The bounded integral `∫ f dP` for a bounded function `f : ℝ → ℂ`.

**Construction**: For each `y : H`, define the sesquilinear form
`S_f(x, y) = ∫ f(t) · ⟨x, P(t)y⟩ dt` using the four polar scalar measures via `polarizedIntegral`. By the
Riesz-Fréchet theorem, this determines a unique bounded operator `T_f : H →L[ℂ] H`
with `⟨x, T_f y⟩ = S_f(x, y)` for all `x, y`. This is `P.boundedIntegral f`. -/
noncomputable def boundedIntegral (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (spectralSesqForm P f)

theorem boundedIntegral_apply_inner (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) (x y : H) :
    inner ℂ (P.boundedIntegral f x) y = polarizedIntegral P (star f) x y := by
  show inner ℂ ((InnerProductSpace.continuousLinearMapOfBilin (spectralSesqForm P f)) x) y = (spectralSesqForm P f) x y
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (spectralSesqForm P f) x y

/-! ### Properties of the bounded integral

These properties characterize the spectral integral uniquely. They follow
from the construction via the sesquilinear form and Bochner integration.

Together, properties (add, smul, zero, mul, star, char) say that
`f ↦ ∫ f dP` is a unital *-homomorphism from L∞(ℝ, P) to B(H)
that sends indicator functions to projections. -/

/-- Linearity in `f`: the integral of a sum is the sum of the integrals. -/
theorem boundedIntegral_add (P : ProjectionValuedMeasure H) (f g : ℝ → ℂ)
    (hf : ∀ x, MeasureTheory.Integrable f (P.scalarBorelMeasure x))
    (hg : ∀ x, MeasureTheory.Integrable g (P.scalarBorelMeasure x)) :
    P.boundedIntegral (f + g) = P.boundedIntegral f + P.boundedIntegral g := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.add_apply, inner_add_left, boundedIntegral_apply_inner,
      boundedIntegral_apply_inner, boundedIntegral_apply_inner]
  simp only [polarizedIntegral]
  have h1 : ∀ z, MeasureTheory.integral (P.scalarBorelMeasure z) (star (f + g)) =
      MeasureTheory.integral (P.scalarBorelMeasure z) (star f) + MeasureTheory.integral (P.scalarBorelMeasure z) (star g) := by
    intro z
    have : star (f + g) = star f + star g := by ext t; simp
    rw [this]
    let L_star : ℂ →L[ℝ] ℂ := {
      toFun := starRingEnd ℂ
      map_add' := map_add _
      map_smul' := star_smul
    }
    have hf_star : MeasureTheory.Integrable (star f) (P.scalarBorelMeasure z) := by
      have : star f = L_star ∘ f := rfl
      rw [this]
      exact ContinuousLinearMap.integrable_comp L_star (hf z)
    have hg_star : MeasureTheory.Integrable (star g) (P.scalarBorelMeasure z) := by
      have : star g = L_star ∘ g := rfl
      rw [this]
      exact ContinuousLinearMap.integrable_comp L_star (hg z)
    exact MeasureTheory.integral_add hf_star hg_star
  simp only [h1]
  ring

/-- Linearity in `f`: the integral of a scalar multiple is the scalar multiple
of the integral. -/
theorem boundedIntegral_smul (P : ProjectionValuedMeasure H) (c : ℂ) (f : ℝ → ℂ)
    (hf : ∀ x, MeasureTheory.Integrable f (P.scalarBorelMeasure x)) :
    P.boundedIntegral (c • f) = c • P.boundedIntegral f := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_left, boundedIntegral_apply_inner,
      boundedIntegral_apply_inner]
  simp only [polarizedIntegral]
  have h1 : ∀ z, MeasureTheory.integral (P.scalarBorelMeasure z) (star (c • f)) =
      starRingEnd ℂ c * MeasureTheory.integral (P.scalarBorelMeasure z) (star f) := by
    intro z
    let L_mul : ℂ →L[ℝ] ℂ := {
      toFun := fun x => star c * x
      map_add' := fun x y => mul_add _ _ _
      map_smul' := fun r x => by
        change star c * ((r : ℂ) * x) = (r : ℂ) * (star c * x)
        ring
    }
    have : star (c • f) = L_mul ∘ (star f) := by ext t; simp [L_mul]
    rw [this]
    let L_star : ℂ →L[ℝ] ℂ := {
      toFun := starRingEnd ℂ
      map_add' := map_add _
      map_smul' := star_smul
    }
    have hf_star : MeasureTheory.Integrable (star f) (P.scalarBorelMeasure z) := by
      have : star f = L_star ∘ f := rfl
      rw [this]
      exact ContinuousLinearMap.integrable_comp L_star (hf z)
    have h_comp : MeasureTheory.integral (P.scalarBorelMeasure z) (L_mul ∘ star f) =
        L_mul (MeasureTheory.integral (P.scalarBorelMeasure z) (star f)) :=
      ContinuousLinearMap.integral_comp_comm L_mul hf_star
    rw [h_comp]
    rfl
  simp only [h1]
  ring

/-- The integral of the zero function is the zero operator. -/
theorem boundedIntegral_zero (P : ProjectionValuedMeasure H) : P.boundedIntegral (0 : ℝ → ℂ) = 0 := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.zero_apply, inner_zero_left, boundedIntegral_apply_inner]
  simp only [polarizedIntegral]
  simp

/-- Multiplicativity: `(∫ f dP)(∫ g dP) = ∫ fg dP`.

This is one of the key structural properties of spectral integrals,
reflecting the fact that the map `f ↦ ∫ f dP` is a *-homomorphism. -/
theorem boundedIntegral_mul (P : ProjectionValuedMeasure H) (f g : ℝ → ℂ) :
    P.boundedIntegral f * P.boundedIntegral g = P.boundedIntegral (f * g) := by
  sorry

@[simp]
theorem scalarBorelMeasure_smul_apply (P : ProjectionValuedMeasure H) (c : ℂ) (x : H) :
    P.scalarBorelMeasure (c • x) = (ENNReal.ofReal (‖c‖ ^ 2)) • P.scalarBorelMeasure x := by
  apply MeasureTheory.Measure.ext
  intro B hB
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have h1 : P.scalarBorelMeasure (c • x) B = ENNReal.ofReal (‖P.proj B (c • x)‖ ^ 2) := by
    simp only [scalarBorelMeasure, MeasureTheory.Measure.ofMeasurable_apply _ hB]
  have h2 : P.scalarBorelMeasure x B = ENNReal.ofReal (‖P.proj B x‖ ^ 2) := by
    simp only [scalarBorelMeasure, MeasureTheory.Measure.ofMeasurable_apply _ hB]
  rw [h1, h2, map_smul, norm_smul, mul_pow]
  rw [ENNReal.ofReal_mul (sq_nonneg _)]

/-- *-Homomorphism property: `(∫ f dP)† = ∫ f̄ dP`.

Combined with multiplicativity, this says `f ↦ ∫ f dP` is a *-homomorphism
from bounded Borel functions to B(H). For real-valued `f` (i.e., `f = f̄`),
this gives `(∫ f dP)† = ∫ f dP`, so the integral is self-adjoint. -/
theorem boundedIntegral_star (P : ProjectionValuedMeasure H) (f : ℝ → ℂ)
    (_hf : ∀ x, MeasureTheory.Integrable f (P.scalarBorelMeasure x)) :
    star (P.boundedIntegral f) = P.boundedIntegral (star f) := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  have : star (P.boundedIntegral f) = ContinuousLinearMap.adjoint (P.boundedIntegral f) := rfl
  rw [this]
  have hLHS : inner ℂ (ContinuousLinearMap.adjoint (P.boundedIntegral f) x) y =
      starRingEnd ℂ (inner ℂ (P.boundedIntegral f y) x) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  have hRHS : inner ℂ (P.boundedIntegral (star f) x) y = polarizedIntegral P (star (star f)) x y := by
    rw [boundedIntegral_apply_inner]
  have h_pol : polarizedIntegral P (star (star f)) x y = polarizedIntegral P f x y := by
    have hs : star (star f) = f := star_star f
    rw [hs]
  rw [hLHS, hRHS, h_pol, boundedIntegral_apply_inner P f y x]
  simp only [polarizedIntegral]
  have h_conj : ∀ z, MeasureTheory.integral (P.scalarBorelMeasure z) (star f) = starRingEnd ℂ (MeasureTheory.integral (P.scalarBorelMeasure z) f) := by
    intro z
    have : star f = fun t => starRingEnd ℂ (f t) := rfl
    rw [this]
    exact integral_conj
  simp only [h_conj]
  have h_add : P.scalarBorelMeasure (x + y) = P.scalarBorelMeasure (y + x) := by rw [add_comm]
  have h_sub : P.scalarBorelMeasure (y - x) = P.scalarBorelMeasure (x - y) := by
    have this1 : y - x = -(x - y) := by rw [neg_sub]
    rw [this1, ← neg_one_smul ℂ (x - y), scalarBorelMeasure_smul_apply, norm_neg, norm_one, one_pow, ENNReal.ofReal_one, one_smul]
  have h_smul_neg_I : P.scalarBorelMeasure (y - Complex.I • x) = P.scalarBorelMeasure (x + Complex.I • y) := by
    have this2 : y - Complex.I • x = -Complex.I • (x + Complex.I • y) := by
      calc y - Complex.I • x = -(Complex.I • x) + y := by rw [sub_eq_neg_add, add_comm]
        _ = -Complex.I • x + -(Complex.I • Complex.I • y) := by simp [smul_smul, Complex.I_mul_I]
        _ = -Complex.I • (x + Complex.I • y) := by simp [smul_add]
    rw [this2, scalarBorelMeasure_smul_apply, norm_neg, Complex.norm_I, one_pow, ENNReal.ofReal_one, one_smul]
  have h_smul_pos_I : P.scalarBorelMeasure (y + Complex.I • x) = P.scalarBorelMeasure (x - Complex.I • y) := by
    have this3 : y + Complex.I • x = Complex.I • (x - Complex.I • y) := by
      calc y + Complex.I • x = Complex.I • x + y := by rw [add_comm]
        _ = Complex.I • x - (Complex.I • Complex.I • y) := by simp [smul_smul, Complex.I_mul_I]
        _ = Complex.I • (x - Complex.I • y) := by simp [smul_sub]
    rw [this3, scalarBorelMeasure_smul_apply, Complex.norm_I, one_pow, ENNReal.ofReal_one, one_smul]
  simp only [h_add, h_sub, h_smul_neg_I, h_smul_pos_I]
  simp only [map_mul, map_add, map_sub, starRingEnd_apply]
  have hI : star (Complex.I) = -Complex.I := Complex.conj_I
  have h_four : star (1 / 4 : ℂ) = 1 / 4 := by norm_num
  simp only [hI, h_four, star_star]
  ring

theorem scalarBorelMeasure_apply (P : ProjectionValuedMeasure H) (x : H) {B : Set ℝ} (hB : MeasurableSet B) :
    P.scalarBorelMeasure x B = ENNReal.ofReal (‖P.proj B x‖ ^ 2) := by
  simp only [scalarBorelMeasure, MeasureTheory.Measure.ofMeasurable_apply _ hB]

/-- Characteristic function property: the integral of `1_B` is `P(B)`.

This is the normalization axiom connecting the integral back to the PVM. -/
theorem boundedIntegral_char (P : ProjectionValuedMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    P.boundedIntegral (B.indicator (fun _ => (1:ℂ))) = P.proj B := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply ext_inner_right ℂ
  intro y
  rw [boundedIntegral_apply_inner]
  have hb : star (B.indicator (fun _ => (1:ℂ))) = B.indicator (fun _ => (1:ℂ)) := by
    ext t
    by_cases ht : t ∈ B
    · simp [ht]
    · simp [ht]
  rw [hb]
  have h_ind : ∀ z, MeasureTheory.integral (P.scalarBorelMeasure z) (B.indicator (fun _ => (1:ℂ))) = ‖P.proj B z‖ ^ 2 := by
    intro z
    rw [integral_indicator hB]
    simp only [integral_const]
    have h1 : ((P.scalarBorelMeasure z).restrict B).real Set.univ = (P.scalarBorelMeasure z B).toReal := by
      rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [h1, scalarBorelMeasure_apply P z hB]
    have h2 : (ENNReal.ofReal (‖P.proj B z‖ ^ 2)).toReal = ‖P.proj B z‖ ^ 2 := ENNReal.toReal_ofReal (sq_nonneg _)
    rw [h2]
    have h3 : ‖P.proj B z‖ ^ 2 • (1 : ℂ) = (‖P.proj B z‖ : ℂ) ^ 2 := by
      rw [Algebra.smul_def, mul_one]
      push_cast
      rfl
    exact h3
  simp only [polarizedIntegral, h_ind]
  have h_pol : inner ℂ (P.proj B x) (P.proj B y) =
      (1 / 4 : ℂ) * (
      (‖P.proj B (x + y)‖ : ℂ) ^ 2 - (‖P.proj B (x - y)‖ : ℂ) ^ 2 +
      Complex.I * (‖P.proj B (x - Complex.I • y)‖ : ℂ) ^ 2 -
      Complex.I * (‖P.proj B (x + Complex.I • y)‖ : ℂ) ^ 2) := by
    have h1 : P.proj B (x + y) = P.proj B x + P.proj B y := map_add _ _ _
    have h2 : P.proj B (x - y) = P.proj B x - P.proj B y := map_sub _ _ _
    have h3 : P.proj B (x - Complex.I • y) = P.proj B x - Complex.I • P.proj B y := by
      rw [map_sub, map_smul]
    have h4 : P.proj B (x + Complex.I • y) = P.proj B x + Complex.I • P.proj B y := by
      rw [map_add, map_smul]
    rw [h1, h2, h3, h4]
    calc inner ℂ (P.proj B x) (P.proj B y) = (
      (‖P.proj B x + P.proj B y‖ : ℂ) ^ 2 - (‖P.proj B x - P.proj B y‖ : ℂ) ^ 2 +
      ((‖P.proj B x - Complex.I • P.proj B y‖ : ℂ) ^ 2 -
      (‖P.proj B x + Complex.I • P.proj B y‖ : ℂ) ^ 2) * Complex.I) / 4 := inner_eq_sum_norm_sq_div_four (P.proj B x) (P.proj B y)
      _ = (1 / 4 : ℂ) * (
      (‖P.proj B x + P.proj B y‖ : ℂ) ^ 2 - (‖P.proj B x - P.proj B y‖ : ℂ) ^ 2 +
      Complex.I * (‖P.proj B x - Complex.I • P.proj B y‖ : ℂ) ^ 2 -
      Complex.I * (‖P.proj B x + Complex.I • P.proj B y‖ : ℂ) ^ 2) := by ring
  rw [← h_pol]
  calc inner ℂ (P.proj B x) (P.proj B y)
      = inner ℂ (star (P.proj B) x) (P.proj B y) := by rw [P.proj_selfAdjoint B]
    _ = inner ℂ (ContinuousLinearMap.adjoint (P.proj B) x) (P.proj B y) := rfl
    _ = inner ℂ x (P.proj B (P.proj B y)) := ContinuousLinearMap.adjoint_inner_left (P.proj B) (P.proj B y) x
    _ = inner ℂ x ((P.proj B * P.proj B) y) := rfl
    _ = inner ℂ x (P.proj B y) := by
      have h_int := P.proj_inter B B
      rw [Set.inter_self B] at h_int
      exact congrArg (inner ℂ x) (DFunLike.congr_fun h_int.symm y)
    _ = inner ℂ x (star (P.proj B) y) := by exact congrArg (fun A => inner ℂ x (A y)) (P.proj_selfAdjoint B).symm
    _ = inner ℂ (P.proj B x) y := ContinuousLinearMap.adjoint_inner_right (P.proj B) x y

/-- The integral of the constant function 1 is the identity operator.

This follows from `boundedIntegral_char` applied to `Set.univ` and `proj_univ`. -/
theorem boundedIntegral_one (P : ProjectionValuedMeasure H) :
    P.boundedIntegral (fun _ => 1) = 1 := by
  have h := P.boundedIntegral_char Set.univ
  simp [Set.indicator_univ] at h
  rw [h]
  exact P.proj_univ

/-- Operator norm bound for the spectral integral: if `f_n → f` pointwise
and the `f_n` are uniformly bounded, then `∫ f_n dP → ∫ f dP` in operator norm.

In particular, this implies that `boundedIntegral` is continuous with respect
to uniform convergence of functions.

The standard proof uses the identity
  `‖(∫ f dP) x‖² = ∫ |f|² dμ_x ≤ ‖f‖_∞² · ‖x‖²`
which gives `‖∫ f dP‖ ≤ ‖f‖_∞`. This requires the full spectral integral
construction. -/
theorem boundedIntegral_norm_le (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) (C : ℝ)
    (hC : ∀ t, ‖f t‖ ≤ C) :
    ‖P.boundedIntegral f‖ ≤ C := by
  sorry

/-- Continuity of `boundedIntegral` with respect to uniform convergence:
if `f_n → f` uniformly (i.e., `‖f_n - f‖_∞ → 0`), then
`‖∫ f_n dP - ∫ f dP‖ → 0`.

This follows from `boundedIntegral_add` and `boundedIntegral_norm_le`:
  `‖∫ f_n dP - ∫ f dP‖ = ‖∫ (f_n - f) dP‖ ≤ ‖f_n - f‖_∞`. -/
theorem boundedIntegral_tendsto_of_uniform (P : ProjectionValuedMeasure H)
    (f : ℝ → ℂ) (g : ℕ → ℝ → ℂ)
    (h_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, ‖g n t - f t‖ ≤ ε) :
    Filter.Tendsto (fun n => P.boundedIntegral (g n)) Filter.atTop
      (nhds (P.boundedIntegral f)) := by
  sorry

/-! ### The complex scalar measure -/

/-- The complex scalar measure `μ_{x,y}(B) = ⟨x, P(B) y⟩`.
This is the sesquilinear form version of `scalarMeasure`. -/
def complexScalarMeasure (P : ProjectionValuedMeasure H) (x y : H) : Set ℝ → ℂ :=
  fun B => @inner ℂ H _ x (P.proj B y)

/-! ### Unbounded domain and integral -/

/-- The domain of the unbounded integral: `{x ∈ H | sup_n ‖∫ f·1_{|f|≤n} dP x‖ < ∞}`.

The carrier is the set of vectors `x` for which the truncated spectral integrals
are uniformly bounded. For the identity function `f(t) = t`, this recovers the domain
of a self-adjoint operator. -/
def unboundedDomain (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) : Submodule ℂ H where
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

/-- The truncated integral: `∫ f·1_{|f|≤n} dP` applied to `x`. -/
private def truncatedIntegral (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) (n : ℕ) (x : H) : H :=
  P.boundedIntegral (fun t => if ‖f t‖ ≤ n then f t else 0) x

/-- The truncated integrals form a Cauchy sequence for vectors in the domain.

The key argument uses the PVM structure: for m ≥ n, the difference `T_m x - T_n x`
equals the integral of `f · 1_{n < ‖f‖ ≤ m}`, and by multiplicativity and the
star property of `boundedIntegral`, we get
  `‖T_m x - T_n x‖² = ⟨x, (∫ |f · 1_{n < ‖f‖ ≤ m}|² dP) x⟩`.
The BddAbove condition on x implies that `∫ |f|² dμ_x < ∞`, so these tails
tend to zero, giving the Cauchy property.

This proof depends on the sorry'd `boundedIntegral_mul`, `boundedIntegral_star`,
and `boundedIntegral_add` properties. -/
private theorem truncatedIntegral_cauchy (P : ProjectionValuedMeasure H) (f : ℝ → ℂ)
    (x : ↥(P.unboundedDomain f)) :
    CauchySeq (fun n => P.truncatedIntegral f n (x : H)) := by
  sorry

/-- For `x` in the unbounded domain, the sequence of truncated integrals converges. -/
private theorem truncatedIntegral_tendsto (P : ProjectionValuedMeasure H) (f : ℝ → ℂ)
    (x : ↥(P.unboundedDomain f)) :
    ∃ y : H, Filter.Tendsto (fun n => P.truncatedIntegral f n (x : H))
      Filter.atTop (nhds y) :=
  cauchySeq_tendsto_of_complete (P.truncatedIntegral_cauchy f x)

/-- The unbounded integral `∫ f dP` as a partially defined linear map.

For a general measurable `f : ℝ → ℂ`, this is defined on the domain
`{x | ∫ |f|² dμ_x < ∞}` and satisfies `⟨x, (∫ f dP) y⟩ = ∫ f dμ_{x,y}`. -/
def unboundedIntegral (P : ProjectionValuedMeasure H) (f : ℝ → ℂ) : LinearPMap ℂ H H where
  domain := P.unboundedDomain f
  toFun :=
    { toFun := fun x => limUnder Filter.atTop
        (fun n => P.truncatedIntegral f n (x : H))
      map_add' := by
        intro x y
        have hx := P.truncatedIntegral_tendsto f x
        have hy := P.truncatedIntegral_tendsto f y
        have hxy := P.truncatedIntegral_tendsto f (x + y)
        obtain ⟨lx, hlx⟩ := hx
        obtain ⟨ly, hly⟩ := hy
        obtain ⟨lxy, hlxy⟩ := hxy
        have hx_eq : limUnder Filter.atTop
            (fun n => P.truncatedIntegral f n (x : H)) = lx := hlx.limUnder_eq
        have hy_eq : limUnder Filter.atTop
            (fun n => P.truncatedIntegral f n (y : H)) = ly := hly.limUnder_eq
        have hxy_eq : limUnder Filter.atTop
            (fun n => P.truncatedIntegral f n ((x + y : ↥(P.unboundedDomain f)) : H)) = lxy :=
          hlxy.limUnder_eq
        rw [hx_eq, hy_eq, hxy_eq]
        have hlin : ∀ n, P.truncatedIntegral f n ((x + y : ↥(P.unboundedDomain f)) : H) =
            P.truncatedIntegral f n (x : H) + P.truncatedIntegral f n (y : H) := by
          intro n
          show (P.boundedIntegral _ ) ((x : H) + (y : H)) =
            (P.boundedIntegral _) (x : H) + (P.boundedIntegral _) (y : H)
          exact ContinuousLinearMap.map_add _ _ _
        have hsum : Filter.Tendsto
            (fun n => P.truncatedIntegral f n (x : H) + P.truncatedIntegral f n (y : H))
            Filter.atTop (nhds (lx + ly)) := hlx.add hly
        exact tendsto_nhds_unique (hlxy.congr (fun n => hlin n)) hsum
      map_smul' := by
        intro c x
        have hx := P.truncatedIntegral_tendsto f x
        have hcx := P.truncatedIntegral_tendsto f (c • x)
        obtain ⟨lx, hlx⟩ := hx
        obtain ⟨lcx, hlcx⟩ := hcx
        have hx_eq : limUnder Filter.atTop
            (fun n => P.truncatedIntegral f n (x : H)) = lx := hlx.limUnder_eq
        have hcx_eq : limUnder Filter.atTop
            (fun n => P.truncatedIntegral f n ((c • x : ↥(P.unboundedDomain f)) : H)) = lcx :=
          hlcx.limUnder_eq
        rw [hx_eq, hcx_eq]
        show lcx = c • lx
        have hlin : ∀ n, P.truncatedIntegral f n ((c • x : ↥(P.unboundedDomain f)) : H) =
            c • P.truncatedIntegral f n (x : H) := by
          intro n
          show (P.boundedIntegral _) (c • (x : H)) = c • (P.boundedIntegral _) (x : H)
          exact ContinuousLinearMap.map_smul _ _ _
        have hscl : Filter.Tendsto
            (fun n => c • P.truncatedIntegral f n (x : H))
            Filter.atTop (nhds (c • lx)) := hlx.const_smul c
        exact tendsto_nhds_unique (hlcx.congr (fun n => hlin n)) hscl }

/-- The bounded integral of a real-valued function is symmetric:
`⟨(∫ f dP) x, y⟩ = ⟨x, (∫ f dP) y⟩`.

This follows from `boundedIntegral_star`: for real `f`, `star f = f`,
so `(∫ f dP)† = ∫ f̄ dP = ∫ f dP`, i.e. the integral is self-adjoint. -/
theorem boundedIntegral_symmetric_real (P : ProjectionValuedMeasure H) (f : ℝ → ℂ)
    (hf : ∀ t, (f t).im = 0)
    (h_int : ∀ x, MeasureTheory.Integrable f (P.scalarBorelMeasure x)) (x y : H) :
    @inner ℂ H _ (P.boundedIntegral f x) y =
    @inner ℂ H _ x (P.boundedIntegral f y) := by
  have hstar : star f = f := by ext t; exact Complex.conj_eq_iff_im.mpr (hf t)
  have hsa : IsSelfAdjoint (P.boundedIntegral f) := by
    show star (P.boundedIntegral f) = P.boundedIntegral f
    rw [P.boundedIntegral_star f h_int]
    exact congrArg P.boundedIntegral hstar
  exact hsa.isSymmetric x y

/-- The truncated integral of the identity function is symmetric. -/
private theorem truncatedIntegral_id_symmetric (P : ProjectionValuedMeasure H) (n : ℕ) (x y : H) :
    @inner ℂ H _ (P.truncatedIntegral (fun t => (t : ℂ)) n x) y =
    @inner ℂ H _ x (P.truncatedIntegral (fun t => (t : ℂ)) n y) := by
  sorry

/-- Key property: the unbounded integral of the identity function
is a (formally) self-adjoint operator. -/
theorem unboundedIntegral_id_symmetric (P : ProjectionValuedMeasure H) :
    ∀ (x y : (P.unboundedDomain (fun t => (t : ℂ)))),
      @inner ℂ H _ (P.unboundedIntegral (fun t => (t : ℂ)) x) y =
      @inner ℂ H _ (x : H) (P.unboundedIntegral (fun t => (t : ℂ)) y) := by
  intro x y
  obtain ⟨lx, hlx⟩ := P.truncatedIntegral_tendsto (fun t => (t : ℂ)) x
  obtain ⟨ly, hly⟩ := P.truncatedIntegral_tendsto (fun t => (t : ℂ)) y
  have hx_eq : (P.unboundedIntegral (fun t => (t : ℂ)) x : H) = lx := by
    show limUnder Filter.atTop (fun n => P.truncatedIntegral _ n (x : H)) = lx
    exact hlx.limUnder_eq
  have hy_eq : (P.unboundedIntegral (fun t => (t : ℂ)) y : H) = ly := by
    show limUnder Filter.atTop (fun n => P.truncatedIntegral _ n (y : H)) = ly
    exact hly.limUnder_eq
  rw [hx_eq, hy_eq]
  have hleft : Filter.Tendsto
      (fun n => @inner ℂ H _
        (P.truncatedIntegral (fun t => (t : ℂ)) n (x : H)) (y : H))
      Filter.atTop (nhds (@inner ℂ H _ lx (y : H))) :=
    Filter.Tendsto.inner hlx tendsto_const_nhds
  have hright : Filter.Tendsto
      (fun n => @inner ℂ H _
        (x : H) (P.truncatedIntegral (fun t => (t : ℂ)) n (y : H)))
      Filter.atTop (nhds (@inner ℂ H _ (x : H) ly)) :=
    Filter.Tendsto.inner tendsto_const_nhds hly
  have heq : ∀ n,
      @inner ℂ H _ (P.truncatedIntegral (fun t => (t : ℂ)) n (x : H)) (y : H) =
      @inner ℂ H _ (x : H) (P.truncatedIntegral (fun t => (t : ℂ)) n (y : H)) :=
    fun n => P.truncatedIntegral_id_symmetric n (x : H) (y : H)
  exact tendsto_nhds_unique (hleft.congr (fun n => heq n)) hright

end ProjectionValuedMeasure

end
