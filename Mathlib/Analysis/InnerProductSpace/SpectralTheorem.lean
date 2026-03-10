/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.SpectralIntegral
import Mathlib.Analysis.InnerProductSpace.CayleyTransform
import Mathlib.Analysis.InnerProductSpace.OneParameterGroup
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.ExpDecay

open MeasureTheory TopologicalSpace Filter Set Topology

/-!
# The Spectral Theorem

## Main results

* `spectral_theorem_bounded`: bounded self-adjoint → unique PVM
* `spectral_theorem_unbounded`: unbounded self-adjoint → PVM via Cayley
* `stone_theorem_unbounded`: C₀-unitary group ↔ self-adjoint generator

## Proof strategy for the bounded case

Given a bounded self-adjoint operator `A` on a Hilbert space `H`:

1. **CFC (Continuous Functional Calculus)**: Mathlib provides `cfcHom` for self-adjoint
   elements in C*-algebras, giving a continuous *-homomorphism
   `Φ : C(σ(A), ℝ) →⋆ₐ[ℝ] B(H)` with `Φ(id) = A`.

2. **Spectral measure extraction**: From the *-homomorphism `Φ`, we extract a PVM `P`
   on `ℝ` such that `Φ(f) = ∫ f dP` for all continuous `f`. This is the
   Riesz-Markov-Kakutani step: for each `x ∈ H`, the map `f ↦ ⟨x, Φ(f) x⟩` is a
   positive linear functional on `C(σ(A))`, hence a Borel measure `μ_x`. By
   polarization, we obtain the full PVM.

3. **Conclusion**: Since `Φ(id) = A` and `Φ(f) = ∫ f dP`, we get `A = ∫ id dP`.

The intermediate lemmas below make this roadmap explicit, with sorry's on the
steps requiring substantial new development.

## References

* Reed & Simon, *Methods of Modern Mathematical Physics I*, Theorem VII.2
* Schmuedgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Ch. 5
-/

noncomputable section

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Helper: the PVM integral of the identity function λ ↦ λ. -/
private def pvm_id_integral (P : ProjectionValuedMeasure H) : H →L[ℂ] H :=
  P.boundedIntegral ((↑) : ℝ → ℂ)

/-! ### Intermediate lemmas for the bounded spectral theorem -/

-- The CFC instance for normal elements in C*-algebras is only a local instance in
-- `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic`, so we locally
-- activate it here. This gives us `ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint`
-- via the chain: CStarAlgebra → CFC ℂ IsStarNormal → CFC ℝ IsSelfAdjoint.
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- **Step 1**: Every bounded self-adjoint operator on a Hilbert space has a
continuous functional calculus, yielding a *-homomorphism from `C(σ(A), ℝ)`.

This is already provided by Mathlib's CFC infrastructure:
- `H →L[ℂ] H` is a `CStarAlgebra` (from `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`)
- `ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint` (from CFC instances)
- `cfcHom hA : C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H)` with `cfcHom hA id = A`
-/
theorem cfc_exists_starAlgHom (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ Φ : C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H),
      Continuous Φ ∧
      Φ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) = A := by
  exact ⟨cfcHom hA, cfcHom_continuous hA, cfcHom_id hA⟩

/-- **Step 2 (key sorry)**: From a positive linear functional on `C(K)` to a Borel measure.

For each `x : H`, the map `f ↦ re⟨x, Φ(f) x⟩` is a positive linear functional on `C(σ(A), ℝ)`.
By the Riesz-Markov-Kakutani representation theorem, there exists a unique Borel measure `μ_x`
on `σ(A)` such that `re⟨x, Φ(f) x⟩ = ∫ f dμ_x`.

This is the core analytic step that bridges the CFC *-homomorphism to a PVM.
The Riesz-Markov theorem exists in Mathlib (`MeasureTheory.Measure.riesz_markov_kakutani`)
but connecting it to the operator-valued setting requires additional work. -/
theorem riesz_markov_for_operator_functional
    (K : Set ℝ) [CompactSpace K]
    (Φ : C(K, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H))
    (hΦ_cont : Continuous Φ) (x : H) :
    ∃ μ : MeasureTheory.Measure K,
      ∀ f : C(K, ℝ), Complex.re (@inner ℂ H _ x (Φ f x)) =
        ∫ t, f t ∂μ := by
  sorry

/-- **Step 3 (key sorry)**: From scalar measures to a projection-valued measure.

Given a *-homomorphism `Φ : C(K, ℝ) →⋆ₐ[ℝ] B(H)`, there exists a PVM `P` on `ℝ` with
support in `K` such that `Φ(f) = ∫_K f dP` for every continuous `f : K → ℝ`.

The construction proceeds by:
(a) For each `x`, use Riesz-Markov to get a scalar measure `μ_x`.
(b) For each pair `(x, y)`, define `μ_{x,y}` by polarization.
(c) For each Borel set `B`, define `P(B)` as the unique operator satisfying
    `⟨x, P(B) y⟩ = μ_{x,y}(B)`.
(d) Verify `P` satisfies the PVM axioms (idempotent, self-adjoint, σ-additive). -/
theorem starAlgHom_to_pvm
    (K : Set ℝ) [CompactSpace K]
    (Φ : C(K, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H))
    (hΦ_cont : Continuous Φ) :
    ∃ P : ProjectionValuedMeasure H,
      ∀ f : C(K, ℝ), Φ f = P.boundedIntegral (fun t => (f ⟨t, sorry⟩ : ℂ)) := by
  sorry

/-- **Step 4**: The PVM integral of `id` recovers the operator.

Given the PVM `P` from `starAlgHom_to_pvm` applied to `cfcHom`, we have
`Φ(id) = ∫ id dP = A`, so `A = pvm_id_integral P`. -/
theorem cfc_pvm_integral_eq (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (P : ProjectionValuedMeasure H)
    (hP : ∀ f : C(spectrum ℝ A, ℝ),
      cfcHom hA f = P.boundedIntegral (fun t => (f ⟨t, sorry⟩ : ℂ))) :
    A = pvm_id_integral P := by
  sorry

/-- **Spectral theorem (bounded case)**: Every bounded self-adjoint operator
has a projection-valued measure such that A = ∫ λ dP(λ).

The proof uses the continuous functional calculus (CFC) from Mathlib:
1. `cfcHom hA` provides `Φ : C(σ(A), ℝ) →⋆ₐ[ℝ] B(H)` with `Φ(id) = A`
2. `starAlgHom_to_pvm` extracts a PVM `P` with `Φ(f) = ∫ f dP` (sorry'd)
3. Evaluating at `f = id` gives `A = Φ(id) = ∫ id dP = pvm_id_integral P`
-/
theorem spectral_theorem_bounded (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ P : ProjectionValuedMeasure H, A = pvm_id_integral P := by
  -- Step 1: The CFC gives a continuous *-homomorphism Φ : C(σ(A), ℝ) →⋆ₐ[ℝ] B(H)
  -- with Φ(id) = A.
  have hΦ_cont : Continuous (cfcHom hA : C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H)) :=
    cfcHom_continuous hA
  have hΦ_id : cfcHom hA ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) = A :=
    cfcHom_id hA
  -- Step 2: Extract a PVM P such that Φ(f) = ∫ f dP for all continuous f.
  obtain ⟨P, hP⟩ := starAlgHom_to_pvm (spectrum ℝ A) (cfcHom hA) hΦ_cont
  -- Step 3: Conclude A = ∫ id dP.
  exact ⟨P, cfc_pvm_integral_eq A hA P hP⟩

/-- The identity function `ℝ → ℂ` used as the spectral integrand. -/
private abbrev spectral_id : ℝ → ℂ := fun t => (t : ℂ)

/-- **Spectral theorem (unbounded case)**: Every densely-defined self-adjoint
operator A has a PVM P such that A = ∫ λ dP(λ).

More precisely, there exists a projection-valued measure P such that
1. The domain of A equals the domain of the unbounded integral ∫ id dP, and
2. A agrees with ∫ id dP on every vector in the domain.

The proof proceeds by:
1. Applying the Cayley transform to obtain a unitary V = (A - iI)(A + iI)⁻¹
2. Obtaining a PVM Q for V via the bounded spectral theorem for unitary operators
3. Pulling Q back through the inverse Cayley transform to get P for A -/
theorem spectral_theorem_unbounded (A : LinearPMap ℂ H H)
    (hA : IsSelfAdjoint A) (hA_dense : Dense (A.domain : Set H)) :
    ∃ P : ProjectionValuedMeasure H,
      A.domain = (P.unboundedDomain spectral_id) ∧
      ∀ (x : H) (hx_A : x ∈ A.domain) (hx_P : x ∈ P.unboundedDomain spectral_id),
        A ⟨x, hx_A⟩ = P.unboundedIntegral spectral_id ⟨x, hx_P⟩ := by
  -- Step 1: The Cayley transform gives a unitary operator V
  have hV_unitary : (LinearPMap.cayleyTransformCLM hA) ∈ unitary (H →L[ℂ] H) :=
    LinearPMap.cayleyTransformCLM_isUnitary hA
  -- Step 2: Apply the spectral theorem to V to get a PVM Q
  --   (The bounded/unitary spectral theorem gives a PVM Q such that
  --    V = ∫ z dQ(z) on the unit circle.)
  obtain ⟨Q, _hQ⟩ : ∃ Q : ProjectionValuedMeasure H, True := by
    exact ⟨sorry, trivial⟩
  -- Step 3: Pull Q back through the inverse Cayley transform
  --   The inverse Cayley map sends z ↦ i(1 + z)/(1 - z), mapping the unit circle
  --   (minus {1}) to ℝ. Define P(B) = Q(cayley⁻¹(B)) for Borel sets B ⊆ ℝ.
  let P : ProjectionValuedMeasure H := sorry
  -- Step 4: Verify domain equality: dom(A) = dom(∫ id dP)
  have h_domain : A.domain = P.unboundedDomain spectral_id := by
    sorry
  -- Step 5: Verify pointwise equality: Ax = (∫ id dP) x for x ∈ dom(A)
  have h_agree : ∀ (x : H) (hx_A : x ∈ A.domain)
      (hx_P : x ∈ P.unboundedDomain spectral_id),
      A ⟨x, hx_A⟩ = P.unboundedIntegral spectral_id ⟨x, hx_P⟩ := by
    sorry
  exact ⟨P, h_domain, h_agree⟩

/-! ### Uniqueness of spectral measure

The proof decomposes into four steps:
1. Agreement on `∫ λ dP` implies agreement on `∫ λⁿ dP` for all n (multiplicativity)
2. Agreement on monomials implies agreement on all polynomial integrals (linearity)
3. Agreement on polynomials implies agreement on continuous functions (Stone-Weierstrass)
4. Agreement on continuous function integrals implies `P(B) = Q(B)` (Riesz representation) -/

/-- Step 1: If `∫ λ dP = ∫ λ dQ`, then `∫ λⁿ dP = ∫ λⁿ dQ` for all n. -/
private theorem spectral_unique_powers (P Q : ProjectionValuedMeasure H)
    (h : pvm_id_integral P = pvm_id_integral Q) (n : ℕ) :
    P.boundedIntegral (fun t => ((t : ℂ) ^ n)) =
    Q.boundedIntegral (fun t => ((t : ℂ) ^ n)) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    rw [ProjectionValuedMeasure.boundedIntegral_one,
        ProjectionValuedMeasure.boundedIntegral_one]
  | succ n ih =>
    have hfun : (fun t : ℝ => ((t : ℂ) ^ (n + 1))) =
        (fun t : ℝ => (t : ℂ)) * (fun t : ℝ => ((t : ℂ) ^ n)) := by
      ext t
      simp [pow_succ]
      ring
    rw [hfun]
    rw [← ProjectionValuedMeasure.boundedIntegral_mul,
        ← ProjectionValuedMeasure.boundedIntegral_mul]
    have h' : P.boundedIntegral (fun t => (t : ℂ)) =
        Q.boundedIntegral (fun t => (t : ℂ)) := h
    rw [h', ih]

/-- Step 2: Agreement on powers implies agreement on all polynomial integrals. -/
private theorem spectral_unique_polynomials (P Q : ProjectionValuedMeasure H)
    (h_pow : ∀ n : ℕ, P.boundedIntegral (fun t => ((t : ℂ) ^ n)) =
      Q.boundedIntegral (fun t => ((t : ℂ) ^ n)))
    (p : Polynomial ℂ) :
    P.boundedIntegral (fun t => p.eval (t : ℂ)) =
    Q.boundedIntegral (fun t => p.eval (t : ℂ)) := by
  sorry

/-- The difference of two PVM integrals respects uniform limits.
If `P` and `Q` agree on a sequence of functions `g_n` that converge uniformly
to `f`, then `P` and `Q` agree on `f`.

This follows from `boundedIntegral_tendsto_of_uniform` applied to both `P` and `Q`. -/
private theorem boundedIntegral_eq_of_uniform_limit (P Q : ProjectionValuedMeasure H)
    (f : ℝ → ℂ) (g : ℕ → ℝ → ℂ)
    (h_agree : ∀ n, P.boundedIntegral (g n) = Q.boundedIntegral (g n))
    (h_unif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, ‖g n t - f t‖ ≤ ε) :
    P.boundedIntegral f = Q.boundedIntegral f := by
  -- Both P.boundedIntegral (g n) and Q.boundedIntegral (g n) converge (to their
  -- respective limits) and are equal for each n. By uniqueness of limits in a
  -- T2 space, the limits coincide.
  have hP : Filter.Tendsto (fun n => P.boundedIntegral (g n)) Filter.atTop
      (nhds (P.boundedIntegral f)) :=
    P.boundedIntegral_tendsto_of_uniform f g h_unif
  have hQ : Filter.Tendsto (fun n => Q.boundedIntegral (g n)) Filter.atTop
      (nhds (Q.boundedIntegral f)) :=
    Q.boundedIntegral_tendsto_of_uniform f g h_unif
  have heq : (fun n => Q.boundedIntegral (g n)) = (fun n => P.boundedIntegral (g n)) :=
    funext (fun n => (h_agree n).symm)
  rw [heq] at hQ
  exact tendsto_nhds_unique hP hQ

/-- Step 3: Agreement on polynomials implies agreement on continuous functions
(by Stone-Weierstrass density).

**Proof outline**: By the Stone-Weierstrass theorem, polynomial functions are
dense in `C(K, ℝ)` for any compact `K ⊆ ℝ`. Given a continuous function `f`,
we can approximate it uniformly by polynomial functions. Since `P` and `Q`
agree on all polynomial integrals (hypothesis `h_poly`), and `boundedIntegral`
is continuous with respect to uniform convergence
(`boundedIntegral_tendsto_of_uniform`), we conclude `P` and `Q` agree on `f`.

The key sorry is in `boundedIntegral_tendsto_of_uniform`, which depends on
the operator norm bound `‖∫ f dP‖ ≤ ‖f‖_∞` (sorry'd in SpectralIntegral). -/
private theorem spectral_unique_continuous (P Q : ProjectionValuedMeasure H)
    (h_poly : ∀ p : Polynomial ℂ,
      P.boundedIntegral (fun t => p.eval (t : ℂ)) =
      Q.boundedIntegral (fun t => p.eval (t : ℂ)))
    (f : ℝ → ℂ) (hf : Continuous f) :
    P.boundedIntegral f = Q.boundedIntegral f := by
  /- **Proof strategy (Stone-Weierstrass + continuity of boundedIntegral)**:
     By Stone-Weierstrass (`polynomialFunctions.starClosure_topologicalClosure`
     in `Mathlib.Topology.ContinuousMap.StoneWeierstrass`), polynomial functions
     are dense in `C(K, ℂ)` for any compact `K ⊆ ℝ`.

     The PVM `P` has support in a compact set `K` (the spectrum), so `f` restricted
     to `K` can be uniformly approximated by polynomials `pₙ` with
     `‖pₙ - f‖_{∞,K} → 0`.

     Since `P` and `Q` agree on all polynomial integrals (hypothesis `h_poly`),
     and since `boundedIntegral` is continuous with respect to uniform convergence
     (`boundedIntegral_tendsto_of_uniform`, which depends on the operator norm
     bound `‖∫ f dP‖ ≤ ‖f‖_∞`), the conclusion follows from
     `boundedIntegral_eq_of_uniform_limit`.

     The remaining sorry encapsulates two ingredients:
     (a) compact support of P (to apply Stone-Weierstrass on a compact set), and
     (b) the operator norm bound (sorry'd in `boundedIntegral_norm_le`). -/
  -- By Stone-Weierstrass, there exists a sequence of polynomials pₙ with
  -- ‖pₙ - f‖_∞ → 0 on the support of P. We construct such a sequence.
  -- (The existence follows from `polynomialFunctions.topologicalClosure` which
  -- states that polynomials are dense in C(K,ℝ) for compact K ⊆ ℝ.)
  suffices ∃ (p : ℕ → Polynomial ℂ),
      ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t : ℝ, ‖(p n).eval (t : ℂ) - f t‖ ≤ ε by
    obtain ⟨p, hp⟩ := this
    exact boundedIntegral_eq_of_uniform_limit P Q f
      (fun n t => (p n).eval (t : ℂ)) (fun n => h_poly (p n)) hp
  -- The existence of such polynomial approximants follows from
  -- Stone-Weierstrass on a compact set containing the support of P.
  -- This requires:
  -- (1) compact support of P (to restrict to a compact domain)
  -- (2) Stone-Weierstrass: `polynomialFunctions.topologicalClosure` (fully proved)
  -- (3) converting density in C(K,ℂ) to pointwise uniform bounds on ℝ
  -- Item (1) is not yet formalized for our PVM type.
  sorry

/-- Step 4: Agreement on continuous function integrals implies P(B) = Q(B)
(by Riesz representation uniqueness). -/
private theorem spectral_unique_of_continuous_agree (P Q : ProjectionValuedMeasure H)
    (h_cont : ∀ (f : ℝ → ℂ), Continuous f →
      P.boundedIntegral f = Q.boundedIntegral f) :
    ∀ B, P.proj B = Q.proj B := by
  sorry

/-- Uniqueness of spectral measure: if two PVMs give the same operator
via `∫ λ dP(λ)`, they are equal on all sets. -/
theorem spectral_unique (P Q : ProjectionValuedMeasure H)
    (h : pvm_id_integral P = pvm_id_integral Q) :
    ∀ B, P.proj B = Q.proj B := by
  apply spectral_unique_of_continuous_agree
  apply spectral_unique_continuous
  apply spectral_unique_polynomials
  exact spectral_unique_powers P Q h

/-- **Borel functional calculus** via PVM. -/
def borelFunctionalCalculus (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (f : ℝ → ℂ) : H →L[ℂ] H :=
  (spectral_theorem_bounded A hA).choose.boundedIntegral f

/-! ### Stone's theorem (unbounded forward direction)

The generator is defined as `A x = lim_{t→0} (U(t)x - x)/(it)`, with domain
consisting of those `x` for which this limit exists. -/

/-- The domain of the Stone generator: vectors `x` for which
`lim_{t→0} (U(t)x - x)/(it)` exists. -/
private def stoneGeneratorDomain (U : StronglyContUnitaryGroup H) :
    Submodule ℂ H where
  carrier := {x : H | ∃ y : H, Filter.Tendsto
    (fun t : ℝ => (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x)))
    (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds y)}
  zero_mem' := ⟨0, by
    simp only [map_zero, sub_self, smul_zero]
    exact tendsto_const_nhds⟩
  add_mem' := by
    rintro x y ⟨lx, hlx⟩ ⟨ly, hly⟩
    exact ⟨lx + ly, by
      have : Filter.Tendsto
        (fun t : ℝ => (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t (x + y) : H) - (x + y))))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (lx + ly)) := by
        have heq : (fun t : ℝ => (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t (x + y) : H) - (x + y)))) =
            (fun t : ℝ => (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x)) +
              (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t y : H) - y))) := by
          ext t
          simp only [map_add (U.toFun t) x y]
          rw [add_sub_add_comm, smul_add, smul_add]
        rw [heq]
        exact Filter.Tendsto.add hlx hly
      exact this⟩
  smul_mem' := by
    rintro c x ⟨lx, hlx⟩
    exact ⟨c • lx, by
      have : Filter.Tendsto
        (fun t : ℝ => (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t (c • x) : H) - (c • x))))
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (c • lx)) := by
        have heq : (fun t : ℝ => (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t (c • x) : H) - (c • x)))) =
            (fun t : ℝ => c • ((t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x)))) := by
          ext t
          simp only [map_smul (U.toFun t) c x, smul_sub, smul_comm c]
        rw [heq]
        exact Filter.Tendsto.const_smul hlx c
      exact this⟩

/-- The Stone generator as a partially defined linear map:
`A x = lim_{t→0} (U(t)x - x)/(it)`. -/
private def stoneGenerator (U : StronglyContUnitaryGroup H) :
    LinearPMap ℂ H H where
  domain := stoneGeneratorDomain U
  toFun :=
    { toFun := fun x => (x.2.choose : H)
      map_add' := by
        intro ⟨x, hx⟩ ⟨y, hy⟩
        simp only []
        apply tendsto_nhds_unique (Submodule.add_mem _ hx hy).choose_spec
        have heq : ∀ t : ℝ, (t : ℂ)⁻¹ • (Complex.I⁻¹ •
            ((U.toFun t (x + y) : H) - (x + y))) =
            (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x)) +
              (t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t y : H) - y)) := by
          intro t
          simp only [map_add (U.toFun t) x y]
          rw [add_sub_add_comm, smul_add, smul_add]
        exact (Filter.Tendsto.congr (fun t => (heq t).symm)
          (Filter.Tendsto.add hx.choose_spec hy.choose_spec))
      map_smul' := by
        intro c ⟨x, hx⟩
        simp only [SetLike.val_smul, RingHom.id_apply]
        apply tendsto_nhds_unique (Submodule.smul_mem _ c hx).choose_spec
        have heq : ∀ t : ℝ, (t : ℂ)⁻¹ • (Complex.I⁻¹ •
            ((U.toFun t (c • x) : H) - (c • x))) =
            c • ((t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x))) := by
          intro t
          simp only [map_smul (U.toFun t) c x, smul_sub, smul_comm c]
        exact (Filter.Tendsto.congr (fun t => (heq t).symm)
          (Filter.Tendsto.const_smul hx.choose_spec c)) }

/-- Cesàro average: `x_T = (1/T) ∫₀ᵀ U(t) x dt`. This is the Bochner integral
of the continuous map `t ↦ U(t) x` over the interval `[0, T]`, scaled by `1/T`. -/
private def cesàroAverage (U : StronglyContUnitaryGroup H) (x : H) (T : ℝ) : H :=
  (T⁻¹ : ℝ) • ∫ t in (0 : ℝ)..T, U.toFun t x

/-- The Cesàro averages `x_T` converge to `x` as `T → 0⁺`.
This follows from the strong continuity of `U`: the map `t ↦ U(t) x` is
continuous with `U(0) x = x`, so `(1/T) ∫₀ᵀ U(t) x dt → U(0) x = x`. -/
private theorem cesàroAverage_tendsto (U : StronglyContUnitaryGroup H) (x : H) :
    Filter.Tendsto (fun T => cesàroAverage U x T) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  sorry

/-- The Cesàro averages lie in the generator domain.
For `T > 0`, the difference quotient `(U(h) x_T - x_T)/(ih)` has a limit as `h → 0`,
because `U(h) x_T - x_T = (1/T)(∫_h^{T+h} U(t) x dt - ∫_0^T U(t) x dt)`
`= (1/T)(∫_T^{T+h} U(t) x dt - ∫_0^h U(t) x dt)`,
and by the Fundamental Theorem of Calculus, dividing by `h` and taking `h → 0`
gives the limit `(1/(iT))(U(T) x - x)`. -/
private theorem cesàroAverage_mem_domain (U : StronglyContUnitaryGroup H) (x : H)
    (T : ℝ) (hT : 0 < T) :
    cesàroAverage U x T ∈ stoneGeneratorDomain U := by
  sorry

/-- The generator domain is dense in H.
Proof: for any `x : H`, the Cesàro averages `(1/T) ∫₀ᵀ U(t) x dt` lie in the
domain (by `cesàroAverage_mem_domain`) and converge to `x` as `T → 0⁺`
(by `cesàroAverage_tendsto`). -/
private theorem stoneGeneratorDomain_dense (U : StronglyContUnitaryGroup H) :
    Dense (stoneGeneratorDomain U : Set H) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  apply mem_closure_of_tendsto (cesàroAverage_tendsto U x)
  apply Filter.eventually_of_mem self_mem_nhdsWithin
  intro T hT
  exact cesàroAverage_mem_domain U x T (Set.mem_Ioi.mp hT)

/-- Key identity: the difference quotient satisfies
`⟪F(t, x), y⟫ = ⟪x, F(-t, y)⟫` where `F(t, z) = t⁻¹ • (I⁻¹ • (U(t)z - z))`. -/
private theorem stoneGenerator_inner_swap (U : StronglyContUnitaryGroup H)
    (x y : H) (t : ℝ) :
    @inner ℂ H _ ((t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x))) y =
    @inner ℂ H _ x (((-t : ℝ) : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun (-t) y : H) - y))) := by
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  -- Use unitarity: ⟪U(t) x, y⟫ = ⟪x, U(-t) y⟫
  have hU : @inner ℂ H _ (U.toFun t x) y = @inner ℂ H _ x (U.toFun (-t) y) := by
    rw [U.map_neg t]
    change @inner ℂ H _ (U.toFun t x) y = @inner ℂ H _ x ((ContinuousLinearMap.adjoint (U.toFun t)) y)
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [hU]
  -- Now it's algebra: conj(t⁻¹) * conj(I⁻¹) * (⟪x, U(-t)y⟫ - ⟪x,y⟫)
  --                  = (-t)⁻¹ * I⁻¹ * (⟪x, U(-t)y⟫ - ⟪x,y⟫)
  -- conj(t⁻¹) = t⁻¹ for t : ℝ, conj(I⁻¹) = conj(-I) = I = -(I⁻¹)... hmm
  -- Actually: conj((t:ℂ)⁻¹) = (t:ℂ)⁻¹ and conj(I⁻¹) = -I⁻¹... wait
  -- I⁻¹ = -I, so conj(I⁻¹) = conj(-I) = -conj(I) = -(-I) = I = -I⁻¹... no
  -- conj(I) = -I, so conj(-I) = -(-I) = I. And I⁻¹ = -I. So conj(I⁻¹) = conj(-I) = I.
  -- Also (-t:ℂ)⁻¹ = -(t:ℂ)⁻¹.
  -- LHS = (t:ℂ)⁻¹ * I * (⟪x, U(-t)y⟫ - ⟪x,y⟫)  [since conj(t⁻¹)=t⁻¹, conj(I⁻¹)=I]
  -- RHS = (-(t:ℂ))⁻¹ * I⁻¹ * (⟪x, U(-t)y⟫ - ⟪x,y⟫)
  --     = -(t:ℂ)⁻¹ * (-I) * (⟪x, U(-t)y⟫ - ⟪x,y⟫)
  --     = (t:ℂ)⁻¹ * I * (⟪x, U(-t)y⟫ - ⟪x,y⟫) ✓
  have ht_conj : starRingEnd ℂ (t : ℂ)⁻¹ = (t : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hI_conj : starRingEnd ℂ (Complex.I⁻¹) = -Complex.I⁻¹ := by
    rw [map_inv₀, Complex.conj_I]
    simp [Complex.inv_I]
  have hneg_inv : ((-t : ℝ) : ℂ)⁻¹ = -(t : ℂ)⁻¹ := by
    rw [Complex.ofReal_neg, neg_inv]
  rw [ht_conj, hI_conj, hneg_inv]
  ring

/-- The difference quotient composed with negation tends to the generator value. -/
private theorem stoneGenerator_tendsto_neg (U : StronglyContUnitaryGroup H) (y : H)
    (hy : y ∈ stoneGeneratorDomain U) :
    Filter.Tendsto
      (fun t : ℝ => ((-t : ℝ) : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun (-t) y : H) - y)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds hy.choose) := by
  -- hy.choose_spec says the limit via nhdsWithin 0 {0}ᶜ exists
  -- We compose with negation: if F(s) → L as s → 0 (s ≠ 0), then F(-t) → L as t → 0 (t ≠ 0)
  have hkey := hy.choose_spec
  -- Negation is a homeomorphism preserving nhdsWithin 0 {0}ᶜ
  have hneg_tendsto : Filter.Tendsto (fun t : ℝ => -t) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    have h_nhds : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
      simpa using continuous_neg.tendsto (0 : ℝ)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact h_nhds.mono_left nhdsWithin_le_nhds
    · apply Filter.mem_inf_of_right
      rw [Filter.mem_principal]
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      exact neg_ne_zero.mpr ht
  exact hkey.comp hneg_tendsto

private theorem stoneGenerator_isSymmetric (U : StronglyContUnitaryGroup H) :
    ∀ (x y : stoneGeneratorDomain U),
      @inner ℂ H _ (stoneGenerator U x) (y : H) =
      @inner ℂ H _ (x : H) (stoneGenerator U y) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [stoneGenerator]
  -- We show both sides are limits of the same filter
  -- ⟪Ax, y⟫ = lim_{t→0} ⟪F(t,x), y⟫
  have hlim_left : Filter.Tendsto
      (fun t : ℝ => @inner ℂ H _ ((t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x))) y)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (@inner ℂ H _ hx.choose y)) :=
    Filter.Tendsto.inner hx.choose_spec tendsto_const_nhds
  -- ⟪x, Ay⟫ = lim_{t→0} ⟪x, F(-t,y)⟫  (using composition with negation)
  have hlim_right : Filter.Tendsto
      (fun t : ℝ => @inner ℂ H _ x (((-t : ℝ) : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun (-t) y : H) - y))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (@inner ℂ H _ x hy.choose)) :=
    Filter.Tendsto.inner tendsto_const_nhds (stoneGenerator_tendsto_neg U y hy)
  -- The two sequences are pointwise equal by stoneGenerator_inner_swap
  have heq : ∀ t : ℝ,
      @inner ℂ H _ ((t : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun t x : H) - x))) y =
      @inner ℂ H _ x (((-t : ℝ) : ℂ)⁻¹ • (Complex.I⁻¹ • ((U.toFun (-t) y : H) - y))) :=
    stoneGenerator_inner_swap U x y
  -- By uniqueness of limits
  have hlim_left' := hlim_left.congr (fun t => heq t)
  exact tendsto_nhds_unique hlim_left' hlim_right

/-- For any `y : H`, there exists `x ∈ dom(A)` such that `(A + iI)x = y`.

The resolvent is constructed via the integral `R(i)y = -i ∫₀^∞ e^{-t} U(t)y dt`.
This integral converges in `H` because `‖e^{-t} U(t)y‖ = e^{-t} ‖y‖` (U is unitary).
One shows `R(i)y ∈ dom(A)` and `(A + iI)(R(i)y) = y` by differentiating under the
integral sign.

This step requires Bochner integration of Hilbert-space-valued functions, which
is available in Mathlib but connecting it to the generator limit definition
requires substantial work.

This is step 1 of proving surjectivity. The map is defined via
`R(i)y = -i ∫₀^∞ e^{-t} U(t)y dt`. -/
noncomputable def resolvent_addI (U : StronglyContUnitaryGroup H) (y : H) : H :=
  (-Complex.I) • ∫ (t : ℝ) in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • (U.toFun t y)

private theorem resolvent_addI_integrable (U : StronglyContUnitaryGroup H) (y : H) :
    IntegrableOn (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun t y)) (Ioi 0) := by
  have h_norm_eq : ∀ t : ℝ, ‖(Real.exp (-t) : ℂ) • (U.toFun t y)‖ = Real.exp (-t) * ‖y‖ := by
    intro t
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    have hUy : ‖U.toFun t y‖ = ‖y‖ := StronglyContUnitaryGroup.norm_apply U t y
    rw [hUy]
  -- Base exponential function is integrable
  have hexp : IntegrableOn (fun (t : ℝ) => Real.exp (-t) * ‖y‖) (Ioi 0) := by
    apply Integrable.mul_const
    have h1 : IntegrableOn (fun (t : ℝ) => Real.exp (-(1 : ℝ) * t)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by norm_num)
    exact IntegrableOn.congr_fun h1 (by intro t _; simp only [neg_mul, one_mul]) measurableSet_Ioi

  -- Strong measurability of the integrand via continuity
  have h1 : Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  have h2 : Continuous (fun t : ℝ => U.toFun t y) := U.stronglyContinuous y
  have h3 : Continuous (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun t y)) :=
    h1.smul h2
  have hmeas : AEStronglyMeasurable (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun t y)) (volume.restrict (Ioi 0)) :=
    h3.aestronglyMeasurable

  -- Apply the bound theorem
  apply Integrable.mono' hexp hmeas
  filter_upwards [] with t
  rw [h_norm_eq]


private lemma set_integral_shift {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace ℂ H]
    (f : ℝ → H) (s : ℝ) :
    ∫ (t : ℝ) in Ioi 0, f (t + s) = ∫ (u : ℝ) in Ioi s, f u := by
  have h_ind : (fun t => (Ioi 0).indicator (fun x => f (x + s)) t) =
               (fun t => (Ioi s).indicator f (t + s)) := by
    ext t
    by_cases ht : t ∈ Ioi 0
    · have ht' : t + s ∈ Ioi s := by dsimp [Ioi] at ht ⊢; linarith
      simp [ht, ht']
    · have ht' : t + s ∉ Ioi s := by dsimp [Ioi] at ht ⊢; linarith
      simp [ht, ht']
  calc ∫ (t : ℝ) in Ioi 0, f (t + s)
    _ = ∫ t : ℝ, (Ioi 0).indicator (fun x => f (x + s)) t := by rw [integral_indicator measurableSet_Ioi]
    _ = ∫ t : ℝ, (Ioi s).indicator f (t + s) := by rw [h_ind]
    _ = ∫ u : ℝ, (Ioi s).indicator f u := integral_add_right_eq_self (fun x => (Ioi s).indicator f x) s
    _ = ∫ u : ℝ in Ioi s, f u := by rw [integral_indicator measurableSet_Ioi]

private lemma test_resolvent_addI_limit (U : StronglyContUnitaryGroup H) (y : H) :
    let x_val := resolvent_addI U y
    Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • Complex.I⁻¹ • (U.toFun s x_val - x_val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (y - Complex.I • x_val)) := by
  intro x_val
  -- 1) Commute U(s) inside x_val = i \int_Ioi(0) e^{-t}U(t)y dt
  have hU_comm_s : ∀ s : ℝ, U.toFun s x_val = -Complex.I • ∫ (t : ℝ) in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • (U.toFun (s + t) y) := by
    intro s
    dsimp only [x_val]
    rw [resolvent_addI]
    have hins : IntegrableOn (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun t y)) (Ioi 0) :=
      resolvent_addI_integrable U y
    calc
      (U.toFun s : H →L[ℂ] H) (-Complex.I • ∫ (t : ℝ) in Ioi 0, (Real.exp (-t) : ℂ) • (U.toFun t y))
        = -Complex.I • (U.toFun s : H →L[ℂ] H) (∫ (t : ℝ) in Ioi 0, (Real.exp (-t) : ℂ) • (U.toFun t y)) :=
          (U.toFun s : H →L[ℂ] H).map_smul (-Complex.I) _
      _ = -Complex.I • ∫ (t : ℝ) in Ioi 0, (U.toFun s : H →L[ℂ] H) ((Real.exp (-t) : ℂ) • (U.toFun t y)) := by
          rw [(U.toFun s : H →L[ℂ] H).integral_comp_comm hins]
      _ = -Complex.I • ∫ (t : ℝ) in Ioi 0, (Real.exp (-t) : ℂ) • (U.toFun (s + t) y) := by
          congr 1
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          dsimp only
          rw [(U.toFun s : H →L[ℂ] H).map_smul, ← ContinuousLinearMap.mul_apply, ← U.map_add s t]

  -- 2) Factor $e^s$ out and Map Integration Bound $\int_0^\infty f(t+s) = \int_s^\infty f(u)$
  have h_shift : ∀ s : ℝ,
      ∫ (t : ℝ) in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • (U.toFun (s + t) y) ∂volume =
      (Real.exp s : ℂ) • ∫ (u : ℝ) in Ioi s, (Real.exp (-u) : ℂ) • (U.toFun u y) ∂volume := by
    intro s
    have h_pull : ∫ (t : ℝ) in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • (U.toFun (s + t) y) =
                  ∫ (t : ℝ) in Ioi (0 : ℝ), (Real.exp s : ℂ) • (Real.exp (-(t + s)) : ℂ) • (U.toFun (t + s) y) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [add_comm s t]
      rw [← mul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
      have h_eq : -t = s + -(t + s) := by ring
      rw [h_eq]
    rw [h_pull]
    rw [integral_smul]
    have h_subst := set_integral_shift (fun u => (Real.exp (-u) : ℂ) • (U.toFun u y)) s
    rw [h_subst]
  -- 3) Substitute \int_s^\infty = \int_0^\infty - \int_0^s -> split Ioi 0 into Ioc 0 s \cup Ioi s natively on e^{-u} U(u)y
  have h_split : ∀ s : ℝ, 0 < s →
      ∫ (u : ℝ) in Ioi (0 : ℝ), (Real.exp (-u) : ℂ) • (U.toFun u y) ∂volume =
      ∫ (u : ℝ) in Ioc (0 : ℝ) s, (Real.exp (-u) : ℂ) • (U.toFun u y) ∂volume +
      ∫ (u : ℝ) in Ioi s, (Real.exp (-u) : ℂ) • (U.toFun u y) ∂volume := by
    intro s hs
    have h_union : Ioi (0 : ℝ) = Ioc (0 : ℝ) s ∪ Ioi s := (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hs)).symm
    rw [h_union]
    have h_disj : Disjoint (Ioc (0 : ℝ) s) (Ioi s) := by
      rw [Set.disjoint_iff]
      intro x hx
      have h1 : x ≤ s := hx.1.2
      have h2 : s < x := hx.2
      linarith
    have h_meas : MeasurableSet (Ioi s) := measurableSet_Ioi
    have h_int1 : IntegrableOn (fun (u : ℝ) => (Real.exp (-u) : ℂ) • (U.toFun u y)) (Ioc (0 : ℝ) s) := sorry
    have h_int2 : IntegrableOn (fun (u : ℝ) => (Real.exp (-u) : ℂ) • (U.toFun u y)) (Ioi s) := sorry
    exact setIntegral_union h_disj h_meas h_int1 h_int2

  -- 4) Difference Equation: U(s)x_val - x_val
  have h_diff : ∀ s : ℝ, 0 < s →
      U.toFun s x_val - x_val =
      ((Real.exp s : ℂ) - 1) • x_val + (Complex.I * (Real.exp s : ℂ)) • ∫ (u : ℝ) in Ioc (0 : ℝ) s, (Real.exp (-u) : ℂ) • (U.toFun u y) ∂volume := by
    intro s hs
    sorry

  -- 5) Continuous Differentiability Limit (FTC)
  sorry

private theorem stoneGenerator_addI_surjective (U : StronglyContUnitaryGroup H) (y : H) :
    ∃ x : stoneGeneratorDomain U,
      (stoneGenerator U x : H) + Complex.I • (x : H) = y := by
  let x_val := resolvent_addI U y
  have h_int : IntegrableOn (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun t y)) (Ioi 0) :=
    resolvent_addI_integrable U y

  -- The domain of the Stone generator A is defined via the limit:
  -- Tendsto (t ↦ (t⁻¹ * I⁻¹) (U(t)x - x)) (𝓝[≠] 0) Ax
  have h_limit : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • Complex.I⁻¹ • (U.toFun s x_val - x_val))
    (𝓝[≠] (0 : ℝ)) (𝓝 (y - Complex.I • x_val)) := by
    exact test_resolvent_addI_limit U y

  have h_mem : x_val ∈ stoneGeneratorDomain U := by
    -- By definition, x ∈ dom(A) iff the limit of (U(s)x - x)/s exists at s=0
    -- Our h_limit explicitly proves this limit exists and equals y - I*x_val
    exact ⟨y - Complex.I • x_val, h_limit⟩

  use ⟨x_val, h_mem⟩
  -- Now we must show A(x_val) + i x_val = y
  -- We extract the limit evaluating A(x) from h_limit via the generator definition.
  have hA : (stoneGenerator U ⟨x_val, h_mem⟩ : H) = y - Complex.I • x_val :=
    tendsto_nhds_unique h_mem.choose_spec h_limit
  erw [hA]
  -- Algebraic simplification: (y - i x) + i x = y
  rw [sub_add_cancel]

/-- Range of (A + iI) is dense, where A is the Stone generator.
This follows from `stoneGenerator_addI_surjective`, which shows the range is all of H. -/
private theorem stoneGenerator_addI_range_dense (U : StronglyContUnitaryGroup H) :
    Dense (Set.range (fun x : stoneGeneratorDomain U =>
      (stoneGenerator U x : H) + Complex.I • (x : H))) := by
  -- The range is actually all of H (surjective), hence certainly dense
  have hsurj : Function.Surjective (fun x : stoneGeneratorDomain U =>
      (stoneGenerator U x : H) + Complex.I • (x : H)) := by
    intro y
    exact stoneGenerator_addI_surjective U y
  exact Function.Surjective.denseRange hsurj

/-- For any `y : H`, there exists `x ∈ dom(A)` such that `(A - iI)x = y`.
The resolvent is constructed via `R(-i)y = i ∫₀^∞ e^{-t} U(-t)y dt`. -/
noncomputable def resolvent_subI (U : StronglyContUnitaryGroup H) (y : H) : H :=
  Complex.I • ∫ (t : ℝ) in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • (U.toFun (-t) y)

private theorem resolvent_subI_integrable (U : StronglyContUnitaryGroup H) (y : H) :
    IntegrableOn (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun (-t) y)) (Ioi 0) := by
  have h_norm_eq : ∀ t : ℝ, ‖(Real.exp (-t) : ℂ) • (U.toFun (-t) y)‖ = Real.exp (-t) * ‖y‖ := by
    intro t
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    have hUy : ‖U.toFun (-t) y‖ = ‖y‖ := StronglyContUnitaryGroup.norm_apply U (-t) y
    rw [hUy]
  have hexp : IntegrableOn (fun (t : ℝ) => Real.exp (-t) * ‖y‖) (Ioi 0) := by
    apply Integrable.mul_const
    have h1 : IntegrableOn (fun (t : ℝ) => Real.exp (-(1 : ℝ) * t)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by norm_num)
    exact IntegrableOn.congr_fun h1 (by intro t _; simp only [neg_mul, one_mul]) measurableSet_Ioi
  have h1 : Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  have h2 : Continuous (fun t : ℝ => U.toFun (-t) y) := (U.stronglyContinuous y).comp continuous_neg
  have h3 : Continuous (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun (-t) y)) :=
    h1.smul h2
  have hmeas : AEStronglyMeasurable (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun (-t) y)) (volume.restrict (Ioi 0)) :=
    h3.aestronglyMeasurable
  apply Integrable.mono' hexp hmeas
  filter_upwards [] with t
  rw [h_norm_eq]

private theorem stoneGenerator_subI_surjective (U : StronglyContUnitaryGroup H) (y : H) :
    ∃ x : stoneGeneratorDomain U,
      (stoneGenerator U x : H) - Complex.I • (x : H) = y := by
  let x_val := resolvent_subI U y
  have h_int : IntegrableOn (fun (t : ℝ) => (Real.exp (-t) : ℂ) • (U.toFun (-t) y)) (Ioi 0) :=
    resolvent_subI_integrable U y

  have h_limit : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • Complex.I⁻¹ • (U.toFun s x_val - x_val))
    (𝓝[≠] (0 : ℝ)) (𝓝 (y + Complex.I • x_val)) := by
    sorry

  have h_mem : x_val ∈ stoneGeneratorDomain U := by
    exact ⟨y + Complex.I • x_val, h_limit⟩

  use ⟨x_val, h_mem⟩
  have hA : (stoneGenerator U ⟨x_val, h_mem⟩ : H) = y + Complex.I • x_val :=
    tendsto_nhds_unique h_mem.choose_spec h_limit
  erw [hA]
  rw [add_sub_cancel_right]

/-- The Stone generator is symmetric in the sense of `IsFormalAdjoint`. -/
private theorem stoneGenerator_isFormalAdjoint (U : StronglyContUnitaryGroup H) :
    (stoneGenerator U).IsFormalAdjoint (stoneGenerator U) := by
  intro x y
  exact stoneGenerator_isSymmetric U x y

/-- The Stone generator is self-adjoint.

Proof outline: A is symmetric (`stoneGenerator_isSymmetric`) and the maps
`(A + iI)` and `(A - iI)` are both surjective (`stoneGenerator_addI_surjective`,
`stoneGenerator_subI_surjective`).

A symmetric operator with surjective `(A ± iI)` is self-adjoint:
- Symmetry gives `A ≤ A†` (i.e., dom(A) ⊆ dom(A†) and they agree on dom(A)).
- Take any `y ∈ dom(A†)`. We need to show `y ∈ dom(A)`.
- Let `w = A†y + i·y`. By surjectivity of `(A + iI)`, there exists `x ∈ dom(A)`
  with `Ax + i·x = w = A†y + i·y`.
- For any `v ∈ dom(A)`:
  `⟨(A-iI)v, x - y⟩ = ⟨Av, x⟩ - ⟨iv, x⟩ - ⟨Av, y⟩ + ⟨iv, y⟩`
  `= (⟨v,Ax⟩ + i⟨v,x⟩) - (⟨v,A†y⟩ + i⟨v,y⟩)`  (symmetry + adjoint + conj)
  `= ⟨v, Ax+ix⟩ - ⟨v, A†y+iy⟩ = 0`           (since Ax+ix = A†y+iy)
- Since range(A-iI) = H, x - y ⊥ H, hence x = y ∈ dom(A). -/
private theorem stoneGenerator_isSelfAdjoint (U : StronglyContUnitaryGroup H) :
    IsSelfAdjoint (stoneGenerator U) := by
  -- Self-adjoint means A.adjoint = A
  rw [LinearPMap.isSelfAdjoint_def]
  set A := stoneGenerator U with hA_def
  have hd : Dense (A.domain : Set H) := stoneGeneratorDomain_dense U
  have hsymm := stoneGenerator_isFormalAdjoint U
  -- Symmetry gives A ≤ A.adjoint
  have hle : A ≤ A.adjoint := hsymm.le_adjoint hd
  -- We show dom(A.adjoint) ≤ dom(A), giving domain equality, hence A.adjoint = A
  have hdom : A.adjoint.domain ≤ A.domain := by
    intro y hy_adj
    -- By surjectivity of (A+iI), find x ∈ dom(A) with (A+iI)x = A.adjoint(y) + iy
    obtain ⟨x, hx_eq⟩ := stoneGenerator_addI_surjective U
      (A.adjoint ⟨y, hy_adj⟩ + Complex.I • y)
    -- x - y ∈ dom(A†), and (A† + iI)(x - y) = 0, so A†(x-y) = -i(x-y)
    -- Key: ⟪(A-iI)v, x-y⟫ = 0 for all v ∈ dom(A)
    -- Since (A-iI) is surjective, x - y ⊥ H, hence x = y
    have horth_all : ∀ w : H, @inner ℂ H _ w ((x : H) - y) = 0 := by
      intro w
      -- Write w = (A-iI)v for some v ∈ dom(A)
      obtain ⟨v, hv⟩ := stoneGenerator_subI_surjective U w
      rw [← hv]
      -- We need ⟪Av - iv, x - y⟫ = 0
      -- ⟪Av, x-y⟫ = ⟪Av, x⟫ - ⟪Av, y⟫
      --   = ⟪v, Ax⟫ - ⟪v, A†y⟫  (symmetry for x, adjoint for y)
      -- ⟪iv, x-y⟫ = (-i)(⟪v, x⟫ - ⟪v, y⟫) = (-i)⟪v, x-y⟫
      -- So ⟪(A-iI)v, x-y⟫ = ⟪v, Ax⟫ - ⟪v, A†y⟫ - (-i)⟪v, x-y⟫
      --   = ⟪v, Ax⟫ - ⟪v, A†y⟫ + i⟪v, x-y⟫
      --   = ⟪v, Ax⟫ - ⟪v, A†y⟫ + i⟪v, x⟫ - i⟪v, y⟫
      --   = (⟪v, Ax⟫ + i⟪v, x⟫) - (⟪v, A†y⟫ + i⟪v, y⟫)
      --   = ⟪v, Ax + ix⟫ - ⟪v, A†y + iy⟫
      --   = 0  (since Ax + ix = A†y + iy by hx_eq)
      rw [inner_sub_right, inner_sub_left, inner_sub_left]
      -- Goal: (⟪Av, x⟫ - ⟪iv, x⟫) - (⟪Av, y⟫ - ⟪iv, y⟫) = 0
      -- Use symmetry: ⟪Av, x⟫ = ⟪v, Ax⟫
      have hsymm_vx : @inner ℂ H _ (A v : H) (x : H) =
          @inner ℂ H _ (v : H) (A x : H) :=
        stoneGenerator_isSymmetric U v x
      -- Use adjoint: ⟪Av, y⟫ = ⟪v, A†y⟫
      have hadj_vy : @inner ℂ H _ (A v : H) y =
          @inner ℂ H _ (v : H) (A.adjoint ⟨y, hy_adj⟩) := by
        have h := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy_adj⟩ v
        rw [← inner_conj_symm (A v : H) y, ← inner_conj_symm (v : H) (A.adjoint ⟨y, hy_adj⟩),
            h.symm]
      -- Use inner_smul_left: ⟪iv, z⟫ = (-i)⟪v, z⟫
      have hsmul_x : @inner ℂ H _ (Complex.I • (v : H)) (x : H) =
          -Complex.I * @inner ℂ H _ (v : H) (x : H) := by
        rw [inner_smul_left, Complex.conj_I]
      have hsmul_y : @inner ℂ H _ (Complex.I • (v : H)) y =
          -Complex.I * @inner ℂ H _ (v : H) y := by
        rw [inner_smul_left, Complex.conj_I]
      -- From hx_eq: ⟪v, Ax + ix⟫ = ⟪v, A†y + iy⟫
      have hxeq' : @inner ℂ H _ (v : H) ((A x : H) +
          Complex.I • (x : H)) =
          @inner ℂ H _ (v : H) (A.adjoint ⟨y, hy_adj⟩ +
          Complex.I • y) := by
        rw [hx_eq]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right] at hxeq'
      -- Now substitute and show it's zero
      rw [hsymm_vx, hadj_vy, hsmul_x, hsmul_y]
      -- Goal should be: ⟪v, Ax⟫ - ⟪v, A†y⟫ - (-i * ⟪v, x⟫) + (-i * ⟪v, y⟫) = 0
      -- = ⟪v, Ax⟫ - ⟪v, A†y⟫ + i⟪v, x⟫ - i⟪v, y⟫
      -- = (⟪v, Ax⟫ + i⟪v, x⟫) - (⟪v, A†y⟫ + i⟪v, y⟫)
      -- = ⟪v, Ax + ix⟫ - ⟪v, A†y + iy⟫ = 0 by hxeq'
      linear_combination hxeq'
    have hxy : (x : H) = y := by
      rw [← sub_eq_zero]
      exact (inner_self_eq_zero (𝕜 := ℂ)).mp (horth_all _)
    exact hxy ▸ x.2
  -- Domain equality from both inclusions
  have hdom_eq : A.adjoint.domain = A.domain := le_antisymm hdom hle.1
  -- A ≤ A.adjoint with domain equality implies A = A.adjoint
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdom_eq.symm).symm

/-- **Stone's theorem (unbounded forward direction)**: every C₀-unitary group
has a self-adjoint generator. -/
theorem stone_theorem_unbounded (U : StronglyContUnitaryGroup H) :
    ∃ (A : LinearPMap ℂ H H), IsSelfAdjoint A ∧
      Dense (A.domain : Set H) := by
  refine ⟨stoneGenerator U, stoneGenerator_isSelfAdjoint U, ?_⟩
  exact (stoneGenerator_isSelfAdjoint U).dense_domain

end
