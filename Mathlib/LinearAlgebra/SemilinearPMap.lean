/-
Copyright (c) 2025 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Partially defined semilinear and conjugate-linear maps

A `ConjLinearPMap 𝕜 E F` is a conjugate-linear (antilinear) map from a submodule of `E`
to `F`, where `E` and `F` are modules over a star-ring `𝕜`. This generalises `LinearPMap`
to the conjugate-linear setting, which is needed for the Tomita–Takesaki modular theory
of von Neumann algebras.

The Tomita operator `S : aΩ ↦ a*Ω` is an unbounded, closable, *antilinear* operator on
a Hilbert space. Mathlib's `LinearPMap` only handles linear maps, so we introduce
`ConjLinearPMap` for the conjugate-linear case.

## Design notes

The graph of a σ-semilinear map (for nontrivial σ) is *not* a submodule over the
original scalar ring, because `f(r • x) = σ(r) • f(x) ≠ r • f(x)` in general.
This means we cannot directly reuse the `Submodule.topologicalClosure` machinery from
`LinearPMap` for the closure theory.

However, when `𝕜` is an `RCLike` field and `σ = starRingEnd 𝕜` (complex conjugation),
the graph *is* a submodule over `ℝ` (via `restrictScalars`), because conjugation is
`ℝ`-linear. We exploit this for the closability theory by viewing the graph as a real
submodule.

An alternative approach would be to generalise `LinearPMap` to carry a ring
homomorphism σ (a "SemilinearPMap"). We leave this as future work; the present file
provides the minimal infrastructure needed for Tomita–Takesaki theory.

## Main definitions

* `ConjLinearPMap 𝕜 E F`: a conjugate-linear partially defined map, consisting of a
  `Submodule 𝕜 E` (the domain) and a conjugate-linear map
  `domain →ₛₗ[starRingEnd 𝕜] F`.
* `ConjLinearPMap.graph`: the graph as a set in `E × F`.
* `ConjLinearPMap.graphSubmoduleReal`: the graph as a submodule over `ℝ`
  (for `RCLike 𝕜`).
* `ConjLinearPMap.IsClosed`: the operator is closed iff its graph is closed.
* `ConjLinearPMap.IsClosable`: the operator is closable iff the closure of its graph
  is the graph of a conjugate-linear operator.

## References

* [O. Bratteli, D.W. Robinson,
  *Operator Algebras and Quantum Statistical Mechanics 1*]
* [M. Takesaki, *Theory of Operator Algebras I*]

## Tags

Unbounded operators, antilinear, conjugate-linear, Tomita–Takesaki, modular theory
-/

noncomputable section

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A `ConjLinearPMap 𝕜 E F` is a conjugate-linear map from a submodule of `E` to `F`.
That is, it consists of a domain `D ≤ E` (a `𝕜`-submodule) together with a
`starRingEnd 𝕜`-semilinear map from `D` to `F`. -/
structure ConjLinearPMap (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] where
  /-- The domain of the partially defined conjugate-linear map. -/
  domain : Submodule 𝕜 E
  /-- The conjugate-linear map on the domain. -/
  toFun : domain →ₛₗ[starRingEnd 𝕜] F

namespace ConjLinearPMap

/-! ### Basic API -/

section Basic

variable (f : ConjLinearPMap 𝕜 E F)

/-- Coercion to a function on the domain. -/
@[coe]
def toFun' : f.domain → F := f.toFun

instance : CoeFun (ConjLinearPMap 𝕜 E F) fun f => f.domain → F :=
  ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (x : f.domain) : f.toFun x = f x :=
  rfl

theorem map_zero : f 0 = 0 :=
  f.toFun.map_zero

theorem map_add (x y : f.domain) : f (x + y) = f x + f y :=
  f.toFun.map_add x y

theorem map_neg (x : f.domain) : f (-x) = -f x :=
  f.toFun.map_neg x

theorem map_sub (x y : f.domain) : f (x - y) = f x - f y :=
  f.toFun.map_sub x y

/-- Conjugate-linearity: `f(c • x) = conj(c) • f(x)`. -/
theorem map_smul (c : 𝕜) (x : f.domain) :
    f (c • x) = starRingEnd 𝕜 c • f x :=
  f.toFun.map_smulₛₗ c x

/-- Extensionality for `ConjLinearPMap`. -/
@[ext (iff := false)]
theorem ext {f g : ConjLinearPMap 𝕜 E F}
    (h : f.domain = g.domain)
    (h' : ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄,
      f ⟨x, hf⟩ = g ⟨x, hg⟩) : f = g := by
  rcases f with ⟨f_dom, f_fun⟩
  rcases g with ⟨g_dom, g_fun⟩
  obtain rfl : f_dom = g_dom := h
  congr 1
  ext ⟨x, hx⟩
  exact h' (hf := hx) (hg := hx)

/-- The ordering: `f ≤ g` iff `g` extends `f`. -/
instance : LE (ConjLinearPMap 𝕜 E F) :=
  ⟨fun f g => f.domain ≤ g.domain ∧
    ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄,
      (x : E) = (y : E) → f x = g y⟩

end Basic

/-! ### Graph -/

section Graph

variable (f : ConjLinearPMap 𝕜 E F)

/-- The graph of a `ConjLinearPMap` as a set in `E × F`. -/
def graph : Set (E × F) :=
  { p | ∃ x : f.domain, (↑x : E) = p.1 ∧ f x = p.2 }

theorem mem_graph_iff {p : E × F} :
    p ∈ f.graph ↔
      ∃ x : f.domain, (↑x : E) = p.1 ∧ f x = p.2 :=
  Iff.rfl

/-- The tuple `(x, f x)` is in the graph. -/
theorem mem_graph (x : f.domain) :
    ((↑x : E), f x) ∈ f.graph :=
  ⟨x, rfl, rfl⟩

/-- If `(x, y₁)` and `(x, y₂)` are both in the graph, then `y₁ = y₂`. -/
theorem graph_fst_eq_imp_snd_eq {x : E} {y₁ y₂ : F}
    (h₁ : (x, y₁) ∈ f.graph)
    (h₂ : (x, y₂) ∈ f.graph) : y₁ = y₂ := by
  obtain ⟨a₁, ha₁, rfl⟩ := h₁
  obtain ⟨a₂, ha₂, rfl⟩ := h₂
  have : a₁ = a₂ := Subtype.ext (ha₁.trans ha₂.symm)
  rw [this]

/-- If `(0, y)` is in the graph, then `y = 0`. -/
theorem graph_fst_eq_zero_snd {y : F}
    (h : (0, y) ∈ f.graph) : y = 0 := by
  obtain ⟨a, ha, rfl⟩ := h
  have : a = 0 := Subtype.ext ha
  rw [this, f.map_zero]

theorem graph_zero_mem : (0, 0) ∈ f.graph :=
  ⟨0, rfl, f.map_zero⟩

theorem graph_add_mem {p q : E × F}
    (hp : p ∈ f.graph) (hq : q ∈ f.graph) :
    p + q ∈ f.graph := by
  obtain ⟨a, ha₁, ha₂⟩ := hp
  obtain ⟨b, hb₁, hb₂⟩ := hq
  refine ⟨a + b, ?_, ?_⟩
  · simp [ha₁, hb₁]
  · simp [f.map_add, ha₂, hb₂]

theorem graph_neg_mem {p : E × F}
    (hp : p ∈ f.graph) : -p ∈ f.graph := by
  obtain ⟨a, ha₁, ha₂⟩ := hp
  refine ⟨-a, ?_, ?_⟩
  · simp [ha₁]
  · simp [f.map_neg, ha₂]

/-- The graph is an `AddSubgroup` of `E × F`. -/
def graphAddSubgroup : AddSubgroup (E × F) where
  carrier := f.graph
  zero_mem' := f.graph_zero_mem
  add_mem' := f.graph_add_mem
  neg_mem' := f.graph_neg_mem

/-- The graph as a submodule over `ℝ`.

Conjugate-linear maps are `ℝ`-linear (since `starRingEnd` is the identity on
real scalars). Therefore the graph, while not a `𝕜`-submodule, is an
`ℝ`-submodule. This enables `Submodule.topologicalClosure` for closability. -/
def graphSubmoduleReal :
    letI : Module ℝ E := Module.compHom E (algebraMap ℝ 𝕜)
    letI : Module ℝ F := Module.compHom F (algebraMap ℝ 𝕜)
    Submodule ℝ (E × F) :=
  letI : Module ℝ E := Module.compHom E (algebraMap ℝ 𝕜)
  letI : Module ℝ F := Module.compHom F (algebraMap ℝ 𝕜)
  { carrier := f.graph
    zero_mem' := f.graph_zero_mem
    add_mem' := f.graph_add_mem
    smul_mem' := fun r p hp => by
      -- For r : ℝ and (x, y) ∈ graph (i.e. y = f x), show r • (x, y) ∈ graph.
      -- The ℝ-action is r • z = algebraMap ℝ 𝕜 r • z = (r : 𝕜) • z (definitionally).
      -- Witness: (algebraMap ℝ 𝕜 r) • a ∈ domain, where a witnesses hp.
      -- Then f((r : 𝕜) • a) = starRingEnd 𝕜 (r : 𝕜) • f a
      --                      = (r : 𝕜) • f a   [since conj fixes reals: conj_ofReal]
      --                      = r • f a          [definitional equality of ℝ-action]
      obtain ⟨a, ha₁, ha₂⟩ := hp
      refine ⟨(algebraMap ℝ 𝕜 r) • a, ?_, ?_⟩
      · -- ↑((algebraMap ℝ 𝕜 r) • a) = r • p.1
        -- Both sides equal (algebraMap ℝ 𝕜 r) • ↑a definitionally,
        -- since Module ℝ E := Module.compHom E (algebraMap ℝ 𝕜) makes r • x = algebraMap ℝ 𝕜 r • x.
        show (algebraMap ℝ 𝕜 r) • (↑a : E) = r • p.1
        rw [← ha₁]; rfl
      · -- f ((algebraMap ℝ 𝕜 r) • a) = r • p.2
        -- f is semilinear: f((r : 𝕜) • a) = starRingEnd 𝕜 (r : 𝕜) • f a = (r : 𝕜) • f a
        -- Then (r : 𝕜) • f a = r • f a = r • p.2 definitionally.
        rw [f.map_smul, starRingEnd_apply, RCLike.star_def,
            RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, ← RCLike.algebraMap_eq_ofReal, ha₂]
        rfl }

end Graph

/-! ### Closed and closable operators -/

section Closable

variable [CompleteSpace E] [CompleteSpace F]

/-- A conjugate-linear operator is closed iff its graph is closed in `E × F`. -/
def IsClosed (f : ConjLinearPMap 𝕜 E F) : Prop :=
  _root_.IsClosed (f.graph : Set (E × F))

/-- A conjugate-linear operator is closable iff the closure of its graph is the
graph of some conjugate-linear operator. -/
def IsClosable (f : ConjLinearPMap 𝕜 E F) : Prop :=
  ∃ g : ConjLinearPMap 𝕜 E F, closure f.graph = g.graph

/-- A closed operator is closable. -/
theorem IsClosed.isClosable {f : ConjLinearPMap 𝕜 E F}
    (hf : f.IsClosed) : f.IsClosable :=
  ⟨f, hf.closure_eq⟩

/-- The graph is contained in the closure of the graph. -/
theorem graph_subset_closure (f : ConjLinearPMap 𝕜 E F) :
    f.graph ⊆ closure f.graph :=
  subset_closure

end Closable

/-! ### Construction helpers -/

section Convert

/-- Shorthand constructor from domain and semilinear map. -/
def mk' (domain : Submodule 𝕜 E)
    (f : domain →ₛₗ[starRingEnd 𝕜] F) : ConjLinearPMap 𝕜 E F :=
  ⟨domain, f⟩

/-- Compose a `LinearPMap` with a conjugate-linear map to get a
`ConjLinearPMap`. If `T` is linear and `J` is conjugate-linear,
then `J ∘ T` is conjugate-linear. -/
def ofLinearPMapComp (T : E →ₗ.[𝕜] F)
    (J : F →ₛₗ[starRingEnd 𝕜] F) :
    ConjLinearPMap 𝕜 E F where
  domain := T.domain
  toFun :=
    { toFun := fun x => J (T x)
      map_add' := fun x y => by
        simp only [T.map_add, map_add]
      map_smulₛₗ' := fun c x => by
        -- J(T(c • x)) = J(c • T(x)) = conj(c) • J(T(x))
        simp only [T.map_smul, J.map_smulₛₗ] }

end Convert

/-! ### Dense domain -/

section Dense

variable (f : ConjLinearPMap 𝕜 E F)

/-- The domain of `f` is dense in `E`. This is required for the
Tomita operator. -/
def IsDenselyDefined : Prop :=
  Dense (f.domain : Set E)

end Dense

/-! ### Formal adjoint for conjugate-linear operators

For a conjugate-linear operator `S : E →ₛₗ[conj] F` with dense domain, the
formal adjoint `S* : F →ₛₗ[conj] E` satisfies
  `⟪S x, y⟫ = conj ⟪x, S* y⟫`
for all `x ∈ dom(S)` and `y ∈ dom(S*)`.

For the Tomita operator `S`, the polar decomposition `S = J Δ^{1/2}` gives the
modular conjugation `J` (an antiunitary) and the modular operator `Δ`
(a positive self-adjoint operator). The adjoint `S*` is needed to form
`Δ = S* S`.

TODO: Define the adjoint of a `ConjLinearPMap` and prove its basic properties.
The adjoint of an antilinear operator is again antilinear, and the inner product
identity is `⟪S x, y⟫ = conj ⟪x, S† y⟫`.
-/

end ConjLinearPMap
