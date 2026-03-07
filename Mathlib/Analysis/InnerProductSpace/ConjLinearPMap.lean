/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Conjugate-Linear Partially Defined Maps

This file defines partially defined conjugate-linear (antilinear) maps on Hilbert spaces,
which are the key ingredient for the Tomita operator S in Tomita-Takesaki theory.

## Main definitions

* `ConjLinearPMap`: A partially defined conjugate-linear map, i.e., a semilinear map
  over `starRingEnd ℂ` defined on a submodule.
* `ConjLinearPMap.IsClosed`: The graph is closed in E × E (as a set).
* `ConjLinearPMap.IsClosable`: The closure of the graph is again a graph.
* `ConjLinearPMap.IsDenselyDefined`: The domain is dense.

## Motivation

In Tomita-Takesaki theory, the Tomita operator S is defined by
  S(aΩ) = a*Ω  for a ∈ M, Ω cyclic+separating.
This is an *antilinear* densely defined operator. Its closure S̄ admits a polar
decomposition S̄ = JΔ^{1/2} where J is anti-unitary and Δ is positive self-adjoint.

Mathlib's `LinearPMap` handles partially defined *linear* maps. This file provides the
analogous infrastructure for the conjugate-linear case needed for TT theory.

## References

* [M. Takesaki, *Theory of Operator Algebras II*][takesaki2003], Chapter VIII
* [O. Bratteli, D.W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*]
  [bratteli_robinson1987], Section 2.5
-/

noncomputable section

open RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A partially defined conjugate-linear map on a Hilbert space.

This consists of a submodule `domain` (over ℂ) and a conjugate-linear map from `domain` to `E`.
The conjugate-linearity means `f(αx) = ᾱ f(x)`.

This is the antilinear analogue of `LinearPMap`. -/
structure ConjLinearPMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The domain of the partially defined conjugate-linear map. -/
  domain : Submodule ℂ E
  /-- The conjugate-linear map itself, as a semilinear map over `starRingEnd ℂ`. -/
  toFun : domain →ₛₗ[starRingEnd ℂ] E

namespace ConjLinearPMap

instance : CoeFun (ConjLinearPMap E) (fun f => f.domain → E) where
  coe f := f.toFun

/-- Two conjugate-linear partial maps are equal if they have the same domain and
agree on it. -/
@[ext]
theorem ext {f g : ConjLinearPMap E} (h_dom : f.domain = g.domain)
    (h_fun : ∀ (x : E) (hf : x ∈ f.domain) (hg : x ∈ g.domain),
      f.toFun ⟨x, hf⟩ = g.toFun ⟨x, hg⟩) : f = g := by
  cases f; cases g
  simp only at h_dom
  subst h_dom
  congr 1
  ext ⟨x, hx⟩
  exact h_fun x hx hx

/-- The graph of a conjugate-linear partial map, as a subset of E × E.
Note: this is NOT a submodule over ℂ (since the map is antilinear),
but it IS an additive subgroup and a submodule over ℝ. -/
def graph (f : ConjLinearPMap E) : Set (E × E) :=
  {p | ∃ (x : f.domain), ((↑x : E), f x) = p}

/-- A conjugate-linear partial map is closed if its graph is closed in E × E. -/
def IsClosed (f : ConjLinearPMap E) : Prop :=
  _root_.IsClosed f.graph

/-- A conjugate-linear partial map is closable if the closure of its graph
is the graph of some conjugate-linear partial map. -/
def IsClosable (f : ConjLinearPMap E) : Prop :=
  ∃ g : ConjLinearPMap E, closure f.graph = g.graph

/-- A conjugate-linear partial map is densely defined if its domain is dense. -/
def IsDenselyDefined (f : ConjLinearPMap E) : Prop :=
  Dense (f.domain : Set E)

/-- Extension (ordering) on conjugate-linear partial maps:
g extends f if domain f ⊆ domain g and they agree on domain f. -/
instance : LE (ConjLinearPMap E) where
  le f g := f.domain ≤ g.domain ∧
    ∀ (x : E) (hf : x ∈ f.domain) (hg : x ∈ g.domain),
      f.toFun ⟨x, hf⟩ = g.toFun ⟨x, hg⟩

-- ═══════════════════════════════════════════════════════
-- Basic Properties
-- ═══════════════════════════════════════════════════════

theorem map_zero' (f : ConjLinearPMap E) : f.toFun ⟨0, f.domain.zero_mem⟩ = 0 :=
  _root_.map_zero f.toFun

theorem map_add' (f : ConjLinearPMap E) (x y : f.domain) :
    f.toFun (x + y) = f.toFun x + f.toFun y :=
  _root_.map_add f.toFun x y

/-- Antilinearity: f(αx) = ᾱ f(x) -/
theorem map_conj_smul (f : ConjLinearPMap E) (c : ℂ) (x : f.domain) :
    f.toFun (c • x) = (starRingEnd ℂ c) • f.toFun x := by
  exact f.toFun.map_smulₛₗ c x

-- ═══════════════════════════════════════════════════════
-- Graph as ℝ-submodule
-- ═══════════════════════════════════════════════════════

/-- The graph of f is closed under addition. -/
theorem graph_add_mem (f : ConjLinearPMap E) {p q : E × E}
    (hp : p ∈ f.graph) (hq : q ∈ f.graph) : p + q ∈ f.graph := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  refine ⟨x + y, ?_⟩
  rw [← hx, ← hy]
  simp only [Submodule.coe_add, Prod.mk_add_mk, map_add']

/-- The graph contains zero. -/
theorem graph_zero_mem (f : ConjLinearPMap E) : (0 : E × E) ∈ f.graph :=
  ⟨⟨0, f.domain.zero_mem⟩, by simp [map_zero']⟩

-- ═══════════════════════════════════════════════════════
-- Closability criterion
-- ═══════════════════════════════════════════════════════

/-- A conjugate-linear partial map is closable if whenever (0, y) is in the
closure of its graph, then y = 0.

This is the standard closability criterion: if x_n → 0 and f(x_n) → y,
then y = 0. -/
theorem isClosable_iff_graph_closure_zero (f : ConjLinearPMap E) :
    f.IsClosable ↔ ∀ y : E, (0, y) ∈ closure f.graph → y = 0 := by
  sorry -- Standard result, proof requires working with closure + graph structure

-- ═══════════════════════════════════════════════════════
-- Involutive operators
-- ═══════════════════════════════════════════════════════

/-- A conjugate-linear partial map is involutive if f(f(x)) = x for all x
in the appropriate domain. This is the key property of the Tomita operator S. -/
def IsInvolutive (f : ConjLinearPMap E) : Prop :=
  ∀ (x : f.domain) (hfx : (f x : E) ∈ f.domain),
    f.toFun ⟨f x, hfx⟩ = (x : E)

/-- If S is involutive and densely defined, then S is closable.

This is a key theorem for Tomita-Takesaki theory: the Tomita operator
S(aΩ) = a*Ω is involutive (since (a*)* = a), and this implies closability. -/
theorem IsInvolutive.isClosable (f : ConjLinearPMap E) (hf : f.IsInvolutive)
    (hd : f.IsDenselyDefined) : f.IsClosable := by
  sorry -- Proof: if (0, y) ∈ closure(graph(f)), use involutivity to show y = 0

end ConjLinearPMap

end
