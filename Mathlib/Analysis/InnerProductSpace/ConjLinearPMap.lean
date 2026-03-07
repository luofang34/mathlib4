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

/-- Forward direction: if f is closable, then (0, y) in the closure of the
graph implies y = 0.

Proof: closable means closure(graph) = graph(g). If (0, y) ∈ graph(g), then
g(0) = y, but g(0) = 0 by conjugate-linearity. -/
theorem isClosable_graph_closure_zero (f : ConjLinearPMap E)
    (hf : f.IsClosable) : ∀ y : E, (0, y) ∈ closure f.graph → y = 0 := by
  intro y hy
  obtain ⟨g, hg⟩ := hf
  rw [hg] at hy
  obtain ⟨x, hx⟩ := hy
  have hx_zero : (x : E) = 0 := (Prod.mk.inj hx).1
  have : x = ⟨0, by rw [← hx_zero]; exact x.2⟩ := Subtype.ext hx_zero
  rw [this] at hx
  have := (Prod.mk.inj hx).2
  rw [← this]
  exact g.map_zero'

/-- Converse: if (0, y) ∈ closure(graph(f)) implies y = 0, then f is closable.

The proof constructs a ConjLinearPMap whose graph equals the closure of f.graph.
The condition ensures the closure is "functional" (single-valued). -/
theorem closable_of_graph_closure_zero (f : ConjLinearPMap E)
    (h : ∀ y : E, (0, y) ∈ closure f.graph → y = 0) : f.IsClosable := by
  sorry
  -- PROOF SKETCH:
  -- 1. Let C = closure(f.graph). C is closed in E × E.
  -- 2. C is an additive subgroup (closure of additive subgroup).
  -- 3. C is "functional": if (x, y₁) ∈ C and (x, y₂) ∈ C, then
  --    (0, y₁ - y₂) ∈ C, so y₁ = y₂ by hypothesis h.
  -- 4. Define domain(g) = π₁(C) as a submodule of E.
  -- 5. Define g(x) = unique y with (x, y) ∈ C.
  -- 6. Show g is conjugate-linear (inherits from f via limits).
  -- 7. Then closure(f.graph) = C = graph(g). ∎

/-- The closability criterion: f is closable iff (0, y) ∈ closure(graph) implies y = 0. -/
theorem isClosable_iff_graph_closure_zero (f : ConjLinearPMap E) :
    f.IsClosable ↔ ∀ y : E, (0, y) ∈ closure f.graph → y = 0 :=
  ⟨f.isClosable_graph_closure_zero, f.closable_of_graph_closure_zero⟩

-- ═══════════════════════════════════════════════════════
-- Involutive operators
-- ═══════════════════════════════════════════════════════

/-- A conjugate-linear partial map is involutive if f(f(x)) = x for all x
in the appropriate domain. This is the key property of the Tomita operator S. -/
def IsInvolutive (f : ConjLinearPMap E) : Prop :=
  ∀ (x : f.domain) (hfx : (f x : E) ∈ f.domain),
    f.toFun ⟨f x, hfx⟩ = (x : E)

/-- A conjugate-linear partial map has a densely defined formal adjoint if
there exists g : ConjLinearPMap E with dense domain such that
⟨f(x), y⟩ = conj(⟨x, g(y)⟩) for all x ∈ dom(f), y ∈ dom(g).

This is the correct general criterion for closability of antilinear operators.
For the Tomita operator S, the formal adjoint is F (Tomita operator for M'). -/
def HasDenselyDefinedFormalAdjoint (f : ConjLinearPMap E) : Prop :=
  ∃ g : ConjLinearPMap E, g.IsDenselyDefined ∧
    ∀ (x : f.domain) (y : g.domain),
      @inner ℂ E _ (f x) (↑y) = starRingEnd ℂ (@inner ℂ E _ (↑x) (g y))

/-- An antilinear operator with a densely defined formal adjoint is closable.

This is the standard closability criterion used in Tomita-Takesaki theory.
The Tomita operator S for M has formal adjoint F (Tomita operator for M'),
which is densely defined because Ω is cyclic for M' (equivalently, separating for M). -/
theorem HasDenselyDefinedFormalAdjoint.isClosable (f : ConjLinearPMap E)
    (hf : f.HasDenselyDefinedFormalAdjoint) : f.IsClosable := by
  rw [isClosable_iff_graph_closure_zero]
  intro y hy
  obtain ⟨g, hg_dense, hg_adj⟩ := hf
  -- Goal: y = 0. Strategy: show ⟨y, w⟩ = 0 for all w in the dense set dom(g).
  apply hg_dense.eq_zero_of_inner_left (𝕜 := ℂ)
  intro w hw
  -- Show ⟨y, w⟩ = 0. Suffices to show ‖⟨y, w⟩‖ ≤ ε for all ε > 0.
  rw [← norm_eq_zero]
  apply le_antisymm _ (norm_nonneg _)
  rw [← not_lt]
  intro h_pos
  -- (0, y) ∈ closure(graph) gives approximation
  set C := ‖w‖ + ‖g.toFun ⟨w, hw⟩‖ + 1 with hC_def
  have hC_pos : C > 0 := by positivity
  have hε : ‖@inner ℂ E _ y w‖ / C > 0 := div_pos h_pos hC_pos
  obtain ⟨p, hp_mem, hp_dist⟩ := Metric.mem_closure_iff.mp hy (‖@inner ℂ E _ y w‖ / C) hε
  obtain ⟨x, hx⟩ := hp_mem
  -- p = (↑x, f(x)) and dist p (0, y) < ε
  have hx1 : p.1 = (↑x : E) := by rw [← hx]
  have hx2 : p.2 = f.toFun x := by rw [← hx]
  -- ‖↑x‖ < ε and ‖f(x) - y‖ < ε (from product distance = max)
  set ε := ‖@inner ℂ E _ y w‖ / C with hε_def
  have h_x_bound : ‖(↑x : E)‖ < ε := by
    have h1 : dist p.1 (0 : E) ≤ dist p (0, y) := by
      simp only [Prod.dist_eq]; exact le_max_left _ _
    have h2 : ‖(↑x : E)‖ = dist p.1 (0 : E) := by
      rw [hx1]; simp [dist_zero_right]
    rw [h2]; exact lt_of_le_of_lt h1 (by rwa [dist_comm] at hp_dist)
  have h_fx_bound : ‖(f.toFun x : E) - y‖ < ε := by
    have h1 : dist p.2 y ≤ dist p (0, y) := by
      simp only [Prod.dist_eq]; exact le_max_right _ _
    have h2 : ‖(f.toFun x : E) - y‖ = dist p.2 y := by
      rw [hx2]; simp [dist_eq_norm]
    rw [h2]; exact lt_of_le_of_lt h1 (by rwa [dist_comm] at hp_dist)
  -- ⟨y, w⟩ = ⟨y - f(x), w⟩ + ⟨f(x), w⟩
  --        = ⟨y - f(x), w⟩ + conj(⟨↑x, g(w)⟩)  [formal adjoint]
  have h_adj : @inner ℂ E _ (f.toFun x) w =
      starRingEnd ℂ (@inner ℂ E _ (↑x : E) (g.toFun ⟨w, hw⟩)) :=
    hg_adj x ⟨w, hw⟩
  have h_split : @inner ℂ E _ y w = @inner ℂ E _ (y - (f.toFun x : E)) w +
      starRingEnd ℂ (@inner ℂ E _ (↑x : E) (g.toFun ⟨w, hw⟩)) := by
    rw [← h_adj, inner_sub_left, sub_add_cancel]
  -- |⟨y, w⟩| ≤ |⟨y - f(x), w⟩| + |⟨↑x, g(w)⟩|
  have h_bound : ‖@inner ℂ E _ y w‖ ≤
      ‖y - (f.toFun x : E)‖ * ‖w‖ + ‖(↑x : E)‖ * ‖g.toFun ⟨w, hw⟩‖ := by
    rw [h_split]
    calc ‖@inner ℂ E _ (y - (f.toFun x : E)) w +
            starRingEnd ℂ (@inner ℂ E _ (↑x : E) (g.toFun ⟨w, hw⟩))‖
        ≤ ‖@inner ℂ E _ (y - (f.toFun x : E)) w‖ +
            ‖starRingEnd ℂ (@inner ℂ E _ (↑x : E) (g.toFun ⟨w, hw⟩))‖ := norm_add_le _ _
      _ = ‖@inner ℂ E _ (y - (f.toFun x : E)) w‖ +
            ‖@inner ℂ E _ (↑x : E) (g.toFun ⟨w, hw⟩)‖ := by
          rw [RCLike.norm_conj]
      _ ≤ _ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
  -- ‖⟨y, w⟩‖ ≤ ε·‖w‖ + ε·‖g(w)‖ < ε·C = ‖⟨y, w⟩‖, contradiction
  linarith [
    calc ‖y - (f.toFun x : E)‖ * ‖w‖
        ≤ ε * ‖w‖ := by
          rw [norm_sub_rev] at h_fx_bound
          exact mul_le_mul_of_nonneg_right (le_of_lt h_fx_bound) (norm_nonneg _),
    calc ‖(↑x : E)‖ * ‖g.toFun ⟨w, hw⟩‖
        ≤ ε * ‖g.toFun ⟨w, hw⟩‖ := by exact mul_le_mul_of_nonneg_right (le_of_lt h_x_bound) (norm_nonneg _),
    show ε * (‖w‖ + ‖g.toFun ⟨w, hw⟩‖) < ε * C from by
      apply mul_lt_mul_of_pos_left _ hε
      linarith [norm_nonneg w, norm_nonneg (g.toFun ⟨w, hw⟩)],
    show ε * C = ‖@inner ℂ E _ y w‖ from by
      rw [hε_def]; exact div_mul_cancel₀ _ (ne_of_gt hC_pos)]

end ConjLinearPMap

end
