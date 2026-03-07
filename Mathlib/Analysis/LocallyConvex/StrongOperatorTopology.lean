/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence

/-!
# Strong Operator Topology

The strong operator topology (SOT) on `E →L[𝕜] F` is the coarsest topology making every
evaluation map `A ↦ A x` continuous (as a map `(E →L[𝕜] F) → F` where `F` has its norm
topology). Equivalently, a net (or sequence) `Aᵢ` converges to `A` in the SOT iff `Aᵢ x → A x`
in norm for every `x : E`.

The SOT is strictly finer than the WOT (which only requires weak convergence of `A x`) and
strictly coarser than the norm topology (which requires uniform convergence on bounded sets).

This file defines the SOT as a type synonym of `E →SL[σ] F` modeled closely on
`WeakOperatorTopology.lean`.

## Main definitions

* `ContinuousLinearMapSOT σ E F`: Type synonym for `E →SL[σ] F` with the SOT.
* `ContinuousLinearMap.toSOT`: the coercion `(E →SL[σ] F) → ContinuousLinearMapSOT σ E F`.
* `ContinuousLinearMapSOT.tendsto_iff_forall_tendsto`: characterization of SOT convergence.

## Main results

* `ContinuousLinearMap.continuous_toSOT`: the norm topology is finer than the SOT, i.e., the
  canonical map from `E →SL[σ] F` (with norm topology) to `E →SSOT[σ] F` (with SOT) is
  continuous.
* `ContinuousLinearMapSOT.continuous_apply`: for each `x : E`, the evaluation map
  `A ↦ A x` is SOT-continuous.
* `continuous_sotToWot`: the WOT is coarser than the SOT (when `F` is a normed space).

## Notation

* `E →SSOT[σ] F` for `ContinuousLinearMapSOT σ E F` (semilinear SOT).
* `E →SOT[𝕜] F` for the `𝕜`-linear case.

## Tags

strong operator topology, SOT, operator convergence, pointwise convergence
-/

@[expose] public section

open Topology Filter

/-- The type copy of `E →SL[σ] F` endowed with the strong operator topology, denoted as
`E →SOT[𝕜] F`. The SOT is the coarsest topology making `A ↦ A x` continuous for every `x : E`.
-/
@[irreducible]
def ContinuousLinearMapSOT {𝕜₁ 𝕜₂ : Type*} [Semiring 𝕜₁] [Semiring 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
    (E F : Type*) [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F] :=
  E →SL[σ] F

@[inherit_doc]
notation:25 E " →SSOT[" σ "] " F => ContinuousLinearMapSOT σ E F

@[inherit_doc]
notation:25 E " →SOT[" 𝕜 "] " F => ContinuousLinearMapSOT (RingHom.id 𝕜) E F

namespace ContinuousLinearMapSOT

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
  {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]

/-!
### Basic properties common with `E →L[𝕜] F`

This section copies basic non-topological properties of `E →L[𝕜] F` over to `E →SOT[𝕜] F`, such
as the module structure, `FunLike`, etc.
-/
section Basic

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]

unseal ContinuousLinearMapSOT in
instance instAddCommGroup [IsTopologicalAddGroup F] : AddCommGroup (E →SSOT[σ] F) :=
  inferInstanceAs <| AddCommGroup (E →SL[σ] F)

unseal ContinuousLinearMapSOT in
instance instModule [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] :
    Module 𝕜₂ (E →SSOT[σ] F) :=
  inferInstanceAs <| Module 𝕜₂ (E →SL[σ] F)

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
unseal ContinuousLinearMapSOT in
/-- The linear equivalence that sends a continuous linear map to the type copy endowed with the
strong operator topology. -/
def _root_.ContinuousLinearMap.toSOT :
    (E →SL[σ] F) ≃ₗ[𝕜₂] (E →SSOT[σ] F) :=
  LinearEquiv.refl 𝕜₂ _

instance instFunLike : FunLike (E →SSOT[σ] F) E F where
  coe f := ((ContinuousLinearMap.toSOT σ E F).symm f : E → F)
  coe_injective' := by intro; simp

instance instContinuousLinearMapClass : ContinuousSemilinearMapClass (E →SSOT[σ] F) σ E F where
  map_add f x y := by simp only [DFunLike.coe]; simp
  map_smulₛₗ f r x := by simp only [DFunLike.coe]; simp
  map_continuous f := ContinuousLinearMap.continuous ((ContinuousLinearMap.toSOT σ E F).symm f)

@[simp]
lemma _root_.ContinuousLinearMap.toSOT_apply {A : E →SL[σ] F} {x : E} :
    ((ContinuousLinearMap.toSOT σ E F) A) x = A x := rfl

unseal ContinuousLinearMapSOT in
lemma ext {A B : E →SSOT[σ] F} (h : ∀ x, A x = B x) : A = B := ContinuousLinearMap.ext h

unseal ContinuousLinearMapSOT in
lemma ext_iff {A B : E →SSOT[σ] F} : A = B ↔ ∀ x, A x = B x := ContinuousLinearMap.ext_iff

@[simp] lemma zero_apply (x : E) : (0 : E →SSOT[σ] F) x = 0 := by simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapSOT in
@[simp] lemma add_apply {f g : E →SSOT[σ] F} (x : E) : (f + g) x = f x + g x := by
  simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapSOT in
@[simp] lemma sub_apply {f g : E →SSOT[σ] F} (x : E) : (f - g) x = f x - g x := by
  simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapSOT in
@[simp] lemma neg_apply {f : E →SSOT[σ] F} (x : E) : (-f) x = -(f x) := by
  simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapSOT in
@[simp] lemma smul_apply {f : E →SSOT[σ] F} (c : 𝕜₂) (x : E) : (c • f) x = c • (f x) := by
  simp only [DFunLike.coe]; rfl

end Basic

/-!
### The topology of `E →SOT[𝕜] F`

This section endows `E →SOT[𝕜] F` with the strong operator topology, which is the topology of
pointwise convergence in the norm of `F`. We show that it makes `E →SOT[𝕜] F` a topological
vector space.
-/
section Topology

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/-- The function that induces the topology on `E →SOT[𝕜] F`, namely the evaluation map
`A ↦ fun x => A x`, bundled as a linear map. -/
def inducingFn : (E →SSOT[σ] F) →ₗ[𝕜₂] (E → F) where
  toFun := fun A x => A x
  map_add' := fun f g => by ext x; simp
  map_smul' := fun c f => by ext x; simp

@[simp]
lemma inducingFn_apply {f : E →SSOT[σ] F} {x : E} :
    inducingFn σ E F f x = f x :=
  rfl

/-- The strong operator topology is the coarsest topology such that `fun A => A x` is
continuous for all `x : E`. -/
instance instTopologicalSpace : TopologicalSpace (E →SSOT[σ] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]
lemma continuous_inducingFn : Continuous (inducingFn σ E F) :=
  continuous_induced_dom

/-- The evaluation map `A ↦ A x` is SOT-continuous. -/
@[fun_prop]
lemma continuous_apply (x : E) : Continuous fun (A : E →SSOT[σ] F) => A x :=
  (continuous_pi_iff.mp continuous_inducingFn) x

@[fun_prop]
lemma continuous_of_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →SSOT[σ] F}
    (h : ∀ x, Continuous fun a => g a x) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

lemma isInducing_inducingFn : IsInducing (inducingFn σ E F) := ⟨rfl⟩

lemma isEmbedding_inducingFn : IsEmbedding (inducingFn σ E F) :=
  Function.Injective.isEmbedding_induced fun A B hAB => by
    rw [ContinuousLinearMapSOT.ext_iff]; simpa [funext_iff] using hAB

open Filter in
/-- The defining property of the strong operator topology: a function `f` tends to
`A : E →SOT[𝕜] F` along filter `l` iff `f a x` tends to `A x` along the same filter (in the
topology of `F`). -/
lemma tendsto_iff_forall_tendsto {α : Type*} {l : Filter α} {f : α → E →SSOT[σ] F}
    {A : E →SSOT[σ] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x, Tendsto (fun a => f a x) l (𝓝 (A x)) := by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]

lemma le_nhds_iff_forall_apply_le_nhds {l : Filter (E →SSOT[σ] F)} {A : E →SSOT[σ] F} :
    l ≤ 𝓝 A ↔ ∀ x, l.map (fun T => T x) ≤ 𝓝 (A x) :=
  tendsto_iff_forall_tendsto (f := id)

instance instT2Space [T2Space F] : T2Space (E →SSOT[σ] F) :=
  isEmbedding_inducingFn.t2Space

instance instContinuousAdd : ContinuousAdd (E →SSOT[σ] F) := .induced (inducingFn σ E F)
instance instContinuousNeg : ContinuousNeg (E →SSOT[σ] F) := .induced (inducingFn σ E F)

instance instContinuousSMul [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E →SSOT[σ] F) :=
  .induced (inducingFn σ E F)

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E →SSOT[σ] F) where
  toContinuousAdd := inferInstance

instance instUniformSpace [UniformSpace F] : UniformSpace (E →SSOT[σ] F) :=
  .comap (inducingFn σ E F) inferInstance

instance instIsUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformAddGroup (E →SSOT[σ] F) :=
  .comap (inducingFn σ E F)

end Topology

/-! ### The SOT is induced by a family of seminorms -/
section Seminorms

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The family of seminorms that induce the strong operator topology, namely `‖A x‖` for all
`x : E`. -/
def seminorm (x : E) : Seminorm 𝕜₂ (E →SSOT[σ] F) where
  toFun A := ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only [add_apply] using norm_add_le (A x) (B x)
  neg' A := by simp [neg_apply]
  smul' r A := by simp [smul_apply, norm_smul]

variable (σ E F) in
/-- The family of seminorms that induce the strong operator topology, indexed by `E`. -/
def seminormFamily : SeminormFamily 𝕜₂ (E →SSOT[σ] F) E :=
  fun x => seminorm x

variable (σ E F) in
/-- The evaluation coercion `E →SSOT[σ] F → E → F` as a linear map, for use in the normed
setting. -/
def inducingFnNormed : (E →SSOT[σ] F) →ₗ[𝕜₂] (E → F) where
  toFun := fun A x => A x
  map_add' := fun f g => by ext x; simp
  map_smul' := fun c f => by ext x; simp

variable (σ E F) in
lemma isInducing_inducingFnNormed : IsInducing (inducingFnNormed σ E F) :=
  isInducing_inducingFn (F := F)

lemma withSeminorms : WithSeminorms (seminormFamily σ E F) :=
  let e : E ≃ (Σ _ : E, Fin 1) := .symm <| .sigmaUnique _ _
  (isInducing_inducingFnNormed σ E F).withSeminorms <|
    withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ F) |>.congr_equiv e

lemma hasBasis_seminorms :
    (𝓝 (0 : E →SSOT[σ] F)).HasBasis (seminormFamily σ E F).basisSets id :=
  withSeminorms.hasBasis

instance instLocallyConvexSpace [NormedSpace ℝ 𝕜₂] [Module ℝ (E →SSOT[σ] F)]
    [IsScalarTower ℝ 𝕜₂ (E →SSOT[σ] F)] :
    LocallyConvexSpace ℝ (E →SSOT[σ] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

section toSOT_continuous

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] [ContinuousSMul 𝕜₁ E]

/-- The strong operator topology is coarser than the bounded convergence topology, i.e. the
inclusion map is continuous. -/
@[continuity, fun_prop]
lemma ContinuousLinearMap.continuous_toSOT :
    Continuous (ContinuousLinearMap.toSOT σ E F) :=
  ContinuousLinearMapSOT.continuous_of_apply_continuous fun x ↦ continuous_eval_const x

/-- The inclusion map from `E →SL[σ] F` to `E →SSOT[σ] F`, bundled as a continuous linear map. -/
def ContinuousLinearMap.toSOTCLM : (E →SL[σ] F) →L[𝕜₂] (E →SSOT[σ] F) :=
  ⟨LinearEquiv.toLinearMap (ContinuousLinearMap.toSOT σ E F), ContinuousLinearMap.continuous_toSOT⟩

end toSOT_continuous

/-! ### The WOT is coarser than the SOT -/
section wot_le_sot

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The SOT is finer than the WOT: the canonical map `E →SSOT[σ] F → E →SWOT[σ] F` is
continuous. This reflects that norm convergence of `A x` implies weak convergence of `A x`. -/
@[fun_prop]
lemma continuous_sotToWot :
    Continuous (fun A : E →SSOT[σ] F =>
      ContinuousLinearMap.toWOT σ E F ((ContinuousLinearMap.toSOT σ E F).symm A)) :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y =>
    y.cont.comp (continuous_apply x)

end wot_le_sot

end ContinuousLinearMapSOT
