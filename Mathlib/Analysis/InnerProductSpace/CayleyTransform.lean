/-
Copyright (c) 2026 Fang Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fang Luo
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Cayley Transform for Unbounded Self-Adjoint Operators

The Cayley transform provides a bijection between unbounded self-adjoint operators on a
Hilbert space and unitary operators (without 1 in the spectrum).

Given a densely-defined self-adjoint operator `A : E →ₗ.[ℂ] E`, the Cayley transform is
`V = (A - iI)(A + iI)⁻¹ : E →L[ℂ] E`, which is a unitary operator.

## Main definitions
- `LinearPMap.addI`: the operator `A + iI` as a `LinearPMap`
- `LinearPMap.subI`: the operator `A - iI` as a `LinearPMap`
- `LinearPMap.resolventCLM`: the bounded inverse `(A + iI)⁻¹ : E →L[ℂ] E`
- `LinearPMap.cayleyTransformCLM`: the Cayley transform `V = (A - iI)(A + iI)⁻¹`

## Main results
- `LinearPMap.inner_Ax_self_im_eq_zero`: for self-adjoint A, `im ⟪Ax, x⟫ = 0`
- `LinearPMap.norm_addI_sq`: the key norm identity `‖(A + iI)x‖² = ‖Ax‖² + ‖x‖²`
- `LinearPMap.addI_norm_ge`: the bound `‖x‖ ≤ ‖(A + iI)x‖`
- `LinearPMap.addI_range_dense`: the range of `(A + iI)` is dense
- `LinearPMap.addI_range_eq_top`: the range of `(A + iI)` equals `E`
- `LinearPMap.cayleyTransformCLM_isometry`: V is an isometry
- `LinearPMap.cayleyTransformCLM_isUnitary`: V is unitary

## References
- Reed & Simon, "Methods of Modern Mathematical Physics", Vol. 2, §VIII.2
- Rudin, "Functional Analysis", Chapter 13
-/

noncomputable section

open RCLike LinearPMap Complex

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

namespace LinearPMap

/-! ### The shifted operators (A ± iI) -/

section ShiftedOperator

/-- The operator `A + iI` on `dom(A)`, defined via `vadd` (adding `i • id` to A). -/
def addI (A : E →ₗ.[ℂ] E) : E →ₗ.[ℂ] E :=
  (Complex.I • LinearMap.id (R := ℂ) (M := E)) +ᵥ A

/-- The operator `A - iI` on `dom(A)`. -/
def subI (A : E →ₗ.[ℂ] E) : E →ₗ.[ℂ] E :=
  ((-Complex.I) • LinearMap.id (R := ℂ) (M := E)) +ᵥ A

omit [CompleteSpace E] in
@[simp]
theorem addI_domain (A : E →ₗ.[ℂ] E) : (addI A).domain = A.domain := vadd_domain _ _

omit [CompleteSpace E] in
@[simp]
theorem subI_domain (A : E →ₗ.[ℂ] E) : (subI A).domain = A.domain := vadd_domain _ _

omit [CompleteSpace E] in
theorem addI_apply {A : E →ₗ.[ℂ] E} (x : (addI A).domain) :
    addI A x = Complex.I • (x : E) + A ⟨x, x.2⟩ := by
  simp [addI, vadd_apply]

omit [CompleteSpace E] in
theorem subI_apply {A : E →ₗ.[ℂ] E} (x : (subI A).domain) :
    subI A x = -Complex.I • (x : E) + A ⟨x, x.2⟩ := by
  simp [subI, vadd_apply]

end ShiftedOperator

/-! ### Key norm identity: `‖(A ± iI)x‖² = ‖Ax‖² + ‖x‖²` -/

section NormIdentity

variable {A : E →ₗ.[ℂ] E}

/-- For a self-adjoint operator A, `im ⟪Ax, x⟫ = 0`.

Since A is self-adjoint, `⟪Ax, x⟫ = ⟪x, Ax⟫` (formal adjoint property).
By `inner_conj_symm`: `starRingEnd ℂ ⟪x, Ax⟫ = ⟪Ax, x⟫`. So `⟪Ax, x⟫ = starRingEnd ℂ ⟪Ax, x⟫`,
i.e. `⟪Ax, x⟫` is self-conjugate, meaning its imaginary part is zero. -/
theorem inner_Ax_self_im_eq_zero (hA : IsSelfAdjoint A) (x : A.domain) :
    RCLike.im ⟪A x, (x : E)⟫ = 0 := by
  have hd := hA.dense_domain
  have hformal : A.IsFormalAdjoint A := by
    have h := adjoint_isFormalAdjoint hd
    rw [isSelfAdjoint_def.mp hA] at h
    exact h
  -- h : ⟪A x, (x : E)⟫ = ⟪(x : E), A x⟫
  have h := hformal x x
  -- congrArg (starRingEnd ℂ) h : starRingEnd ℂ ⟪Ax, x⟫ = starRingEnd ℂ ⟪x, Ax⟫
  -- inner_conj_symm (A x) (x : E) : starRingEnd ℂ ⟪x, Ax⟫ = ⟪Ax, x⟫
  have hconj : starRingEnd ℂ ⟪A x, (x : E)⟫ = ⟪A x, (x : E)⟫ :=
    (congrArg (starRingEnd ℂ) h).trans (inner_conj_symm (A x) (x : E))
  exact RCLike.conj_eq_iff_im.mp hconj

/-- The key norm identity for (A + iI):
  `‖(A + iI)x‖² = ‖Ax‖² + ‖x‖²`

Proof: ‖Ax + i·x‖² = ‖Ax‖² + 2·re⟪Ax, i·x⟫ + ‖i·x‖²
                    = ‖Ax‖² + 2·re(i·⟪Ax,x⟫) + ‖x‖²
                    = ‖Ax‖² + 2·(-im⟪Ax,x⟫) + ‖x‖²
                    = ‖Ax‖² + ‖x‖²  (since im⟪Ax,x⟫ = 0 for self-adj. A)

The key step uses `Complex.I_mul_re : (I * z).re = -z.im`. -/
theorem norm_addI_sq (hA : IsSelfAdjoint A) (x : A.domain) :
    ‖addI A ⟨x, x.2⟩‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  rw [addI_apply]
  rw [show Complex.I • (x : E) + A ⟨x, x.2⟩ = A x + Complex.I • (x : E) from add_comm _ _]
  rw [norm_add_sq (𝕜 := ℂ)]
  have him : RCLike.im ⟪A x, (x : E)⟫ = 0 := inner_Ax_self_im_eq_zero hA x
  conv_lhs => rw [inner_smul_right]
  -- Goal: ‖Ax‖² + 2 * re (I * ⟪Ax, x⟫) + ‖I•x‖² = ‖Ax‖² + ‖x‖²
  have key : RCLike.re (Complex.I * ⟪A x, (x : E)⟫) = 0 := by
    change (Complex.I * ⟪A x, (x : E)⟫).re = 0
    rw [Complex.I_mul_re]; exact neg_eq_zero.mpr him
  simp only [key, mul_zero, add_zero, norm_smul, Complex.norm_I, one_mul]

/-- The key norm identity for (A - iI):
  `‖(A - iI)x‖² = ‖Ax‖² + ‖x‖²` -/
theorem norm_subI_sq (hA : IsSelfAdjoint A) (x : A.domain) :
    ‖subI A ⟨x, x.2⟩‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  rw [subI_apply]
  rw [show -Complex.I • (x : E) + A ⟨x, x.2⟩ = A x + -Complex.I • (x : E) from add_comm _ _]
  rw [norm_add_sq (𝕜 := ℂ)]
  have him : RCLike.im ⟪A x, (x : E)⟫ = 0 := inner_Ax_self_im_eq_zero hA x
  conv_lhs => rw [inner_smul_right]
  -- Goal: ‖Ax‖² + 2 * re (-I * ⟪Ax, x⟫) + ‖-I•x‖² = ‖Ax‖² + ‖x‖²
  have key : RCLike.re (-Complex.I * ⟪A x, (x : E)⟫) = 0 := by
    change (-Complex.I * ⟪A x, (x : E)⟫).re = 0
    rw [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]; exact him
  simp only [key, mul_zero, add_zero, norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- The norms of (A + iI)x and (A - iI)x are equal. -/
theorem addI_norm_eq_subI_norm (hA : IsSelfAdjoint A) (x : A.domain) :
    ‖addI A ⟨x, x.2⟩‖ = ‖subI A ⟨x, x.2⟩‖ := by
  have h1 := norm_addI_sq hA x
  have h2 := norm_subI_sq hA x
  nlinarith [norm_nonneg (addI A ⟨x, x.2⟩), norm_nonneg (subI A ⟨x, x.2⟩),
             sq_nonneg (‖addI A ⟨x, x.2⟩‖ - ‖subI A ⟨x, x.2⟩‖)]

/-- The bound `‖x‖ ≤ ‖(A + iI)x‖`. -/
theorem addI_norm_ge (hA : IsSelfAdjoint A) (x : A.domain) :
    ‖(x : E)‖ ≤ ‖addI A ⟨x, x.2⟩‖ := by
  have h := norm_addI_sq hA x
  nlinarith [sq_nonneg ‖A x‖, sq_nonneg ‖(x : E)‖, sq_nonneg ‖addI A ⟨x, x.2⟩‖,
             norm_nonneg (x : E), norm_nonneg (addI A ⟨x, x.2⟩)]

/-- The bound `‖x‖ ≤ ‖(A - iI)x‖`. -/
theorem subI_norm_ge (hA : IsSelfAdjoint A) (x : A.domain) :
    ‖(x : E)‖ ≤ ‖subI A ⟨x, x.2⟩‖ := by
  rw [← addI_norm_eq_subI_norm hA]
  exact addI_norm_ge hA x

end NormIdentity

/-! ### Injectivity and range of (A + iI) -/

section RangeProperties

variable {A : E →ₗ.[ℂ] E}

/-- (A + iI) has trivial kernel. -/
theorem addI_ker_eq_bot (hA : IsSelfAdjoint A) : (addI A).toFun.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro ⟨x, hx⟩ h
  have hx_dom : x ∈ A.domain := by rwa [addI_domain] at hx
  -- (addI A) ⟨x, hx_dom⟩ = 0
  have h' : addI A ⟨x, hx_dom⟩ = 0 := by convert h using 2
  have hbnd : ‖(x : E)‖ ≤ ‖addI A ⟨x, hx_dom⟩‖ := addI_norm_ge hA ⟨x, hx_dom⟩
  rw [h', norm_zero] at hbnd
  exact Subtype.val_injective (norm_eq_zero.mp (le_antisymm (norm_nonneg _) hbnd).symm)

/-- The range of `(A + iI)` is closed.

Follows from the antilipschitz condition `‖(A + iI)x‖ ≥ ‖x‖` and closedness of A.
We define Φ : ↥A.graph → E by Φ(x, Ax) = i·x + Ax = (A+iI)x. Since A.graph is complete
(A is closed by self-adjointness) and Φ is 1-antilipschitz, its range is closed. -/
theorem addI_range_isClosed (hA : IsSelfAdjoint A) :
    _root_.IsClosed (LinearMap.range (addI A).toFun : Set E) := by
  sorry

/-- The range of `(A + iI)` is dense in E.

Proof: If y ⊥ range(A + iI), then for all x ∈ dom(A), `⟪y, (A + iI)x⟫ = 0`.
This gives `⟪y, Ax⟫ = -i⟪y, x⟫`, showing y ∈ dom(A†) = dom(A) and A†y = iy.
Since A† = A, (A - iI)y = 0. But `‖(A - iI)y‖ ≥ ‖y‖`, so y = 0. -/
theorem addI_range_dense (hA : IsSelfAdjoint A) :
    Dense (LinearMap.range (addI A).toFun : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  -- hy : y ∈ (LinearMap.range (addI A).toFun)ᗮ
  -- Step 1: For any x : A.domain, ⟪y, (A+iI)x⟫ = 0
  have horth : ∀ x : A.domain, ⟪y, addI A x⟫ = 0 := by
    intro x
    have hmem : addI A x ∈ (LinearMap.range (addI A).toFun : Submodule ℂ E) :=
      LinearMap.mem_range_self (addI A).toFun x
    exact (Submodule.mem_orthogonal' _ y).mp hy _ hmem
  -- Step 2: From orthogonality: ⟪y, Ax⟫ = -I * ⟪y, x⟫ for all x : A.domain
  have hinner : ∀ x : A.domain, ⟪y, A x⟫ = -Complex.I * ⟪y, (x : E)⟫ := by
    intro x
    have h := horth x
    rw [addI_apply, inner_add_right, inner_smul_right] at h
    linear_combination h
  -- Step 3: Show y ∈ A†.domain using w = I•y
  have hy_dom : y ∈ A†.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨Complex.I • y, fun x => ?_⟩
    simp only [inner_smul_left, Complex.conj_I, hinner x]
  -- Step 4: Apply adjoint_apply_eq to get A†⟨y, hy_dom⟩ = I•y
  have hAstary : A† ⟨y, hy_dom⟩ = Complex.I • y := by
    apply LinearPMap.adjoint_apply_eq hA.dense_domain ⟨y, hy_dom⟩
    intro x
    simp only [inner_smul_left, Complex.conj_I, hinner x]
  -- Step 5: Transport to get A⟨y, hy_A⟩ = I•y
  have heq : A† = A := isSelfAdjoint_def.mp hA
  have hy_A : y ∈ A.domain := heq ▸ hy_dom
  have hAy : A ⟨y, hy_A⟩ = Complex.I • y :=
    ((LinearPMap.ext_iff.mp heq).2 (hf := hy_dom) (hg := hy_A)).symm.trans hAstary
  -- Step 6: (A - iI)y = -I•y + I•y = 0
  have hsubI : subI A ⟨y, hy_A⟩ = 0 := by
    rw [subI_apply, hAy, ← add_smul]
    simp
  -- Step 7: By subI_norm_ge, ‖y‖ = 0, so y = 0
  have hnorm : ‖(y : E)‖ ≤ 0 :=
    (subI_norm_ge hA ⟨y, hy_A⟩).trans (by rw [hsubI, norm_zero])
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- The range of `(A + iI)` equals all of E.
Since the range is closed  and dense (sorry'd), it equals ⊤. -/
theorem addI_range_eq_top (hA : IsSelfAdjoint A) :
    LinearMap.range (addI A).toFun = ⊤ := by
  have hclosed := addI_range_isClosed hA
  have hdense := addI_range_dense hA
  have hd : (LinearMap.range (addI A).toFun).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
  rwa [hclosed.submodule_topologicalClosure_eq] at hd

end RangeProperties

/-! ### The bounded inverse (A + iI)⁻¹ -/

section ResolventMap

variable {A : E →ₗ.[ℂ] E}

/-- The bounded linear map `(A + iI)⁻¹ : E →L[ℂ] E`.

Since `(A + iI)` is bijective (injective by norm bound, surjective because range = E)
and `‖(A + iI)x‖ ≥ ‖x‖`, the inverse is bounded with `‖(A + iI)⁻¹‖ ≤ 1`. -/
-- The linear equivalence `(addI A).domain ≃ₗ[ℂ] E` from bijectivity of `(addI A).toFun`.
private noncomputable def resolventEquiv (hA : IsSelfAdjoint A) :
    (addI A).domain ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective (addI A).toFun
    ⟨LinearMap.ker_eq_bot.mp (addI_ker_eq_bot hA),
     LinearMap.range_eq_top.mp (addI_range_eq_top hA)⟩

def resolventCLM (hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  (A.domain.subtype.comp (resolventEquiv hA).symm.toLinearMap).mkContinuous 1 fun y => by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, one_mul]
    -- ‖((resolventEquiv hA).symm y : E)‖ ≤ ‖y‖
    -- Let x := (resolventEquiv hA).symm y : (addI A).domain = A.domain
    set x := (resolventEquiv hA).symm y with hx_def
    -- hbnd : ‖(x : E)‖ ≤ ‖addI A x‖
    have hbnd : ‖(x : E)‖ ≤ ‖addI A x‖ := addI_norm_ge hA x
    -- heq : addI A x = y (as elements of E)
    have heq : addI A x = y := by
      -- addI A x = (addI A).toFun x = resolventEquiv hA (resolventEquiv hA).symm y = y
      change (addI A).toFun x = y
      simp [hx_def, resolventEquiv, LinearEquiv.ofBijective]
    calc ‖(x : E)‖ ≤ ‖addI A x‖ := hbnd
      _ = ‖y‖ := by rw [heq]

theorem resolventCLM_norm_le (hA : IsSelfAdjoint A) : ‖resolventCLM hA‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le
  exact zero_le_one

/-- The image of `resolventCLM` lands in `A.domain`. -/
theorem resolventCLM_mem_domain (hA : IsSelfAdjoint A) (y : E) :
    resolventCLM hA y ∈ A.domain := by
  simp only [resolventCLM, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
             Submodule.subtype_apply]
  exact ((resolventEquiv hA).symm y).2

/-- The defining property: `(A + iI)(resolventCLM y) = y`. -/
theorem addI_resolventCLM (hA : IsSelfAdjoint A) (y : E) :
    addI A ⟨resolventCLM hA y, resolventCLM_mem_domain hA y⟩ = y := by
  simp only [resolventCLM, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
             Submodule.subtype_apply]
  -- After simp: addI A ⟨((resolventEquiv hA).symm y : E), _⟩ = y
  -- which is addI A ((resolventEquiv hA).symm y) = y
  -- i.e. (addI A).toFun ((resolventEquiv hA).symm y) = y
  have : (addI A).toFun ((resolventEquiv hA).symm y) = y := by
    simp [resolventEquiv, LinearEquiv.ofBijective]
  rw [LinearPMap.toFun_eq_coe] at this
  convert this using 2

end ResolventMap

/-! ### The Cayley Transform V = (A - iI)(A + iI)⁻¹ -/

section CayleyTransform

variable {A : E →ₗ.[ℂ] E}

/-- The Cayley transform `V = (A - iI)(A + iI)⁻¹ : E →L[ℂ] E`.

For y ∈ E, let x = (A + iI)⁻¹ y ∈ dom(A). Then V(y) = (A - iI)(x). -/
def cayleyTransformCLM (hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun y => subI A ⟨resolventCLM hA y, resolventCLM_mem_domain hA y⟩
      map_add' := by
        intro x y
        have hx : resolventCLM hA x ∈ A.domain := resolventCLM_mem_domain hA x
        have hy : resolventCLM hA y ∈ A.domain := resolventCLM_mem_domain hA y
        rw [← LinearPMap.map_add (subI A) ⟨resolventCLM hA x, hx⟩ ⟨resolventCLM hA y, hy⟩]
        congr 1; ext1
        simp [(resolventCLM hA).map_add]
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply]
        have hx : resolventCLM hA x ∈ A.domain := resolventCLM_mem_domain hA x
        rw [← LinearPMap.map_smul (subI A) c ⟨resolventCLM hA x, hx⟩]
        congr 1; ext1
        simp [(resolventCLM hA).map_smul] }
    1
    (fun y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      set x := resolventCLM hA y
      have hxd : x ∈ A.domain := resolventCLM_mem_domain hA y
      have hy : addI A ⟨x, hxd⟩ = y := addI_resolventCLM hA y
      have heq : ‖subI A ⟨x, hxd⟩‖ = ‖y‖ :=
        ((addI_norm_eq_subI_norm hA ⟨x, hxd⟩).symm.trans (by rw [hy]))
      linarith [norm_nonneg y])

/-- The Cayley transform preserves norms: `‖Vy‖ = ‖y‖`.

Let x = (A + iI)⁻¹ y. Then y = (A + iI)x, so ‖y‖ = ‖(A + iI)x‖.
Vy = (A - iI)x, and ‖(A - iI)x‖ = ‖(A + iI)x‖ = ‖y‖. -/
theorem cayleyTransformCLM_norm_eq (hA : IsSelfAdjoint A) (y : E) :
    ‖cayleyTransformCLM hA y‖ = ‖y‖ := by
  change ‖subI A ⟨resolventCLM hA y, resolventCLM_mem_domain hA y⟩‖ = ‖y‖
  set x := resolventCLM hA y
  have hxd : x ∈ A.domain := resolventCLM_mem_domain hA y
  have hy : addI A ⟨x, hxd⟩ = y := addI_resolventCLM hA y
  calc ‖subI A ⟨x, hxd⟩‖ = ‖addI A ⟨x, hxd⟩‖ := (addI_norm_eq_subI_norm hA ⟨x, hxd⟩).symm
    _ = ‖y‖ := by rw [hy]

/-- The Cayley transform is an isometry. -/
theorem cayleyTransformCLM_isometry (hA : IsSelfAdjoint A) :
    Isometry (cayleyTransformCLM hA) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm]
  rw [show cayleyTransformCLM hA x - cayleyTransformCLM hA y =
      cayleyTransformCLM hA (x - y) from ((cayleyTransformCLM hA).map_sub x y).symm]
  exact cayleyTransformCLM_norm_eq hA _

/-- The range of the Cayley transform is dense. -/
theorem cayleyTransformCLM_range_dense (hA : IsSelfAdjoint A) :
    Dense (Set.range (cayleyTransformCLM hA)) := by
  sorry

/-- The Cayley transform is surjective.

The Cayley transform is a linear isometry (cayleyTransformCLM_isometry), hence has closed range
(Isometry.isClosedEmbedding). Its range is also dense (cayleyTransformCLM_range_dense).
A closed dense set equals the whole space, so V is surjective. -/
theorem cayleyTransformCLM_surjective (hA : IsSelfAdjoint A) :
    Function.Surjective (cayleyTransformCLM hA) := by
  -- The isometry has closed range
  have hclosed : _root_.IsClosed (Set.range (cayleyTransformCLM hA)) :=
    (cayleyTransformCLM_isometry hA).isClosedEmbedding.isClosed_range
  -- The range is dense
  have hdense : Dense (Set.range (cayleyTransformCLM hA)) :=
    cayleyTransformCLM_range_dense hA
  -- Dense + closed = everything
  have huniv : Set.range (cayleyTransformCLM hA) = Set.univ := by
    rw [dense_iff_closure_eq] at hdense
    rwa [hclosed.closure_eq] at hdense
  rwa [← Set.range_eq_univ]

/-- The Cayley transform is unitary. -/
theorem cayleyTransformCLM_isUnitary (hA : IsSelfAdjoint A) :
    (cayleyTransformCLM hA) ∈ unitary (E →L[ℂ] E) := by
  -- Build a linear isometry from the norm identity
  let φ : E →ₗᵢ[ℂ] E :=
    { (cayleyTransformCLM hA).toLinearMap with
      norm_map' := cayleyTransformCLM_norm_eq hA }
  -- Use surjectivity to get a linear isometry equivalence
  let Φ : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.ofSurjective φ (cayleyTransformCLM_surjective hA)
  -- Show the underlying CLM of Φ equals cayleyTransformCLM hA
  have hcoe : (Φ : E →L[ℂ] E) = cayleyTransformCLM hA := by
    ext y
    have hfun := LinearIsometryEquiv.coe_ofSurjective φ (cayleyTransformCLM_surjective hA)
    exact congr_fun hfun y
  -- Use the membership of the symm element and transfer via hcoe
  have hmem : (Unitary.linearIsometryEquiv.symm Φ : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
    (Unitary.linearIsometryEquiv.symm Φ).property
  rwa [Unitary.coe_symm_linearIsometryEquiv_apply, hcoe] at hmem

end CayleyTransform

end LinearPMap

end
