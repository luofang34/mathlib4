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
- `LinearPMap.addI_range_dense`: the range of `(A + iI)` is dense (sorry'd)
- `LinearPMap.addI_range_eq_top`: the range of `(A + iI)` equals `E` (sorry'd)
- `LinearPMap.cayleyTransformCLM_isometry`: V is an isometry
- `LinearPMap.cayleyTransformCLM_isUnitary`: V is unitary (sorry'd)

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
The precise argument: if `(A + iI)xₙ → y`, the norm bound implies `{xₙ}` is Cauchy,
so `xₙ → x` for some x. Since `A` is closed (self-adjoint ↔ closed), `Axₙ → Ax`,
so `(A + iI)xₙ → (A + iI)x = y`. -/
theorem addI_range_isClosed (hA : IsSelfAdjoint A) :
    _root_.IsClosed (LinearMap.range (addI A).toFun : Set E) := by
  sorry

/-- The range of `(A + iI)` is dense in E.

Proof: If y ⊥ range(A + iI), then for all x ∈ dom(A), `⟪y, (A + iI)x⟫ = 0`.
This gives `⟪y, Ax⟫ = -i⟪y, x⟫`, showing y ∈ dom(A†) = dom(A) and A†y = -iy.
Since A† = A, (A - iI)y = 0. But `‖(A - iI)y‖ ≥ ‖y‖`, so y = 0. -/
theorem addI_range_dense (hA : IsSelfAdjoint A) :
    Dense (LinearMap.range (addI A).toFun : Set E) := by
  sorry

/-- The range of `(A + iI)` equals all of E.
Since the range is closed (sorry'd) and dense (sorry'd), it equals ⊤. -/
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
def resolventCLM (hA : IsSelfAdjoint A) : E →L[ℂ] E := by
  sorry

theorem resolventCLM_norm_le (hA : IsSelfAdjoint A) : ‖resolventCLM hA‖ ≤ 1 := by
  sorry

/-- The image of `resolventCLM` lands in `A.domain`. -/
theorem resolventCLM_mem_domain (hA : IsSelfAdjoint A) (y : E) :
    resolventCLM hA y ∈ A.domain := by
  sorry

/-- The defining property: `(A + iI)(resolventCLM y) = y`. -/
theorem addI_resolventCLM (hA : IsSelfAdjoint A) (y : E) :
    addI A ⟨resolventCLM hA y, resolventCLM_mem_domain hA y⟩ = y := by
  sorry

end ResolventMap

/-! ### The Cayley Transform V = (A - iI)(A + iI)⁻¹ -/

section CayleyTransform

variable {A : E →ₗ.[ℂ] E}

/-- The Cayley transform `V = (A - iI)(A + iI)⁻¹ : E →L[ℂ] E`.

For y ∈ E, let x = (A + iI)⁻¹ y ∈ dom(A). Then V(y) = (A - iI)(x). -/
def cayleyTransformCLM (hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  { toFun := fun y => subI A ⟨resolventCLM hA y, resolventCLM_mem_domain hA y⟩
    map_add' := by intro x y; sorry
    map_smul' := by intro c x; sorry
    cont := by sorry }

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

/-- The Cayley transform is surjective. -/
theorem cayleyTransformCLM_surjective (hA : IsSelfAdjoint A) :
    Function.Surjective (cayleyTransformCLM hA) := by
  sorry

/-- The Cayley transform is unitary. -/
theorem cayleyTransformCLM_isUnitary (hA : IsSelfAdjoint A) :
    (cayleyTransformCLM hA) ∈ unitary (E →L[ℂ] E) := by
  sorry

end CayleyTransform

end LinearPMap

end
