/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Inner product spaces

This file defines inner product spaces.
Hilbert spaces can be obtained using the set of assumptions
`[RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]`.
For convenience, a variable alias `HilbertSpace` is provided so that one can write
`variable? [HilbertSpace 𝕜 E]` and get this as a suggestion.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `RCLike` typeclass.

Rather than defining the norm on an inner product space to be `√(re ⟪x, x⟫)`, we assume that a norm
is given, and add a hypothesis stating that `‖x‖ ^ 2 = re ⟪x, x⟫`. This makes it possible to
handle spaces where the norm is equal, but not defeq, to the square root of the
inner product. Defining a norm starting from an inner product is handled via the
`InnerProductSpace.Core` structure.

This file is intended to contain the minimal amount of machinery needed to define inner product
spaces, and to construct a normed space from an inner product space. Many more general lemmas can
be found in `Analysis.InnerProductSpace.Basic`. For the specific construction of an inner product
structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `EuclideanSpace` in
`Analysis.InnerProductSpace.PiL2`.

## Main results

- We define the class `InnerProductSpace 𝕜 E` extending `NormedSpace 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `RCLike` typeclass.
- The inner product axioms that make no reference to a norm form the `Prop`-valued mixin
  `IsInnerProduct 𝕜 F`. Stating a lemma for it rather than for `InnerProductSpace` also makes the
  lemma available on a space whose norm is yet to be constructed from the inner product.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

@[expose] public section


noncomputable section

open RCLike Real Filter Bornology

open scoped Topology ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class Inner (𝕜 E : Type*) where
  /-- The inner product function. -/
  inner (𝕜) : E → E → 𝕜

export Inner (inner)

/-- The inner product with values in `𝕜`. -/
scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y

section Notations

/-- The inner product with values in `ℝ`. -/
scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The inner product with values in `ℂ`. -/
scoped[ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℂ x y

end Notations

/-- A (pre) inner product space is a vector space with an additional operation called inner product.
The (semi)norm could be derived from the inner product, instead we require the existence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`.
-/
@[wikidata Q214159]
class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
    NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_re_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

/-! ### The algebraic axioms of an inner product -/

/-- `IsInnerProduct 𝕜 F` states that the inner product on `F` is a positive semidefinite
Hermitian sesquilinear form.

`InnerProductSpace` provides an instance; see also `InnerProductSpace.Core.toIsInnerProduct`. -/
class IsInnerProduct (𝕜 F : Type*) [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [Inner 𝕜 F] :
    Prop where
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm (x y : F) : conj (inner 𝕜 y x) = inner 𝕜 x y
  /-- The inner product is positive (semi)definite. -/
  re_inner_nonneg (x : F) : 0 ≤ re (inner 𝕜 x x)
  /-- The inner product is additive in the first coordinate. -/
  add_left (x y z : F) : inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left (x y : F) (r : 𝕜) : inner 𝕜 (r • x) y = conj r * inner 𝕜 x y

instance InnerProductSpace.toIsInnerProduct [SeminormedAddCommGroup E]
    [c : InnerProductSpace 𝕜 E] : IsInnerProduct 𝕜 E :=
  { c with re_inner_nonneg x := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x ▸ sq_nonneg ‖x‖ }

section IsInnerProduct

variable [AddCommGroup F] [Module 𝕜 F] [Inner 𝕜 F] [IsInnerProduct 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Local notation for `starRingEnd _` -/
local postfix:90 "†" => starRingEnd _

@[simp]
theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  IsInnerProduct.conj_inner_symm ..

theorem inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

theorem norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

theorem inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  IsInnerProduct.add_left ..

theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  simp [← inner_conj_symm x (y + z), inner_add_left]

/-- See `inner_smul_left_eq_star_smul` for the case of a general algebra action. -/
theorem inner_smul_left (x y : F) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  IsInnerProduct.smul_left ..

/-- See `inner_smul_right_eq_smul` for the case of a general algebra action. -/
theorem inner_smul_right (x y : F) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  simp [← inner_conj_symm x (r • y), inner_smul_left]

@[simp]
theorem inner_zero_left (x : F) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F), inner_smul_left, map_zero, zero_mul]

@[simp]
theorem inner_zero_right (x : F) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, map_zero]

@[simp]
theorem inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  simpa using inner_smul_left x y (-1 : 𝕜)

@[simp]
theorem inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  simpa using inner_smul_right x y (-1 : 𝕜)

theorem inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  linarith [inner_im_symm (𝕜 := 𝕜) x x]

theorem inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  conj_eq_iff_re.mp (inner_conj_symm x x)

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  IsInnerProduct.re_inner_nonneg _

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]
  ring

/-- Expand `⟪x - y, x - y⟫` -/
theorem inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]
  ring

theorem IsInnerProduct.inner_smul_ofReal_left (x y : F) (t : ℝ) :
    ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_left, conj_ofReal, mul_comm]

theorem IsInnerProduct.inner_smul_ofReal_right (x y : F) (t : ℝ) :
    ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_right, mul_comm]

theorem IsInnerProduct.re_inner_smul_ofReal_smul_self (x : F) (t : ℝ) :
    re ⟪(t : 𝕜) • x, (t : 𝕜) • x⟫ = re ⟪x, x⟫ * t * t := by
  simp [IsInnerProduct.inner_smul_ofReal_left, IsInnerProduct.inner_smul_ofReal_right]

/-- The nonnegative quadratic in `t` behind the discriminant proof of the
**Cauchy–Schwarz inequality**. -/
lemma IsInnerProduct.cauchy_schwarz_aux' (x y : F) (t : ℝ) :
    0 ≤ re ⟪x, x⟫ * t * t + 2 * re ⟪x, y⟫ * t + re ⟪y, y⟫ := by
  have h : (0 : ℝ) ≤ re ⟪(t : 𝕜) • x + y, (t : 𝕜) • x + y⟫ := inner_self_nonneg
  rw [inner_add_add_self] at h
  simp only [inner_smul_left, inner_smul_right, conj_ofReal, map_add, re_ofReal_mul,
    inner_re_symm y x] at h
  linarith

/-- An auxiliary equality behind the equality case of the **Cauchy–Schwarz inequality**. -/
theorem IsInnerProduct.cauchy_schwarz_aux (x y : F) :
    re ⟪⟪x, y⟫ • x - ⟪x, x⟫ • y, ⟪x, y⟫ • x - ⟪x, x⟫ • y⟫
      = re ⟪x, x⟫ * (re ⟪x, x⟫ * re ⟪y, y⟫ - ‖⟪x, y⟫‖ ^ 2) := by
  -- Name the reals underlying `⟪x, x⟫` and `⟪y, y⟫`, so that rewriting `⟪x, x⟫` into its own
  -- real part does not loop.
  obtain ⟨a, ha⟩ := conj_eq_iff_real.mp (inner_conj_symm (𝕜 := 𝕜) x x)
  obtain ⟨b, hb⟩ := conj_eq_iff_real.mp (inner_conj_symm (𝕜 := 𝕜) y y)
  rw [← @ofReal_inj 𝕜, inner_self_ofReal_re]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, ha, hb, conj_ofReal, mul_sub,
    ofReal_re]
  rw [← mul_assoc, mul_conj, RCLike.conj_mul, mul_left_comm, ← inner_conj_symm y, mul_conj]
  push_cast
  ring

/-- **Cauchy–Schwarz inequality**. -/
@[wikidata Q190546]
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  suffices discrim (re ⟪x, x⟫) (2 * ‖⟪x, y⟫‖) (re ⟪y, y⟫) ≤ 0 by
    rw [norm_inner_symm y x]
    rw [discrim, sq] at this
    linarith
  refine discrim_le_zero fun t ↦ ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [← sq, hzero, norm_zero, mul_zero, zero_mul, add_zero]
    obtain ⟨hx, hy⟩ : (0 ≤ re ⟪x, x⟫ ∧ 0 ≤ re ⟪y, y⟫) := ⟨inner_self_nonneg, inner_self_nonneg⟩
    positivity
  · have hzero' : ‖⟪x, y⟫‖ ≠ 0 := norm_ne_zero_iff.2 hzero
    convert! IsInnerProduct.cauchy_schwarz_aux' (𝕜 := 𝕜) (⟪x, y⟫ • x) y (t / ‖⟪x, y⟫‖) using 3
    · field_simp
      rw [inner_smul_right, inner_smul_left, ← mul_assoc _ _ ⟪x, x⟫, mul_conj]
      rw [← ofReal_pow, re_ofReal_mul]
      ring
    · field_simp
      rw [inner_smul_left, mul_comm _ ⟪x, y⟫, mul_conj, ← ofReal_pow, ofReal_re]
      ring

end IsInnerProduct

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`InnerProductSpace.Core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `InnerProductSpace`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/-- A structure requiring that a scalar product is positive semidefinite and symmetric. -/
structure PreInnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
    [Module 𝕜 F] extends Inner 𝕜 F where
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm x y : conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  re_inner_nonneg x : 0 ≤ re (inner x x)
  /-- The inner product is additive in the first coordinate. -/
  add_left x y z : inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left x y r : inner (r • x) y = conj r * inner x y

attribute [class] PreInnerProductSpace.Core

/-- A structure requiring that a scalar product is positive definite. Some theorems that
require these assumptions are put under section `InnerProductSpace.Core`. -/
structure InnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends PreInnerProductSpace.Core 𝕜 F where
  /-- The inner product is positive definite. -/
  definite : ∀ x, inner x x = 0 → x = 0

/- We set `InnerProductSpace.Core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

instance (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
    [Module 𝕜 F] [cd : InnerProductSpace.Core 𝕜 F] : PreInnerProductSpace.Core 𝕜 F :=
  { cd with }

/-- Define `PreInnerProductSpace.Core` from `InnerProductSpace`. Note that the `Seminorm` instance
provided by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally equal to the
original norm. -/
@[instance_reducible, deprecated "Use `IsInnerProduct` for the norm-free lemmas; the rest of \
the `Core` API concerns the norm `Core` builds, which is not defeq to the original one."
  (since := "2026-09-09")]
def PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    PreInnerProductSpace.Core 𝕜 E where
  __ := c
  re_inner_nonneg := IsInnerProduct.re_inner_nonneg

/-- Define `InnerProductSpace.Core` from `InnerProductSpace`. Note that the `Norm` instance
provided by `InnerProductSpace.Core.norm` is propositionally but not definitionally equal to the
original norm. -/
@[instance_reducible, deprecated "Use `IsInnerProduct` for the norm-free lemmas; the rest of \
the `Core` API concerns the norm `Core` builds, which is not defeq to the original one."
  (since := "2026-09-09")]
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    re_inner_nonneg := IsInnerProduct.re_inner_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| eq_zero_of_pow_eq_zero (n := 2) <| by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x, hx, map_zero] }

namespace InnerProductSpace.Core

section PreInnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Local notation for `starRingEnd _` -/
local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `PreInnerProductSpace.Core` structure. We can't reuse
`PreInnerProductSpace.Core.toInner` because it takes `PreInnerProductSpace.Core` as an explicit
argument. -/
@[instance_reducible]
def toPreInner' : Inner 𝕜 F :=
  c.toInner

attribute [local instance] toPreInner'

/-- Make this a local instance to use the `IsInnerProduct` lemmas on a `Core`, before a norm on
`F` exists. -/
lemma toIsInnerProduct : IsInnerProduct 𝕜 F := { c with }

attribute [local instance] toIsInnerProduct

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
def normSq (x : F) :=
  re ⟪x, x⟫

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
local notation "normSqF" => @normSq 𝕜 F _ _ _ _

theorem inner_self_of_eq_zero {x : F} : x = 0 → ⟪x, x⟫ = 0 := fun h ↦ h ▸ inner_zero_left _

theorem normSq_eq_zero_of_eq_zero {x : F} : x = 0 → normSqF x = 0 := fun h ↦ by
  simp [normSq, inner_self_of_eq_zero h]

theorem ne_zero_of_inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 → x ≠ 0 :=
  mt inner_self_of_eq_zero

/-- (Semi)norm constructed from a `PreInnerProductSpace.Core` structure, defined to be the square
root of the scalar product. -/
@[instance_reducible]
def toNorm : Norm F where norm x := √(re ⟪x, x⟫)

attribute [local instance] toNorm

theorem norm_eq_sqrt_re_inner (x : F) : ‖x‖ = √(re ⟪x, x⟫) := rfl

theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_re_inner, ← sqrt_mul inner_self_nonneg, sqrt_mul_self inner_self_nonneg]

theorem sqrt_normSq_eq_norm (x : F) : √(normSqF x) = ‖x‖ := rfl

/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) <| by
    simpa only [norm_inner_symm y x, inner_self_eq_norm_mul_norm, mul_mul_mul_comm]
      using inner_mul_inner_self_le (𝕜 := 𝕜) x y

/-- The seminorm shared by `toSeminormedAddCommGroup` and `toNormedAddCommGroup`. -/
@[instance_reducible]
def toAddGroupSeminorm : AddGroupSeminorm F where
  toFun x := √(re ⟪x, x⟫)
  map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
  neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
  add_le' := fun x y => by
    have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
    have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := (re_le_norm _).trans h₁
    have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
    have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
      simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
      linarith
    exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this

/-- Seminormed group structure constructed from a `PreInnerProductSpace.Core` structure -/
@[instance_reducible]
def toSeminormedAddCommGroup : SeminormedAddCommGroup F :=
  AddGroupSeminorm.toSeminormedAddCommGroup (toAddGroupSeminorm (𝕜 := 𝕜))

attribute [local instance] toSeminormedAddCommGroup

/-- Normed space (which is actually a seminorm in general) structure constructed from a
`PreInnerProductSpace.Core` structure -/
@[instance_reducible]
def toNormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_re_inner, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul,
      ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← inner_self_ofReal_re, ofReal_re]
    · simp [← norm_eq_sqrt_re_inner]
    · positivity

omit c in
/-- Seminormed space core structure constructed from a `PreInnerProductSpace.Core` structure -/
lemma toSeminormedSpaceCore (c : PreInnerProductSpace.Core 𝕜 F) : SeminormedSpace.Core 𝕜 F where
  norm_nonneg x := norm_nonneg x
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

end PreInnerProductSpace.Core

section InnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [cd : InnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Inner product defined by the `InnerProductSpace.Core` structure. We can't reuse
`InnerProductSpace.Core.toInner` because it takes `InnerProductSpace.Core` as an explicit
argument. -/
@[instance_reducible]
def toInner' : Inner 𝕜 F :=
  cd.toInner

attribute [local instance] toInner'

/-- The `InnerProductSpace.Core` counterpart of `toIsInnerProduct`. -/
lemma toIsInnerProduct' : IsInnerProduct 𝕜 F := { cd with }

attribute [local instance] toIsInnerProduct'

local notation "normSqF" => @normSq 𝕜 F _ _ _ _

theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  ⟨cd.definite _, inner_self_of_eq_zero⟩

theorem normSq_eq_zero {x : F} : normSqF x = 0 ↔ x = 0 := by
  rw [normSq, ← ofReal_eq_zero (K := 𝕜), inner_self_ofReal_re, inner_self_eq_zero]

theorem inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

attribute [local instance] toNorm

/-- Normed group structure constructed from an `InnerProductSpace.Core` structure -/
@[instance_reducible]
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { __ := toAddGroupSeminorm (𝕜 := 𝕜)
      eq_zero_of_map_eq_zero' := fun _ hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }

section

attribute [local instance] toNormedAddCommGroup

omit cd in
/-- Normed space core structure constructed from an `InnerProductSpace.Core` structure -/
lemma toNormedSpaceCore (cd : InnerProductSpace.Core 𝕜 F) : NormedSpace.Core 𝕜 F where
  norm_nonneg x := norm_nonneg x
  norm_eq_zero_iff x := norm_eq_zero
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

end

set_option backward.isDefEq.respectTransparency false in
/-- In a topological vector space, if the unit ball of a continuous inner product is von Neumann
bounded, then the inner product defines the same topology as the original one. -/
lemma topology_eq
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    tF = cd.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  let p : Seminorm 𝕜 F := @normSeminorm 𝕜 F _ cd.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace
  suffices WithSeminorms (fun (i : Fin 1) ↦ p) by
    rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 this]
    simp
  have : p.ball 0 1 = {v | re (cd.inner v v) < 1} := by
    ext v
    simp only [ball_normSeminorm, Metric.mem_ball, dist_eq_norm, sub_zero, Set.mem_ofPred_eq, p]
    change √(re (cd.inner v v)) < 1 ↔ re (cd.inner v v) < 1
    conv_lhs => rw [show (1 : ℝ) = √1 by simp]
    rw [sqrt_lt_sqrt_iff]
    exact inner_self_nonneg
  rw [withSeminorms_iff_mem_nhds_isVonNBounded, this]
  refine ⟨?_, h'⟩
  have A : ContinuousAt (fun (v : F) ↦ re (cd.inner v v)) 0 := by fun_prop
  have B : Set.Iio 1 ∈ 𝓝 (re (cd.inner 0 0)) := by
    simp only [inner_zero_left, map_zero]
    exact Iio_mem_nhds (by positivity)
  exact A B

/-- Normed space structure constructed from an `InnerProductSpace.Core` structure, adjusting the
topology to make sure it is defeq to an already existing topology. -/
@[reducible] def toNormedAddCommGroupOfTopology
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    NormedAddCommGroup F :=
  NormedAddCommGroup.ofCoreReplaceTopology cd.toNormedSpaceCore (cd.topology_eq h h')

/-- Normed space structure constructed from an `InnerProductSpace.Core` structure, adjusting the
topology to make sure it is defeq to an already existing topology. -/
@[reducible] def toNormedSpaceOfTopology
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h';
    NormedSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  { norm_smul_le r x := by
      rw [norm_eq_sqrt_re_inner, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul,
        ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← inner_self_ofReal_re, ofReal_re]
      · simp [← norm_eq_sqrt_re_inner]
      · positivity }

end InnerProductSpace.Core

@[deprecated (since := "2026-09-09")] alias inner_conj_symm := _root_.inner_conj_symm
@[deprecated (since := "2026-09-09")] alias inner_self_nonneg := _root_.inner_self_nonneg
@[deprecated (since := "2026-09-09")] alias inner_self_im := _root_.inner_self_im
@[deprecated (since := "2026-09-09")] alias inner_add_left := _root_.inner_add_left
@[deprecated (since := "2026-09-09")] alias inner_add_right := _root_.inner_add_right
@[deprecated (since := "2026-09-09")] alias inner_re_symm := _root_.inner_re_symm
@[deprecated (since := "2026-09-09")] alias inner_im_symm := _root_.inner_im_symm
@[deprecated (since := "2026-09-09")] alias inner_smul_left := _root_.inner_smul_left
@[deprecated (since := "2026-09-09")] alias inner_smul_right := _root_.inner_smul_right
@[deprecated (since := "2026-09-09")] alias inner_zero_left := _root_.inner_zero_left
@[deprecated (since := "2026-09-09")] alias inner_zero_right := _root_.inner_zero_right
@[deprecated (since := "2026-09-09")] alias inner_self_ofReal_re := _root_.inner_self_ofReal_re
@[deprecated (since := "2026-09-09")]
alias ofReal_normSq_eq_inner_self := _root_.inner_self_ofReal_re
@[deprecated (since := "2026-09-09")] alias norm_inner_symm := _root_.norm_inner_symm
@[deprecated (since := "2026-09-09")] alias inner_neg_left := _root_.inner_neg_left
@[deprecated (since := "2026-09-09")] alias inner_neg_right := _root_.inner_neg_right
@[deprecated (since := "2026-09-09")] alias inner_sub_left := _root_.inner_sub_left
@[deprecated (since := "2026-09-09")] alias inner_sub_right := _root_.inner_sub_right
@[deprecated (since := "2026-09-09")]
alias inner_mul_symm_re_eq_norm := _root_.inner_mul_symm_re_eq_norm
@[deprecated (since := "2026-09-09")] alias inner_add_add_self := _root_.inner_add_add_self
@[deprecated (since := "2026-09-09")] alias inner_sub_sub_self := _root_.inner_sub_sub_self
@[deprecated (since := "2026-09-09")]
alias inner_smul_ofReal_left := IsInnerProduct.inner_smul_ofReal_left
@[deprecated (since := "2026-09-09")]
alias inner_smul_ofReal_right := IsInnerProduct.inner_smul_ofReal_right
@[deprecated (since := "2026-09-09")]
alias re_inner_smul_ofReal_smul_self := IsInnerProduct.re_inner_smul_ofReal_smul_self
@[deprecated (since := "2026-09-09")]
alias inner_mul_inner_self_le := _root_.inner_mul_inner_self_le
@[deprecated (since := "2026-09-09")]
alias cauchy_schwarz_aux' := IsInnerProduct.cauchy_schwarz_aux'
@[deprecated (since := "2026-09-09")]
alias cauchy_schwarz_aux := IsInnerProduct.cauchy_schwarz_aux

end InnerProductSpace.Core

section

attribute [local instance] InnerProductSpace.Core.toSeminormedAddCommGroup

/-- Given a `PreInnerProductSpace.Core` structure on a space, one can use it to turn
the space into a pre-inner product space (i.e., `SeminormedAddCommGroup` and `InnerProductSpace`).
The `SeminormedAddCommGroup` structure is expected to already be defined with
`InnerProductSpace.ofCore.toSeminormedAddCommGroup`. -/
@[instance_reducible]
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (cd : PreInnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := InnerProductSpace.Core.toNormedSpace
  { cd with
    norm_sq_eq_re_inner x := sq_sqrt (cd.re_inner_nonneg x) }

end

/-- Given an `InnerProductSpace.Core` structure on a space with a topology, one can use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is expected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroupOfTopology`. -/
@[instance_reducible]
def InnerProductSpace.ofCoreOfTopology [AddCommGroup F] [hF : Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (cd : InnerProductSpace.Core 𝕜 F)
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h';
    InnerProductSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  letI : NormedSpace 𝕜 F := cd.toNormedSpaceOfTopology h h'
  { cd with
    norm_sq_eq_re_inner x := sq_sqrt (cd.re_inner_nonneg x) }

/-- A Hilbert space is a complete normed inner product space. -/
@[variable_alias]
structure HilbertSpace (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace PUnit

instance : InnerProductSpace 𝕜 PUnit where
  inner _ _ := 0
  norm_sq_eq_re_inner := by simp
  conj_inner_symm := by simp
  add_left := by simp
  smul_left := by simp

@[simp] lemma inner_eq_zero (x y : PUnit) : inner 𝕜 x y = 0 := rfl

end PUnit

end
