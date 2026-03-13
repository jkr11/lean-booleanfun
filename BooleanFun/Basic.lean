/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import BooleanFun.AuxLemmas
import BooleanFun.ToMathlib.Finset

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi

--set_option profiler true

/-!
# Analysis on Boolean functions

This file contains some basic definitions and theorems for analysis
of real-valued Boolean functions mainly following Ryan O'Donnell's book [odonnell2014].
The Hamming cube is represented by the function type `Fin n → Fin 2`, so that
a `BooleanFunc n` is a `(Fin n → Fin 2) → ℝ`.

Thanks to Mathlib, it is relatively straightforward to get started with Fourier analysis:
* Typeclass inference automatically equips `BooleanFunc n` with the appropriate ℝ-vector space structure.
* We define inner product space structure via `InnerProductSpace.Core` and show that
the `walshCharacter`s form an orthonormal basis.
* Then Plancherel's theorem follows from Mathlib's `OrthogonalFamily.inner_sum`.

Even if there was a general framework for Fourier transforms on LCA groups in Mathlib,
it may be preferrable to use this ad-hoc definition due to slightly different notational conventions
in the context of Boolean functions, and the simplicity of working with finite sums.

## Main results

* `walsh_fourier` expresses a Boolean function in terms of its Walsh-Fourier transform
* `variance_le_totalInfluence` is a version of the classical L² Poincaré inequality
* `fourier_convolution` is the convolution theorem for the Walsh-Fourier transform

## Notation

* `𝐄` denotes expectation with respect to uniform probability measure
* `χ S` denotes the Walsh character associated with an `S : Finset (Fin n)`
* `𝓕` denotes the Walsh-Fourier transform `fourierTransform`
* `⟨⬝, ⬝⟩` denotes the inner product defined as expectation of product
* `‖⬝‖` denotes the (normalized) L² norm
* `⋆` denotes convolution

## ToDo
* Generalize to `RCLike`-valued
* Fill in some more basic facts

-/

namespace BooleanFun

open Real BigOperators Function Finset Pi
open RealInnerProductSpace


/-- A Boolean function maps an `n`-tuple of bits (of type `Fin n → Fin 2`) to a real number. -/
abbrev BooleanFunc (n : ℕ) : Type := (Fin n → Fin 2) → ℝ

noncomputable section

variable {α : Type*}

variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}

lemma two_eq_zero : (2 : Fin n → Fin 2) = 0 := by
  -- slightly awkward because `CharP (Fin n → Fin 2) 2` depends on  `Nonempty (Fin n)`
  obtain hn|hn := isEmpty_or_nonempty (Fin n)
  · simp only [Unique.eq_default]
  · exact CharTwo.two_eq_zero

/-- Translation invariance -/
lemma sum_translate (a : Fin n → Fin 2) : ∑ x, f x = ∑ x, f (x + a) := by
  apply sum_bijective (fun x ↦ x + a)
  · constructor
    · intro x y; simp
    · intro y; use y + a; abel_nf; simp [two_eq_zero]
  · simp
  · intro i _; abel_nf; simp [two_eq_zero]

/-- The expectation of a Boolean function is its average value with respect to the uniform
probability measure on `Fin n → Fin 2`. -/
def expectation : BooleanFunc n →ₗ[ℝ] ℝ := {
  toFun := fun f ↦ (1 / 2) ^ n * ∑ i, f i
  map_add' := by
    intro f g
    simp only [one_div, inv_pow, Pi.add_apply]
    rw [sum_add_distrib]
    ring
  map_smul' := by
    intro c f
    dsimp
    rw [← mul_sum]
    ring
}

/-- Expectation of a Boolean function -/
scoped notation "𝐄" => expectation

/-- Definition of Walsh character -/
abbrev walshCharacter (S : Finset (Fin n)) : BooleanFunc n := fun x ↦ ∏ i ∈ S, (-1) ^ (x i).val

/-- Walsh character -/
scoped notation "χ" => walshCharacter

lemma walsh_def : χ S x = ∏ i ∈ S, (-1) ^ (x i).val := by rfl

lemma walsh_ne_zero : χ S x ≠ 0 := by apply prod_ne_zero_iff.mpr; intro i _; simp

lemma walsh_eq_neg_one_pow_sum : χ S x = (-1) ^ ∑ i ∈ S, (x i).val := prod_pow_eq_pow_sum _ _ _
-- or use Finset.cons_induction

/-- Walsh characters are characters. -/
lemma walsh_add : χ S (x + y) = (χ S x) * (χ S y) := by
  rw [← prod_mul_distrib, prod_congr (by rfl)]
  have (v : Fin 2) : v = 0 ∨ v = 1 := by omega
  intro i _
  dsimp
  obtain ⟨hx|hx, hy|hy⟩ := And.intro (this (x i)) (this (y i)) <;>
    { rw [hx, hy]; simp }

/-- Dual space of Boolean functions as the type of real-valued functions on `Finset (Fin n)`. -/
abbrev BooleanFunc' n := Finset (Fin n) → ℝ

/-- The Walsh-Fourier transform of a Boolean function `f` is defined on sets of coordinates
`S : Finset (Fin n)` as expectation of the Walsh character `χ S` times `f`. -/
def fourierTransform : BooleanFunc n →ₗ[ℝ] BooleanFunc' n := {
  toFun := fun f ↦ fun S ↦ 𝐄 (χ S * f)
  map_add' := by
    intro f g
    funext S
    simp
    ring_nf
    simp
  map_smul' := by
    intro c f
    funext S
    simp
}

/-- Walsh-Fourier transform on Boolean functions -/
scoped notation "𝓕" => fourierTransform

theorem expectation_eq_fourier : 𝐄 f = 𝓕 f ∅ := by
  unfold fourierTransform
  unfold walshCharacter
  unfold expectation
  simp only [one_div, inv_pow, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.mul_apply, prod_empty, one_mul]

/-- The inner product of two Boolean functions is the expectation of their pointwise product. -/

theorem expectation_prod_self_nonneg : 0 ≤ 𝐄 (f * f) := by
  apply mul_nonneg
  · norm_num
  · apply sum_nonneg
    intros x _
    apply mul_self_nonneg

/-- Boolean functions form an inner product space. -/
instance : InnerProductSpace.Core ℝ (BooleanFunc n) := {
  inner := fun f g ↦ 𝐄 (f * g)
  conj_symm := by
    intros f g
    simp only [conj_trivial]
    rw [mul_comm]
  nonneg_re := by
    intro f
    simp only [RCLike.re_to_real, expectation_prod_self_nonneg]
  add_left := by simp only [add_mul, map_add, implies_true]
  smul_left := by
    simp only [Algebra.smul_mul_assoc, map_smul, smul_eq_mul, conj_trivial, implies_true]
  definite := by
    intro h; simp [expectation]
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    . simp; intro i; ext j; simp [i]
    . intro i _; apply mul_self_nonneg

}

instance : NormedAddCommGroup (BooleanFunc n) :=
  instCoreRealBooleanFunc.toNormedAddCommGroup

instance : SeminormedAddCommGroup (BooleanFunc n) :=
  instNormedAddCommGroupBooleanFunc.toSeminormedAddCommGroup

instance : InnerProductSpace ℝ (BooleanFunc n) :=
  InnerProductSpace.ofCore instCoreRealBooleanFunc

instance : Norm (BooleanFunc n) := InnerProductSpace.Core.toNorm (𝕜 := ℝ) (F := BooleanFunc n)

/-- Cauchy-Schwarz inequality on Boolean functions -/
theorem cauchy_schwarz : |⟪f, g⟫| ≤ ‖f‖ * ‖g‖ :=
  norm_inner_le_norm (𝕜 := ℝ) f g

@[simp]
lemma walsh_sq_eq_one : (χ S) ^ 2 = 1 := by
  funext x
  unfold walshCharacter
  simp only [Pi.pow_apply, Pi.one_apply]
  rw [← prod_pow]
  ring_nf
  simp

@[simp]
lemma expectation_one : @expectation n 1 = 1 := by simp [expectation]

lemma norm_sq_eq_inner : ‖f‖ ^ 2 = ⟪f, f⟫ := by
  rw [← RCLike.re_to_real (x := ⟪f, f⟫), ← InnerProductSpace.norm_sq_eq_inner]

/-- Walsh characters are L² normalized. -/
@[simp]
theorem walsh_norm_one (S : Finset (Fin n)) : ‖χ S‖ = 1 := by
  simp only [norm_eq_sqrt_inner (𝕜 := ℝ), sqrt_eq_one]
  change 𝐄 _ = 1
  rw [← pow_two, walsh_sq_eq_one]
  simp

@[simp]
theorem walsh_inner_self_eq_one : ⟪χ S, χ S⟫ = 1 := by
  rw [← norm_sq_eq_inner, walsh_norm_one, one_pow]

theorem walsh_mul_eq : χ S * χ S' = χ (symmDiff S S') := by
  funext x
  unfold walshCharacter
  simp
  nth_rewrite 1 [← sdiff_union_inter S S']
  nth_rewrite 3 [← sdiff_union_inter S' S]
  repeat rw [prod_union (disjoint_sdiff_inter _ _)]
  rw [inter_comm S]
  ring_nf
  have haux : (∏ i ∈ S' ∩ S, ((-1 : ℝ) ^ (x i).val)) ^ 2 = 1 := by
    rw [← prod_pow]; ring_nf; simp
  rw [haux, mul_one, ← prod_union]
  · rfl
  · simp only [disjoint_iff_ne, mem_sdiff, ne_eq, and_imp]
    intro _ ha _ _ _ _ h
    rw [h] at ha
    contradiction

lemma inner_eq_expectation : ⟪f, g⟫ = 𝐄 (f * g) := by rfl

lemma fourier_eq_inner : 𝓕 f S = ⟪χ S, f⟫ := by rfl

/-- Flip the `i₀`th bit of `x`. -/
def flipAt (i₀ : Fin n) (x : Fin n → Fin 2) : Fin n → Fin 2 := fun i ↦ if i = i₀ then 1 - x i else x i

/-- The `i₀`th bit of `x` is flipped. -/
@[simp]
lemma flipAt_flipped {i₀ : Fin n} {x : Fin n → Fin 2} : flipAt i₀ x i₀ = 1 - x i₀ := by
  unfold flipAt
  split_ifs <;> tauto

/-- Bits that are not the `i₀`th bits remain unchanged. -/
lemma flipAt_unflipped {i i₀ : Fin n} {x : Fin n → Fin 2} (h : i ≠ i₀) : flipAt i₀ x i = x i := by
  unfold flipAt
  split_ifs <;> tauto

/-- Flipping a bit twice results in no change. -/
@[simp]
lemma flipAt_flipAt_eq {i₀ : Fin n} {x : Fin n → Fin 2} : flipAt i₀ (flipAt i₀ x) = x := by
  unfold flipAt
  funext i
  split_ifs
  · rw [sub_sub_cancel]
  · rfl

/-- Flipping a bit is an involution on `Fin n → Fin 2`. -/
theorem flipAt_involutive {i₀ : Fin n} : Function.Involutive (flipAt i₀) := fun _ ↦ flipAt_flipAt_eq

/-- Flipping a bit is a bijection on `Fin n → Fin 2`. -/
theorem flipAt_bijective {i₀ : Fin n} : Function.Bijective (flipAt i₀) :=
    Function.Involutive.bijective (flipAt_involutive)

/-- Expectation of `χ S` is zero if `S` is nonempty -/
@[simp]
theorem expectation_walsh_eq_zero (hS : S.Nonempty) : 𝐄 (χ S) = 0 := by
  simp [expectation, walshCharacter]
  obtain ⟨i₀, hi₀⟩ := hS
  let e : (Fin n → Fin 2) ≃ (Fin n → Fin 2) := Equiv.addRight (Pi.single i₀ 1)

  have h_add_one (b : Fin 2) : (-1 : ℝ) ^ (b + 1).val = - ((-1) ^ b.val) := by fin_cases b <;> simp

  have : ∀ x, χ S (e x) = - χ S x := by
    intro x; unfold walshCharacter e
    simp [e, Pi.single_apply, ← Finset.prod_erase_mul S _ hi₀, h_add_one (x i₀), mul_neg]
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.ne_of_mem_erase hi), add_zero]
  have h_sum := e.sum_comp (χ S)
  simp [this] at h_sum
  linarith [this]

theorem walsh_orthogonal {S S' : Finset (Fin n)} (h : S ≠ S') : ⟪χ S, χ S'⟫ = 0 := by
  change 𝐄 _ = 0
  rw [walsh_mul_eq]
  apply expectation_walsh_eq_zero
  by_contra h1
  simp at h1
  exact h h1

theorem walsh_inner_eq : ⟪χ S, χ S'⟫ = oneOn (S = S') := by
  unfold oneOn
  split_ifs with h
  · rw [← h]; exact walsh_inner_self_eq_one
  · exact walsh_orthogonal h

theorem walsh_orthonormal : Orthonormal (ι := Finset (Fin n)) ℝ χ := ⟨walsh_norm_one, @walsh_orthogonal _⟩

/-- Basis of Walsh characters on `BooleanFunc n`. -/
abbrev walsh_basis : Basis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
  basisOfOrthonormalOfCardEqFinrank (v := χ) walsh_orthonormal (by simp)

/-- Orthonormal basis of Walsh characters on `BooleanFunc n`. -/
abbrev walsh_orthonormal_basis : OrthonormalBasis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
  Basis.toOrthonormalBasis (basisOfOrthonormalOfCardEqFinrank (v := χ) walsh_orthonormal (by simp))
    (by simp [walsh_orthonormal])

-- Q : Why does this not work:
-- def walsh_orthonormal_basis' : OrthonormalBasis (ι := Finset (Fin n)) ℝ (BooleanFunc n) :=
--     Basis.toOrthonormalBasis walsh_basis walsh_orthonormal
/-- Walsh-Fourier expansion : Every Boolean function is equal to a linear combination of Walsh characters. -/
theorem walsh_fourier (f : BooleanFunc n) : f = ∑ S : Finset (Fin n), (𝓕 f S)•χ S := by
  convert (OrthonormalBasis.sum_repr' walsh_orthonormal_basis f).symm <;> simp; rfl

lemma fourier_walsh : 𝓕 (χ S) S' = oneOn (S' = S) := walsh_inner_eq

/-- Plancherel/Parseval theorem for Boolean functions. -/
theorem inner_eq_sum_fourier : ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) := by
  convert OrthogonalFamily.inner_sum (Orthonormal.orthogonalFamily walsh_orthonormal) _ _ _ <;>
    exact walsh_fourier _

/-- Plancherel/Parseval theorem for Boolean functions. -/
theorem walsh_plancherel : ‖f‖^2 = ∑ S : Finset (Fin n), |𝓕 f S|^2 := by
  simp_rw [norm_sq_eq_inner, inner_eq_sum_fourier (f := f) (g := f), sq_abs, pow_two]

/-- Set the `i₀`th bit of `x` to `v`.
TODO : possibly use Mathlib's `Function.update` -/
abbrev setAt (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i ↦ if i = i₀ then v else x i

/-- The `i₀`th bit of `setAt i₀ v x` has value `v`. -/
@[simp]
lemma setAt_it (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) : setAt i₀ v x i₀ = v := by
  unfold setAt; split_ifs <;> tauto

/-- Bits other than the `i₀`th bit are unaffected by `setAt`. -/
lemma setAt_other (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) (i : Fin n) (h : i₀ ≠ i) : setAt i₀ v x i = x i := by
  unfold setAt; split_ifs <;> tauto

/-- Discrete partial "derivative" of a Boolean function with respect to the `i`th coordinate.
See Def. 2.16 in [odonnell2014]. -/
def dderiv (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := fun f ↦ fun x ↦ (f (setAt i 0 x) - f (setAt i 1 x)) / 2
  map_add' := by intros; funext; simp only [Pi.add_apply]; ring
  map_smul' := by intros; funext; dsimp; ring

lemma walsh_setAt_eq_ite : χ S (setAt i v x) = ite (i ∈ S) ((-1) ^ v.val * χ (S \ {i}) x) (χ S x) := by
  unfold walshCharacter
  split_ifs with h
  · rw [← mul_prod_erase S _ h, setAt_it, erase_eq]
    congr! 4 with j hj
    rw [setAt_other]
    rw [mem_sdiff, mem_singleton] at hj
    symm
    exact hj.right
  · congr! 3 with j hj
    rw [setAt_other]
    by_contra hc
    rw [hc] at h
    exact h hj

theorem dderiv_walsh (i : Fin n) (S : Finset (Fin n)) : dderiv i (χ S) = ite (i ∈ S) (χ (S \ {i})) 0 := by
  funext
  simp [dderiv]
  repeat rw [walsh_setAt_eq_ite]
  split_ifs <;> simp

theorem dderiv_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) : dderiv i f = ∑ S ∈ {S | i ∈ S}, 𝓕 f S•χ (S \ {i}) := by
  nth_rewrite 1 [walsh_fourier f]
  rw [map_sum, sum_filter]
  simp_rw [map_smul, dderiv_walsh]
  congr! 1; simp

/-- The `i`th coordinate Laplacian operator as in Def. 2.25 [odonnell2014].  -/
def laplace (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := {
  toFun := fun f ↦ fun x ↦ (f x - f (flipAt i x)) / 2
  map_add' := by intros; funext; simp only [Pi.add_apply]; ring
  map_smul' := by intros; funext; dsimp; ring
}

lemma setAt_eq_id (h : x i = v) : setAt i v x = x := by
  funext j
  unfold setAt
  split_ifs with hj
  · rw [hj]; symm; assumption
  · rfl

lemma setAt_eq_flipAt (h : x i ≠ v) : setAt i v x = flipAt i x := by
  funext j
  unfold setAt flipAt
  split_ifs with hj
  · rw [hj]; omega
  · rfl

lemma laplace_eq_dderiv (i : Fin n) (f : BooleanFunc n) (x : Fin n → Fin 2):
    laplace i f x = (-1) ^ (x i).val * (dderiv i f x) := by
  change (f x - _) / 2 = (-1)^_ * ( (_ - _) / 2 )
  by_cases hx : x i = 0
  · simp [hx]
    rw [setAt_eq_id hx, setAt_eq_flipAt (by rw [hx]; trivial)]
  · have hx1 := Fin.eq_one_of_neq_zero (x i) hx
    rw [setAt_eq_id hx1, setAt_eq_flipAt hx]
    simp [hx1]; ring

theorem laplace_walsh (i : Fin n) (S : Finset (Fin n)) : laplace i (χ S) = ite (i ∈ S) (χ S) 0 := by
  funext x
  rw [laplace_eq_dderiv, dderiv_walsh]
  split_ifs with h
  · unfold walshCharacter
    rw [← erase_eq, mul_prod_erase (s := S) (a := i) (f := fun i ↦ (-1 : ℝ) ^ (x i).val) h]
  · simp only [Pi.zero_apply, mul_zero]

theorem laplace_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) : laplace i f = ∑ S ∈ {S | i ∈ S}, 𝓕 f S•χ (S) := by
  nth_rewrite 1 [walsh_fourier f]
  rw [map_sum, sum_filter, sum_congr (by rfl)]
  intros
  rw [map_smul, laplace_walsh]
  simp

/-- The `i`th influence of a Boolean function is defined as the expectation of the `i`th Laplacian squared. -/
abbrev influence (f : BooleanFunc n) (i : Fin n) : ℝ := 𝐄 ((laplace i f) ^ 2)

theorem influence_eq_sum_fourier (f : BooleanFunc n) (i : Fin n):
    influence f i = ∑ S ∈ {S | i ∈ S}, (𝓕 f S) ^ 2 := by
  unfold influence
  nth_rewrite 1 [laplace_eq_sum_fourier]
  -- todo: simplify
  rw [pow_two, sum_mul_sum, map_sum, sum_filter]
  conv =>
    enter [1, 2, S]
    conv =>
      arg 2
      rw [map_sum]
      enter [2, S']
      rw [mul_smul_comm, map_smul, smul_mul_assoc, map_smul]
      rw [← inner_eq_expectation, walsh_inner_eq]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_filter,
      mem_univ, true_and, ite_ite_same]
  rw [← sum_filter]
  congr! 1; ring

/-- The total influence of a Boolean function is defined as the sum of the `i`th influences. -/
abbrev totalInfluence (f : BooleanFunc n) : ℝ := ∑ i, influence f i

theorem totalInfluence_eq_sum_fourier (f : BooleanFunc n) : totalInfluence f = ∑ S, S.card * (𝓕 f S) ^ 2 := by
  unfold totalInfluence
  conv =>
    enter [1, 2, i]
    rw [influence_eq_sum_fourier f i, sum_filter]
  rw [sum_comm]
  simp

/-- Covariance of two Boolean functions -/
abbrev covariance (f g : BooleanFunc n) : ℝ := 𝐄 (f * g) - 𝐄 f * 𝐄 g

/-- Variance of a Boolean function defined via covariance -/
abbrev variance (f : BooleanFunc n) : ℝ := covariance f f

theorem covariance_eq_sum_fourier (f g : BooleanFunc n) : covariance f g = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, 𝓕 f S * 𝓕 g S := by
  unfold covariance
  rw [← inner_eq_expectation, inner_eq_sum_fourier]
  simp [Finset.nonempty_iff_ne_empty, Finset.filter_ne', expectation_eq_fourier]

theorem variance_eq_sum_fourier (f : BooleanFunc n) : variance f = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, (𝓕 f S) ^ 2 := by
  convert covariance_eq_sum_fourier f f; exact pow_two _

/-- L² Poincaré inequality : variance of a Boolean function is ≤ total Influence.
See [odonnell2014], Sec. 2.3. -/
theorem variance_le_totalInfluence (f : BooleanFunc n) : variance f ≤ totalInfluence f := by
  rw [variance_eq_sum_fourier, totalInfluence_eq_sum_fourier, sum_filter]
  gcongr with S
  split_ifs with h
  · nth_rewrite 1 [← one_mul ((𝓕 f S)^2)]
    gcongr
    simp only [Nat.one_le_cast, one_le_card, h]
  · rw [← zero_mul 0]
    gcongr
    simp only [Nat.cast_nonneg]
    exact sq_nonneg (𝓕 f S)


section FourierWeight
-- some redundancy in this section

/-- The `k`th Fourier weight is the sum of squares of degree `k` Fourier coefficients -/
abbrev fourierWeight (k : ℕ) (f : BooleanFunc n) : ℝ := ∑ S ∈ {S | S.card = k}, |𝓕 f S| ^ 2

/-- Alternative expression for degree one Fourier weight in terms in terms of sum over coordinates -/
abbrev fourierWeightOne (f : BooleanFunc n) : ℝ := ∑ i, |𝓕 f {i}| ^ 2

lemma fourier_weight_one {f : BooleanFunc n} : fourierWeight 1 f = fourierWeightOne f := by
  apply sum_singletons; intro; rfl

lemma fourier_eq_zero_iff_fourier_weight_eq {k : ℕ} {f : BooleanFunc n}:
    (∀ S, S.card ≠ k → 𝓕 f S = 0) ↔ fourierWeight k f = ‖f‖ ^ 2 := by
  constructor
  · intro h
    have h : ∀ S, S.card ≠ k → |𝓕 f S|^2 = 0 := by intro S hS; simp; exact h S hS
    symm
    rw [walsh_plancherel]
    calc
      _ = fourierWeight k f + ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2 := by
        rw [sum_filter_add_sum_filter_not]
      _ = fourierWeight k f + ∑ S, if S.card ≠ k then |𝓕 f S|^2 else 0 := by
        rw [sum_filter]
      _ = fourierWeight k f := by
        conv => {enter [1, 2, 2, S]; rw [rw_ite_left (h S), ite_self]}; simp
  · intro h S hS
    have : ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2 = 0 := by
      symm
      calc
        0 = ‖f‖^2 - ‖f‖^2                           := (sub_self _).symm
        _ = ∑ S, |𝓕 f S|^2 - fourierWeight k f      := by rw [h, walsh_plancherel]
        _ = ∑ S ∈ {S | S.card = k}, |𝓕 f S|^2 + ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2
          - fourierWeight k f                       := by rw [sum_filter_add_sum_filter_not]
        _ = ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2       := by rw [add_comm, add_sub_assoc, sub_self, add_zero]
    have := (sum_eq_zero_iff_of_nonneg <| by intro S _; apply pow_two_nonneg).mp this
    specialize this S (by simp [hS])
    rw [sq_abs, pow_eq_zero_iff (by trivial)] at this
    assumption

lemma eq_sum_fourier_of_fourier_weight {k : ℕ} {f : BooleanFunc n} (h : fourierWeight k f = ‖f‖ ^ 2):
    f = ∑ S ∈ {S|S.card = k}, 𝓕 f S • χ S := by
  have hf : ∑ S ∈ {S | S.card ≠ k}, 𝓕 f S • χ S = 0 := by
    rw [sum_eq_zero]
    intro S hS
    rw [smul_eq_zero]
    left
    simp at hS
    exact fourier_eq_zero_iff_fourier_weight_eq.mpr h S hS
  calc
    f = ∑ S, 𝓕 f S•χ S                     := walsh_fourier f
    _ = ∑ S ∈ {S | S.card = k}, 𝓕 f S•χ S +
      ∑ S ∈ {S | S.card ≠ k}, 𝓕 f S•χ S     := by rw [sum_filter_add_sum_filter_not]
    _ = ∑ S ∈ {S | S.card = k}, 𝓕 f S•χ S    := by rw [hf, add_zero]

lemma fourier_expansion (f : BooleanFunc n) :
  f = ∑ S, fourierTransform f S • χ S := by
  sorry

lemma eq_sum_degree_one_of_fourier_weight_one {f : BooleanFunc n} (h : fourierWeight 1 f = ‖f‖ ^ 2) :
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by
  intro
  nth_rewrite 1 [eq_sum_fourier_of_fourier_weight h, sum_apply]
  apply sum_singletons
  intro
  simp only [Pi.smul_apply, prod_singleton, smul_eq_mul]

lemma eq_sum_degree_one_of_fourier_eq_zero {f : BooleanFunc n} (h : ∀ S, S.card ≠ 1 → 𝓕 f S = 0):
    ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val :=
  eq_sum_degree_one_of_fourier_weight_one (fourier_eq_zero_iff_fourier_weight_eq.mp h)

lemma eq_const_of_degree_zero {f : BooleanFunc n} (h : ∀ S, S.card ≠ 0 → 𝓕 f S = 0) :
    ∃ c, ∀ x, f x = c := by
  use (𝓕 f ∅)
  intro x
  rw [fourier_expansion f]
  rw [Finset.sum_eq_single ∅]
  · simp; sorry
  . intros S hS h_ne
    have h_card : S.card ≠ 0 := by rw [Finset.card_ne_zero]; rw [Finset.nonempty_iff_ne_empty]; exact h_ne
    simp [h S h_card]
  · simp

end FourierWeight

section Multiplier

/-- Walsh-Fourier multiplier as an ℝ-linear operator on Boolean functions -/
def multiplier (m : ℕ → ℝ) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := {
  toFun := fun f ↦ ∑ S : Finset (Fin n), (m S.card) • 𝓕 f S • χ S
  map_add' := by
    intros; ext; dsimp
    repeat rw [sum_apply]
    rw [← sum_add_distrib, sum_congr (by rfl)]
    intros
    simp only [map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' := by
    intros; ext
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, sum_apply, RingHom.id_apply, mul_sum]
    congr! 1; ring
}

/-- Walsh characters are eigenfunctions of multipliers. -/
lemma multiplier_walsh {m : ℕ → ℝ} {S : Finset (Fin n)} : multiplier m (χ S) = (m S.card)•χ S := by
  unfold multiplier
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [1, 2, S']; rw [fourier_walsh]
  simp

/-- The noise operator defined via Fourier expansion. See Prop. 2.47 in [odonnell2014]. -/
abbrev noise_operator (ρ : ℝ) : BooleanFunc n →ₗ[ℝ] BooleanFunc n := multiplier (ρ^·)

/-- Noise stability  -/
abbrev noise_stability (ρ : ℝ) (f : BooleanFunc n) := ⟪f, noise_operator ρ f⟫

lemma noise_stability_eq_sum_fourier {ρ : ℝ} : noise_stability ρ f = ∑ S, ρ^(S.card) * |𝓕 f S|^2 := by
  unfold noise_stability
  nth_rewrite 1 [walsh_fourier f]
  simp only [noise_operator, multiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rewrite [sum_inner]
  conv => enter [1, 2, S]; rw [inner_smul_left, inner_sum];
          enter [2, 2, S']; rw [inner_smul_right, inner_smul_right, walsh_inner_eq]
  congr! 1; simp; ring

end Multiplier

section Convolution

/-- Discrete convolution of Boolean functions -/
abbrev convolution (f g : BooleanFunc n) : BooleanFunc n := fun x ↦ 𝐄 (fun y ↦ (f y) * (g (x + y)))

/-- Discrete convolution of Boolean functions -/
infixl : 67 "⋆" => convolution

-- lemma convolution_comm : f⋆g = g⋆f := by
--   sorry

-- lemma convolution_assoc : f⋆g⋆h = f⋆(g⋆h) := by
--   sorry

/-- Convolution theorem : the Walsh-Fourier transform turns convolution into pointwise product. -/
lemma fourier_convolution : 𝓕 (f ⋆ g) = (𝓕 f) * (𝓕 g) := by
  funext S
  unfold fourierTransform convolution expectation
  dsimp
  simp_rw [mul_sum]; rw [sum_comm]
  conv => enter [1, 2, y]; rw [sum_translate y]
  simp_rw [walsh_add]
  rw [sum_comm]
  -- reorder -- there should be short tactics for these things
  simp_rw [sum_mul]
  apply sum_congr (by rfl)
  intro y _
  apply sum_congr (by rfl)
  intro x _
  ring_nf
  rw [two_eq_zero, mul_zero, add_zero]

end Convolution

section Contractivity

noncomputable
def Ei (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun f := fun x => (f (setAt i 0 x) + f (setAt i 1 x)) / 2
  map_add' f g := by
    ext x; simp; ring
  map_smul' c f := by
    ext x; simp; ring


instance : Sub (BooleanFunc n) := Pi.instSub
instance : Pow (BooleanFunc n) ℕ := Pi.instPow

lemma BooleanFunc.congr {f : BooleanFunc n} {x y : Fin n → Fin 2} (h : x = y) :
    f x = f y := by
  rw [h]

theorem decomposition (i : Fin n) (f : BooleanFunc n) (x : Fin n → Fin 2) :
    f x = ((-1) ^ (x i).val) * ((dderiv i f) x)  + ((Ei i f) x) := by
  simp [dderiv, Ei]
  match h: x i with
  | 0 =>
      simp
      field_simp
      apply f.congr;
      funext j
      unfold setAt
      split_ifs with hj
      . rw [← hj] at h
        exact h
      simp
  | 1 =>
      simp
      field_simp
      ring_nf
      field_simp
      apply f.congr;
      funext j
      unfold setAt
      split_ifs with hj
      . rw [← hj] at h
        exact h
      simp

theorem decomposition' (i : Fin n) (f : BooleanFunc n) :
  f = fun x => (((-1) ^ (x i).val) * (dderiv i f x) + (Ei i f x)) := by
  --simp [dderiv, Ei]
  funext x
  exact decomposition i f x

def DependsOnlyOn (f : BooleanFunc n) (J : Finset (Fin n)) : Prop :=
  ∀ x y : Fin n → Fin 2, (∀ i ∈ J, x i = y i) → f x = f y

def Independent (f g : BooleanFunc n) : Prop :=
  ∃ J₁ J₂ : Finset (Fin n), DependsOnlyOn f J₁ ∧ DependsOnlyOn g J₂ ∧ Disjoint J₁ J₂

def IndependentOfLast {n : ℕ} (f : BooleanFunc (n + 1)) : Prop :=
  DependsOnlyOn f (Finset.univ.erase (Fin.last n))

lemma DependsOnlyOn.mul {f g : BooleanFunc n} {S : Finset (Fin n)}
    (hf : DependsOnlyOn f S) (hg : DependsOnlyOn g S) :
    DependsOnlyOn (f * g) S := by
  intro x y h; simp [hf x y h, hg x y h]

lemma DependsOnlyOn.pow {f : BooleanFunc n} {S : Finset (Fin n)} (k : ℕ)
    (hf : DependsOnlyOn f S) :
    DependsOnlyOn (f ^ k) S := by
  intro x y h; simp [hf x y h]

def Ei.DependsOnlyOn (i : Fin n) (f : BooleanFunc (n)) :
  DependsOnlyOn (Ei i f) (Finset.univ.erase i) := by
  intro x y h; unfold Ei; simp
  congr 1
  congr 1
  . sorry
  . sorry



lemma expectation_mul_of_independent' (f g : BooleanFunc n) (hI : Independent f g) :
  𝐄 (f * g) = 𝐄 f * 𝐄 g := by
  obtain ⟨S, T, hST⟩ := hI
  sorry

-- TODO: swap these.
lemma expectation_mul_of_independent (f g : BooleanFunc n)
    (S T : Finset (Fin n)) (hS : DependsOnlyOn f S) (hT : DependsOnlyOn g T)
    (h_disjoint : Disjoint S T) :
    𝐄 (f * g) = 𝐄 f * 𝐄 g := by
  unfold expectation
  simp
  field_simp
  ring_nf
  admit

def degree (f : BooleanFunc n) : ℕ :=
  let f_hat := fourierTransform f
  let support_sets := Finset.univ.filter (fun S ↦ f_hat S ≠ 0)
  support_sets.sup Finset.card


lemma eq_const_of_degree_zero' (f : BooleanFunc n) (h : degree f = 0) :
  ∃ c, ∀ x, f x = c := by
  rw [fourier_expansion f]
  use 𝓕 f ∅
  rw [Finset.sum_eq_single ∅]
  . simp
  . intro S hS hne
    have h_coeff_zero : ∀ S : Finset (Fin n), S ≠ ∅ → 𝓕 f S = 0 := by
      intro S hne
      by_contra h_nz
      have mem : S ∈ univ.filter (fun S ↦ 𝓕 f S ≠ 0) := by simp [h_nz]
      have le_deg : #S ≤ degree f := Finset.le_sup mem
      rw [h] at le_deg
      have : #S = 0 := Nat.le_zero.mp le_deg
      have : S = ∅ := Finset.card_eq_zero.mp this
      contradiction
    rw [h_coeff_zero S hne]
    simp
  . simp


def restrict {n : ℕ} (g : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x ↦ g (Fin.append x (fun _ ↦ 0))

def BooleanFunc.lower {n : ℕ} (f : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x ↦ f (Fin.append x (fun _ ↦ 0))

def BooleanFunc.lift {n : ℕ} (f : BooleanFunc n) : BooleanFunc (n + 1) :=
  fun x ↦ f (Fin.init x)

lemma lower_lift_eq_id (f : BooleanFunc (n+1)) :
  f.lower.lift = f := by
  unfold BooleanFunc.lift
  unfold BooleanFunc.lower
  sorry -- this is only true if independent of the last bit.

lemma lift_lower_eq_id (f : BooleanFunc n) :
  f.lift.lower = f := by
  unfold BooleanFunc.lower
  unfold BooleanFunc.lift
  funext x
  sorry

/-- if g depends on on its first n coords, we can restrict down to n with the same expectation. -/
lemma expectation_restrict {n : ℕ} (g : BooleanFunc (n + 1))
    (h : DependsOnlyOn g (Finset.univ.erase (Fin.last n))) :
    expectation g = expectation (restrict g) := by
  unfold expectation;
  have h_split : ∑ x : Fin (n + 1) → Fin 2, g x = ∑ x : Fin n → Fin 2, ∑ y : Fin 2, g (Fin.append x (fun _ => y)) := by
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => ( x ∘ Fin.castSucc, x ( Fin.last _ ) ) ) _ _ _ _ <;> simp +decide;
    · exact fun a₁ a₂ h₁ h₂ => funext fun i => by cases i using Fin.lastCases <;> simpa [ * ] using congr_fun h₁ ‹_›;
    · --exact fun a => ⟨ ⟨ Fin.snoc a 0, by ext i; simp +decide, by simp +decide ⟩, ⟨ Fin.snoc a 1, by ext i; simp +decide, by simp +decide ⟩ ⟩;
      intro a b
      use Fin.snoc a b
      constructor
      . ext i
        simp
      . simp
    · intro a; congr; ext i; induction i using Fin.lastCases <;> simp +decide [ *, Fin.append ] ;
      · simp +decide [ Fin.addCases ];
      · simp +decide [ Fin.addCases ];
  have h_eq : ∀ x : Fin n → Fin 2, ∀ y : Fin 2, g (Fin.append x (fun _ => y)) = g (Fin.append x (fun _ => 0)) := by
    intro x y; apply h; intro i hi; simp_all +decide [ Fin.append ] ;
    cases i using Fin.lastCases <;> simp_all +decide [ Fin.addCases ];
  simp_all +decide [ pow_succ, div_mul_eq_div_div ];
  rw [ ← Finset.mul_sum _ _ _ ] ; ring!;

lemma expectation_lower (f : BooleanFunc (n+1)) (h : IndependentOfLast f) :
  𝐄 f = 𝐄 f.lower := by
  unfold IndependentOfLast at h
  exact expectation_restrict f h

lemma noise_independent {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) (h : IndependentOfLast f) :
  noise_operator ρ f =  (noise_operator ρ (f.lower)).lift := by
  sorry

lemma norm_independent {n : ℕ} (p : ℕ) (f : BooleanFunc (n + 1)) (h : IndependentOfLast f) :
  𝐄 (f ^ p) = 𝐄 ((f.lower) ^ p) := by
  sorry



lemma depends_chi_pow {xₙ : BooleanFunc (n+1)} (hx : xₙ = fun x ↦ (-1) ^ (x (Fin.last n)).val) (k : ℕ) : DependsOnlyOn (xₙ ^ k) {Fin.last n} := by
  intro x y h
  rw [hx]
  simp_all

lemma  dependsOnlyOn_d (f : BooleanFunc n) (i : Fin n) :
    DependsOnlyOn (dderiv i f) (Finset.univ.erase i) := by
  intro x y hxy
  unfold dderiv
  simp
  field_simp
  congr 1
  · apply f.congr
    unfold setAt
    funext j
    split_ifs with hj
    . simp
    . apply hxy; simp [hj]
  . apply f.congr
    unfold setAt
    funext j
    split_ifs with hj
    . simp
    . apply hxy; simp [hj]

lemma dependsOnlyOn_e (f : BooleanFunc n) (i : Fin n) :
    DependsOnlyOn (Ei i f) (Finset.univ.erase i) := by
  intro x y hxy
  unfold Ei
  simp
  field_simp
  congr 1
  · apply BooleanFunc.congr
    funext j
    unfold setAt
    split_ifs with hj
    · rfl
    · apply hxy
      simp [hj]
  · apply BooleanFunc.congr
    funext j
    unfold setAt
    split_ifs with hj
    · rfl
    · apply hxy
      simp [hj]

lemma depends_de_prod (a b : ℕ) {f d e : BooleanFunc (n+1)}
   (hd : d = (dderiv (Fin.last n)) f) (he : e = (Ei (Fin.last n)) f) :
    DependsOnlyOn (d^a * e^b) (Finset.univ.erase (Fin.last n)) := by
  apply DependsOnlyOn.mul
  · apply DependsOnlyOn.pow
    rw [hd]
    exact dependsOnlyOn_d f (Fin.last n)
  · apply DependsOnlyOn.pow
    rw [he]
    exact dependsOnlyOn_e f (Fin.last n)


lemma expectation_mul_const_func (c : ℝ) (g : BooleanFunc (n + 1)) :
    𝐄 ((fun _ ↦ c) * g) = c * 𝐄 g := by
  have h_smul : (fun x ↦ c) * g = c • g := by
    ext x
    simp [Pi.mul_apply, Pi.smul_apply]
  rw [h_smul]
  exact expectation.map_smul c g

lemma expectation_const_func (c : ℝ) :
  𝐄 ((fun _ ↦ c) : BooleanFunc n) = c := by
  sorry

lemma expectation_const_power (c : ℝ) (k : ℕ) :
  𝐄 ((fun _ ↦ c) ^ k : BooleanFunc n) = c ^ k := by
  simp [expectation]

lemma chi_pow_reduce (xₙ : BooleanFunc (n + 1))
    (hx : xₙ = fun x ↦ (-1) ^ (x (Fin.last n)).val) (k : ℕ) :
    xₙ ^ k = if k % 2 = 0 then 1 else xₙ := by
  ext x
  rw [hx]
  simp only [Pi.pow_apply, Pi.one_apply]
  match kk : (x (Fin.last n)) with
  | 0 =>
    simp
    split_ifs
    . simp
    . simp [kk]
  | 1 =>
    split_ifs
    · simp; sorry -- use the powOne api stuff
    · have h_odd : ∃ m, k = 2 * m + 1 := sorry
      rcases h_odd with ⟨m, rfl⟩
      rw [pow_succ]
      simp
      rw [kk]
      simp


lemma restrict_pow {n : ℕ} (f : BooleanFunc (n + 1)) (p : ℕ) :
    restrict (f^p) = (restrict f)^p := by
  ext x
  simp [restrict, Pi.pow_apply]

lemma dderiv_const {n : ℕ} (c : ℝ) (i : Fin (n + 1)) :
    dderiv i (λ _ => c) = 0 := by
  ext x
  simp [dderiv]

lemma degree_dderiv_le {n : ℕ} (f : BooleanFunc (n + 1)) (i : Fin (n + 1)) :
    degree (dderiv i f) ≤ degree f - 1 := by
  sorry

lemma degree_restrict_le {n : ℕ} (g : BooleanFunc (n + 1)) :
    degree (restrict g) ≤ degree g := by
  sorry

lemma norm_eq_sqrt_inner : ‖f‖ = √⟪f,f⟫ := by sorry -- add nonneg assumption

lemma degree_Ei_le (i : Fin n) (f : BooleanFunc n) :
  degree (Ei i f) ≤ degree f := by
  unfold degree
  simp
  unfold Ei
  simp
  intro b
  intro h_nonzero
  have h_not_in : i ∉ b := by
    contrapose! h_nonzero
    sorry
  have h_eq_f : 𝓕 (Ei i f) b = 𝓕 f b := by
    unfold fourierTransform
    simp
    unfold Ei
    simp
    sorry
  sorry

lemma Cube_zero_eq_const (f : BooleanFunc 0) :
  ∃c, ∀ x, f x = c := by
  simp

lemma exp_pow_restrict {n : ℕ} (f : BooleanFunc (n + 1)) (p : ℕ) (h : IndependentOfLast f) :
  𝐄 (f^p) = 𝐄 ((restrict f)^p) := by
  rw [expectation_restrict (f^p) (DependsOnlyOn.pow p h), restrict_pow]

lemma ih_transfer {n : ℕ} (f : BooleanFunc (n + 1)) (h : IndependentOfLast f)
  (P : ∀ {m}, BooleanFunc m → Prop) :
  P (restrict f) → P f := by
  sorry

set_option profiler true
lemma bonamis_lemma (f : BooleanFunc n) (k : ℕ) (h_def : degree f ≤ k) :
  𝐄 (f ^ 4) ≤ 9^k * (𝐄 (f ^ 2)) ^ 2 := by
  revert k f
  induction n with
  | zero =>
    intro f k hk
    obtain ⟨c, h⟩ := Cube_zero_eq_const f
    have hf : f = (λ _ => c) := by funext x; exact h x
    rw [hf]
    simp_rw [expectation_const_power]
    ring
    nth_rewrite 1 [← mul_one (c ^ 4)]
    apply mul_le_mul_of_nonneg_left
    . exact one_le_pow₀ (a := 9) (by norm_num)
    . positivity
  | succ n' ih =>
    intro f k hk
    rw [pow_succ, pow_succ, pow_succ, pow_one]
    rw [decomposition' (Fin.last (n')) f]
    set d := dderiv (Fin.last n') f with hd
    set e := Ei (Fin.last n') f with he
    set xₙ := fun x : Fin (n' + 1) → Fin 2 ↦ (-1 : ℝ) ^ (x (Fin.last n')).val with hχ

    change 𝐄 ((xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e)) ≤
       9 ^ k * 𝐄 ((xₙ * d + e) * (xₙ * d + e)) ^ 2
    have h_expand : (xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e) =
                xₙ^4 * d^4 + 4 * (xₙ^3 * (d^3 * e)) + 6 * (xₙ^2 * (d^2 * e^2)) + 4 * (xₙ * (d * e^3)) + e^4 := by
      ring
    have h_expand_2 : (xₙ * d + e) * (xₙ * d + e) = (xₙ ^ 2 * d ^ 2) + 2 * (xₙ * (d * e)) + e ^ 2 := by
      ring
    rw [h_expand, h_expand_2]
    clear h_expand h_expand_2
    repeat rw [map_add]

    have h_zero : 𝐄 xₙ = 0 := by
      have hz : 𝐄 (χ {Fin.last n'}) = 0 :=
        expectation_walsh_eq_zero (Finset.singleton_nonempty (Fin.last n'))
      unfold walshCharacter at hz
      simp_rw [Finset.prod_singleton] at hz
      simp_rw [hχ]
      exact hz

    have h4 : (4 : BooleanFunc (n' + 1)) = (fun _ ↦ (4 : ℝ)) := rfl
    have h6 : (6 : BooleanFunc (n' + 1)) = (fun _ ↦ (6 : ℝ)) := rfl
    have h2 : (2 : BooleanFunc (n' + 1)) = (fun _ ↦ (2 : ℝ)) := rfl

    have dep_d_4 : DependsOnlyOn (d ^ 4) (univ.erase (Fin.last n')) := by
      rw [← mul_one (d^4)]; rw [← pow_zero e]; exact depends_de_prod 4 0 hd he

    have dep_e_4 : DependsOnlyOn (e ^ 4) (univ.erase (Fin.last n')) := by
      rw [← one_mul (e ^ 4)]; rw [← pow_zero d]; exact depends_de_prod 0 4 hd he

    have dep_d_n (s : ℕ) : DependsOnlyOn  (d ^ s) (univ.erase (Fin.last n')) := by
      rw [← mul_one (d ^ s)]; rw [← pow_zero e]; exact depends_de_prod s 0 hd he

    have dep_e_n (s : ℕ) : DependsOnlyOn (e ^ s) (univ.erase (Fin.last n')) := by
      rw [←one_mul (e ^ s)]; rw [← pow_zero d]; exact depends_de_prod 0 s hd he

    have dep_xₙ : DependsOnlyOn xₙ {Fin.last n'} := by
      unfold DependsOnlyOn; simp; unfold xₙ; intro x y; intro cond; sorry

    have e4_nn : 0 ≤ 𝐄 (e ^ 4) := by
      have : e ^ 4 = (e ^ 2) * (e ^ 2) := by ring
      rw [this]
      rw [← inner_eq_expectation]
      exact real_inner_self_nonneg

    have d4_nn : 0 ≤ 𝐄 (d ^ 4) := by
      have : d ^ 4 = (d ^ 2) * (d ^ 2) := by ring
      rw [this]
      rw [← inner_eq_expectation]
      exact real_inner_self_nonneg

    repeat rw [h4]
    rw [h6]
    rw [h2]
    repeat rw [expectation_mul_const_func 4 _]
    rw [expectation_mul_const_func 6 _]
    rw [expectation_mul_const_func 2 _]

    simp
    nth_rw 1 5 [← pow_one e]
    nth_rw 4 6 [← pow_one d]
    have disj : Disjoint {Fin.last n'} (Finset.univ.erase (Fin.last n')) := by
      simp
    rw [expectation_mul_of_independent (xₙ^4) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (depends_chi_pow hχ 4) (dep_d_4) disj]
    rw [expectation_mul_of_independent (xₙ^2) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (depends_chi_pow hχ 2) (dep_d_n 2) disj]
    rw [expectation_mul_of_independent (xₙ^3) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (depends_chi_pow hχ 3) (depends_de_prod 3 1 hd he) disj]
    rw [expectation_mul_of_independent (xₙ) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (dep_xₙ) (depends_de_prod 1 1 hd he) disj]
    rw [BooleanFun.chi_pow_reduce xₙ hχ 3]; simp only [Nat.reduceMod, one_ne_zero, ↓reduceIte]
    rw [BooleanFun.chi_pow_reduce xₙ hχ 4]; simp only [Nat.reduceMod, one_ne_zero, ↓reduceIte]
    rw [BooleanFun.chi_pow_reduce xₙ hχ 2]; simp only [Nat.reduceMod, one_ne_zero, ↓reduceIte]
    rw [expectation_mul_of_independent (xₙ) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (dep_xₙ) (depends_de_prod 1 3 hd he) disj]



    simp_rw [h_zero]; simp

    rw [expectation_restrict (d^4) dep_d_4]
    rw [restrict_pow]
    have ihd := ih (restrict d)
    repeat rw [← restrict_pow] at ihd
    rw [← expectation_restrict (d^4) (dep_d_n 4)] at ihd
    rw [← expectation_restrict (d^2) (dep_d_n 2)] at ihd
    have h_deg : degree (restrict d) ≤ k - 1 := by
      have : degree d ≤ k-1 := by
        unfold d
        have : k - 1 ≤ degree f := by
          simp [hk]
          sorry
        sorry
      sorry
    have hbd := ihd (k := k - 1) h_deg
    rw [← restrict_pow]
    rw [← expectation_restrict (d^4) dep_d_4]
    have cs : 𝐄 (d^2 * e^2) ≤ (𝐄 (d^4))^(1/2 : ℝ) * (𝐄 (e^4))^(1/2 : ℝ) := by
      rw [inner_eq_expectation.symm]
      calc ⟪d^2, e^2⟫
        _ ≤ ‖d^2‖ * ‖e^2‖ := real_inner_le_norm _ _
        _ = (𝐄 (d^4))^(1/2 : ℝ) * (𝐄 (e^4))^(1/2 : ℝ) := by
          simp [norm_eq_sqrt_inner, inner_eq_expectation, sqrt_eq_rpow]
          ring_nf

    rw [exp_pow_restrict e 4]
    rotate_left
    . sorry

    have ihe := ih (restrict e)
    repeat rw [← restrict_pow] at ihe
    rw [← expectation_restrict (e^4) (dep_e_n 4)] at ihe
    rw [← expectation_restrict (e^2) (dep_e_n 2)] at ihe
    have e_deg : degree (restrict (e)) ≤ k := by
      -- Expedite this proof
      sorry
    have hbe := ihe k e_deg
    rw [← exp_pow_restrict e 4]
    rotate_left
    . sorry
    cases k with
    | zero =>
      simp at h_deg
      simp at hbe
      rw [sq]; ring;
      nth_rw 2 [add_comm]
      nth_rw 1 [mul_comm, mul_assoc]
      rw [le_zero_iff] at hk
      have deriv : d = 0 := by
        unfold d
        obtain ⟨cf, hcf⟩ := eq_const_of_degree_zero' f hk
        ext x
        simp [dderiv, hcf]
      simp [deriv, hbe]
    | succ k' =>
      have h_mid : 6 * (9^k' * 𝐄 (d^2)^2 * 9^(k'+1) * 𝐄 (e^2)^2)^(1/2 : ℝ) = 18 * 9^k' * 𝐄 (d^2) * 𝐄 (e^2) := by
        simp; ring_nf; rw [← Real.sqrt_eq_rpow]; rw [Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul]
        rw [Real.sqrt_sq, Real.sqrt_sq]; ring_nf
        simp_rw [sq]
        rw [pow_mul]; rw [Real.sqrt_sq];
        have nine : (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
        nth_rw 2 [nine]; rw [Real.sqrt_sq];
        ring
        . norm_num
        . exact pow_nonneg (show (0 : ℝ) ≤ 9 by norm_num) (k')
        . rw [sq]; exact expectation_prod_self_nonneg
        . rw [sq]; exact expectation_prod_self_nonneg
        . simp_rw [sq_nonneg]
        . positivity
        . positivity
      calc
        𝐄 (d^4) + 6 * 𝐄 (d^2 * e^2) + 𝐄 (e^4)
          ≤ 9^(k') * 𝐄 (d^2) ^ 2 + 6 * (𝐄 (d^4) ^(1/2 : ℝ) * 𝐄 (e^4)^(1/2 : ℝ)) + 9^(k'+1) * 𝐄 (e^2)^2 := by
            gcongr;
            . exact hbd
        _ ≤ 9^(k') * 𝐄 (d^2)^2 + 6 * ((9^(k') * 𝐄 (d^2)^2) * 9^(k'+1) * 𝐄 (e^2)^2)^(1/2 : ℝ) + 9^(k'+1) * 𝐄 (e^2)^2 := by
            gcongr
            repeat rw [← Real.sqrt_eq_rpow]
            rw [← Real.sqrt_mul, Real.sqrt_le_sqrt_iff _, mul_assoc (b := (9 ^ (k' + 1)))]
            gcongr
            . exact hbd
            . positivity
            . exact d4_nn
        _ = ((9:ℝ)^(k') * 𝐄 (d^2)^2) + (2 * 9^(k'+1) * 𝐄 (d^2) * 𝐄 (e^2)) + (9^(k'+1) * 𝐄 (e^2)^2) := by
            erw [h_mid]; field_simp;
            apply Or.inl; apply Or.inl
            ring
        _ ≤ 9^(k' + 1) * 𝐄 (d^2)^2 + 2 * 9^(k'+1) * 𝐄 (d^2) * 𝐄 (e^2) + 9^(k'+1) * 𝐄 (e^2)^2 := by
            ring_nf; field_simp;
            apply le_mul_of_one_le_right
            · positivity
            · norm_num
        _ ≤ 9^(k' + 1) * (𝐄 (d^2) + 𝐄 (e^2))^2 := by
            ring_nf; rfl



lemma hypercontractive_ineq_2_4 (f : BooleanFunc n) :
  let p := 2; let q := 4; let ρ := (1/√3);
  let T := noise_operator ρ;
  𝐄 ((T f)^4) ≤ 𝐄 (f ^ 2) ^ 2 := by
  sorry


end Contractivity

end

--#lint
--#min_imports
