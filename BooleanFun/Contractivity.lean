import BooleanFun.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.SymmDiff
set_option checkBinderAnnotations false
open BooleanFun
open scoped Finset
open RealInnerProductSpace

variable {n : ℕ} {f g : BooleanFunc n}


theorem decomposition' (i : Fin n) (f : BooleanFunc n) :
  f = fun x => (((-1) ^ (x i).val) * (dderiv i f x) + (expectation_op i f x)) := by
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

def DependsOnlyOn_Ei (i : Fin n) (f : BooleanFunc (n)) :
  DependsOnlyOn (expectation_op i f) (Finset.univ.erase i) := by
  intro x y h; unfold expectation_op; simp
  congr 1; congr 1
  all_goals (
    congr 1
    ext j
    by_cases hj : j = i
    . simp [hj]
    . simp [setAt, h, hj]
  )

-- lemma expectation_mul_of_independent' (f g : BooleanFunc n) (hI : Independent f g) :
--   𝐄 (f * g) = 𝐄 f * 𝐄 g := by
--   obtain ⟨S, T, hST⟩ := hI
--   sorry --

lemma expectation_mul_const_func (c : ℝ) (g : BooleanFunc (n)) :
    𝐄 ((fun _ ↦ c) * g) = c * 𝐄 g := by
  have h_smul : (fun x ↦ c) * g = c • g := by
    ext x
    simp [Pi.mul_apply, Pi.smul_apply]
  rw [h_smul]
  exact expectation.map_smul c g

lemma expectation_mul_of_independent (f g : BooleanFunc n)
    (S T : Finset (Fin n)) (hS : DependsOnlyOn f S) (hT : DependsOnlyOn g T)
    (h_disjoint : Disjoint S T) :
    𝐄 (f * g) = 𝐄 f * 𝐄 g := by
  unfold expectation
  simp
  field_simp
  ring_nf
  admit

noncomputable
def degree (f : BooleanFunc n) : ℕ :=
  let f_hat := fourierTransform f
  let support_sets := Finset.univ.filter (fun S ↦ f_hat S ≠ 0)
  support_sets.sup Finset.card

lemma eq_const_of_degree_zero' (f : BooleanFunc n) (h : degree f = 0) :
  ∃ c, ∀ x, f x = c := by
  rw [walsh_fourier f]
  use 𝓕 f ∅
  rw [Finset.sum_eq_single ∅]
  . simp
  . intro S hS hne
    have h_coeff_zero : ∀ S : Finset (Fin n), S ≠ ∅ → 𝓕 f S = 0 := by
      intro S hne
      by_contra h_nz
      have mem : S ∈ Finset.univ.filter (fun S ↦ 𝓕 f S ≠ 0) := by simp [h_nz]
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

/-- if g depends on on its first n coords, we can restrict down to n with the same expectation. -/
lemma expectation_restrict {n : ℕ} (g : BooleanFunc (n + 1))
    (h : DependsOnlyOn g (Finset.univ.erase (Fin.last n))) :
    expectation g = expectation (restrict g) := by
  unfold expectation;
  have h_split : ∑ x : Fin (n + 1) → Fin 2, g x = ∑ x : Fin n → Fin 2, ∑ y : Fin 2, g (Fin.append x (fun _ => y)) := by
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => ( x ∘ Fin.castSucc, x ( Fin.last _ ) ) ) _ _ _ _ <;> simp +decide;
    · exact fun a₁ a₂ h₁ h₂ => funext fun i => by cases i using Fin.lastCases <;> simpa [ * ] using congr_fun h₁ ‹_›;
    · intro a
      constructor
      . use Fin.snoc a 0
        simp
      . use Fin.snoc a 1
        simp
    · intro a; congr; ext i; induction i using Fin.lastCases <;> simp [Fin.append] ;
      · simp [Fin.addCases];
      · simp [Fin.addCases];
  have h_eq : ∀ x : Fin n → Fin 2, ∀ y : Fin 2, g (Fin.append x (fun _ => y)) = g (Fin.append x (fun _ => 0)) := by
    intro x y; apply h; intro i hi; simp [Fin.append];
    cases i using Fin.lastCases <;> simp_all [Fin.addCases];
  simp_all [pow_succ];
  rw [← Finset.mul_sum]; ring!

set_option maxHeartbeats 400000
lemma fourier_restriction (g : BooleanFunc (n + 1)) (b : Finset (Fin n)) :
  𝓕 (restrict g) b =
    𝓕 g (b.map Fin.castSuccEmb) + 𝓕 g (insert (Fin.last n) (b.map Fin.castSuccEmb)) := by
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
    DependsOnlyOn (expectation_op i f) (Finset.univ.erase i) := by
  intro x y hxy
  unfold expectation_op
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
   (hd : d = (dderiv (Fin.last n)) f) (he : e = (expectation_op (Fin.last n)) f) :
    DependsOnlyOn (d^a * e^b) (Finset.univ.erase (Fin.last n)) := by
  apply DependsOnlyOn.mul
  · apply DependsOnlyOn.pow
    rw [hd]
    exact dependsOnlyOn_d f (Fin.last n)
  · apply DependsOnlyOn.pow
    rw [he]
    exact dependsOnlyOn_e f (Fin.last n)



lemma expectation_const_func (c : ℝ) :
  𝐄 ((fun _ ↦ c) : BooleanFunc n) = c := by
  simp [expectation]

lemma expectation_const_power (c : ℝ) (k : ℕ) :
  𝐄 ((fun _ ↦ c) ^ k : BooleanFunc n) = c ^ k := by
  simp [expectation]

lemma chi_pow_reduce (xₙ : BooleanFunc (n + 1))
    (hx : xₙ = fun x ↦ (-1) ^ (x (Fin.last n)).val) (k : ℕ) :
    xₙ ^ k = if k % 2 = 0 then 1 else xₙ := by
  ext x
  rw [hx]
  simp only [Pi.pow_apply]
  match kk : (x (Fin.last n)) with
  | 0 =>
    simp
    split_ifs
    . simp
    . simp [kk]
  | 1 =>
    split_ifs
    · simp; rename_i h; apply Even.neg_one_pow; exact Nat.even_iff.mpr h
    · have h_odd : ∃ m, k = 2 * m + 1 := by
        rename_i h; apply odd_iff_exists_bit1.mp; apply Nat.odd_iff.mpr; exact
          Nat.mod_two_ne_zero.mp h
      rcases h_odd with ⟨m, rfl⟩
      rw [pow_succ]
      simp
      rw [kk]
      simp


lemma restrict_pow_eq_pow_restrict {n : ℕ} (f : BooleanFunc (n + 1)) (p : ℕ) :
    restrict (f^p) = (restrict f)^p := by
  ext x
  simp [restrict, Pi.pow_apply]

lemma dderiv_const_eq_zero {n : ℕ} (c : ℝ) (i : Fin (n + 1)) :
    dderiv i (λ _ => c) = 0 := by
  ext x
  simp [dderiv]

lemma degree_restrict_le {n : ℕ} (g : BooleanFunc (n + 1)) :
    degree (restrict g) ≤ degree g := by
  unfold degree restrict; simp
  intro b h
  have h_support : ∃ S : Finset (Fin (n + 1)), S.card ≥ b.card ∧ (𝓕 g S) ≠ 0 := by
    have h_support : (𝓕 g (b.map Fin.castSuccEmb)) + (𝓕 g (insert (Fin.last n) (b.map Fin.castSuccEmb))) ≠ 0 := by
      convert h using 1;
      convert fourier_restriction g b |> Eq.symm using 1;
    contrapose! h_support; aesop;
  exact le_trans h_support.choose_spec.1 ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_support.choose_spec.2 ⟩))

lemma degree_dderiv_le {n : ℕ} (f : BooleanFunc (n + 1)) (i : Fin (n + 1)) :
    degree (dderiv i f) ≤ degree f - 1 := by
    unfold degree; simp; intro b h
    have hi : i ∉ b := by
      rw [fourier_dderiv_eq_fourier_insert] at h
      contrapose! h
      rw [if_neg]
      . exact not_not.mpr h
    have h_mem : (insert i b) ∈ (Finset.filter (fun S ↦ 𝓕 f S ≠ 0) Finset.univ) := by
      simp_all [fourier_dderiv_eq_fourier_insert]
    have h_le := Finset.le_sup (f := Finset.card) h_mem
    rw [Finset.card_insert_of_notMem hi] at h_le
    exact Nat.le_sub_of_add_le h_le

lemma degree_Ei_le (i : Fin n) (f : BooleanFunc n) :
  degree (expectation_op i f) ≤ degree f := by
  unfold degree
  simp
  intro b h_nonzero
  have hi : i ∉ b := by
    rw [fourier_expect_op] at h_nonzero
    contrapose! h_nonzero
    rw [if_neg]
    · exact not_not.mpr h_nonzero
  have h_eq_f : 𝓕 (expectation_op i f) b = 𝓕 f b := by
    simp_all [fourier_expect_op]
  have h_card_b : b ∈ Finset.univ.filter (fun S => (𝓕 f S) ≠ 0) := by
    grind;
  apply Finset.le_sup (f := Finset.card) h_card_b


lemma Cube_zero_eq_const (f : BooleanFunc 0) :
  ∃c, ∀ x, f x = c := by
  simp

lemma exp_pow_restrict {n : ℕ} (f : BooleanFunc (n + 1)) (p : ℕ) (h : IndependentOfLast f) :
  𝐄 (f^p) = 𝐄 ((restrict f)^p) := by
  rw [expectation_restrict (f^p) (DependsOnlyOn.pow p h), restrict_pow_eq_pow_restrict]

--set_option trace.Meta.synthInstance true
set_option profiler true
set_option maxHeartbeats 400000
lemma bonamis_lemma (f : BooleanFunc n) (k : ℕ) (h_def : degree f ≤ k) :
  𝐄 (f ^ 4) ≤ 9^k * (𝐄 (f ^ 2)) ^ 2 := by
  revert k f
  induction n with
  | zero =>
    intro f k hf; obtain ⟨c, h⟩ := Cube_zero_eq_const f
    have hf : f = (λ _ => c) := by funext x; exact h x
    simp_rw [hf, expectation_const_power]
    ring_nf
    nth_rewrite 1 [← mul_one (c ^ 4)]
    apply mul_le_mul_of_nonneg_left
    . exact one_le_pow₀ (a := 9) (by norm_num)
    . positivity
  | succ n' ih =>
    intro f k hk
    rw [pow_succ, pow_succ, pow_succ, pow_one, decomposition' (Fin.last (n')) f]
    set d := dderiv (Fin.last n') f with hd
    set e := expectation_op (Fin.last n') f with he
    set xₙ := fun x : Fin (n' + 1) → Fin 2 ↦ (-1 : ℝ) ^ (x (Fin.last n')).val with hχ

    change 𝐄 ((xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e)) ≤
       9 ^ k * 𝐄 ((xₙ * d + e) * (xₙ * d + e)) ^ 2
    have h_expand : (xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e) * (xₙ * d + e) =
                xₙ^4 * d^4 + (4:ℕ) * (xₙ^3 * (d^3 * e)) + (6:ℕ) * (xₙ^2 * (d^2 * e^2)) + (4:ℕ) * (xₙ * (d * e^3)) + e^4 := by
      ring
    have h_expand_2 : (xₙ * d + e) * (xₙ * d + e) = (xₙ ^ 2 * d ^ 2) + (2:ℕ) * (xₙ * (d * e)) + e ^ 2 := by
      ring
    rw [h_expand, h_expand_2]
    clear h_expand h_expand_2
    repeat rw [map_add]
    have h_const : ∀ (n : ℕ), (n : BooleanFunc (n' + 1)) = (fun _ ↦ (n : ℝ)) := by
      intro n; ext x; rfl

    have h_zero : 𝐄 xₙ = 0 := by
      have hz : 𝐄 (χ {Fin.last n'}) = 0 :=
        expectation_walsh_eq_zero (Finset.singleton_nonempty (Fin.last n'))
      unfold walshCharacter at hz
      simp only [Finset.prod_singleton, ← hχ] at hz
      exact hz

    have dep_d_n (s : ℕ) : DependsOnlyOn  (d ^ s) (Finset.univ.erase (Fin.last n')) := by
      rw [← mul_one (d ^ s)]; rw [← pow_zero e]; exact depends_de_prod s 0 hd he

    have dep_e_n (s : ℕ) : DependsOnlyOn (e ^ s) (Finset.univ.erase (Fin.last n')) := by
      rw [←one_mul (e ^ s)]; rw [← pow_zero d]; exact depends_de_prod 0 s hd he

    have dep_xₙ : DependsOnlyOn xₙ {Fin.last n'} := by
      unfold DependsOnlyOn; simp; unfold xₙ; intro x y; intro cond; rw [cond]

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

    simp_rw [h_const]
    simp_rw [expectation_mul_const_func]

    simp
    nth_rw 1 5 [← pow_one e]
    nth_rw 4 6 [← pow_one d]
    have disj : Disjoint {Fin.last n'} (Finset.univ.erase (Fin.last n')) := by
      simp

    simp_rw [chi_pow_reduce xₙ hχ]
    simp only [Nat.reduceMod, one_ne_zero, ↓reduceIte, one_mul]

    rw [expectation_mul_of_independent (xₙ) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (dep_xₙ) ((depends_de_prod 3 1 hd he)) disj]
    rw [expectation_mul_of_independent (xₙ) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (dep_xₙ) (depends_de_prod 1 1 hd he) disj]
    rw [expectation_mul_of_independent (xₙ) _ {Fin.last n'} (Finset.univ.erase (Fin.last n')) (dep_xₙ) (depends_de_prod 1 3 hd he) disj]

    simp_rw [h_zero]; simp

    rw [expectation_restrict (d^4) (dep_d_n 4)]
    rw [restrict_pow_eq_pow_restrict]
    have ihd := ih (restrict d)
    repeat rw [← restrict_pow_eq_pow_restrict] at ihd
    rw [← expectation_restrict (d^4) (dep_d_n 4)] at ihd
    rw [← expectation_restrict (d^2) (dep_d_n 2)] at ihd

    have h_deg : degree (restrict d) ≤ k - 1 := by
      apply le_trans (degree_restrict_le d)
      have h_red : degree d ≤ degree f - 1 := by
        rw [hd]
        apply degree_dderiv_le
      apply le_trans h_red
      exact Nat.sub_le_sub_right hk 1
    have hbd := ihd (k := k - 1) h_deg

    rw [← restrict_pow_eq_pow_restrict]
    rw [← expectation_restrict (d^4) (dep_d_n 4)]


    have cs : 𝐄 (d^2 * e^2) ≤ (𝐄 (d^4))^(1/2 : ℝ) * (𝐄 (e^4))^(1/2 : ℝ) := by
      rw [inner_eq_expectation.symm]
      calc ⟪d^2, e^2⟫
        _ ≤ ‖d^2‖ * ‖e^2‖ := real_inner_le_norm _ _
        _ = (𝐄 (d^4))^(1/2 : ℝ) * (𝐄 (e^4))^(1/2 : ℝ) := by
          simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℝ)]
          simp [inner_eq_expectation, Real.sqrt_eq_rpow]
          simp_rw [← pow_add]

    rw [exp_pow_restrict e 4]
    rotate_left
    . unfold IndependentOfLast; unfold DependsOnlyOn; intro x y h; rw [← pow_one e]; exact dep_e_n 1 x y h

    have ihe := ih (restrict e)
    repeat rw [← restrict_pow_eq_pow_restrict] at ihe
    rw [← expectation_restrict (e^4) (dep_e_n 4)] at ihe
    rw [← expectation_restrict (e^2) (dep_e_n 2)] at ihe
    have e_deg : degree (restrict (e)) ≤ k := by
      apply le_trans (degree_restrict_le e) (le_trans (degree_Ei_le (Fin.last n') f) hk)
    have hbe := ihe k e_deg
    rw [← exp_pow_restrict e 4]
    rotate_left
    . simp [IndependentOfLast]; rw [he]; exact dependsOnlyOn_e f (Fin.last n')
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
      letI : CommRing (BooleanFunc n) := inferInstance
      letI : Algebra ℝ (BooleanFunc n) := inferInstance
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
            ring
        _ ≤ 9^(k' + 1) * 𝐄 (d^2)^2 + 2 * 9^(k'+1) * 𝐄 (d^2) * 𝐄 (e^2) + 9^(k'+1) * 𝐄 (e^2)^2 := by
            field_simp;
            ring_nf
            nlinarith [sq_nonneg (𝐄 (d ^ 2)), pow_nonneg (show (0:ℝ) ≤ 9 from by norm_num) k']
        _ ≤ 9^(k' + 1) * (𝐄 (d^2) + 𝐄 (e^2))^2 := by
            ring_nf; rfl



--- lemma hypercontractive_ineq_2_4 (f : BooleanFunc n) :
---   let p := 2; let q := 4; let ρ := (1/√3);
---   let T := noise_operator ρ;
---   𝐄 ((T f)^4) ≤ 𝐄 (f ^ 2) ^ 2 := by
---   sorry
