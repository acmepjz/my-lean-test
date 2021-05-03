-- import data.nat.prime
import algebra.field
import algebra.char_zero
import algebra.char_p
import gtm106.naive_plane
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.linear_change_of_variable
import gtm106.weierstrass_equation.models_by_characteristic
import myhelper.char
import myhelper.perfect
import myhelper.separable_closed
import tactic

namespace weierstrass_equation

/--
For any `j ∈ K` there exists a Weierstrass equation over `K`
which has non-zero discriminant and whose j-invariant equals `j`.
-/
lemma exists_j {K : Type*} [field K]
(j_ : K) : ∃ E : weierstrass_equation K,
E.non_singular' ∧ E.j = j_ :=
begin
  let E0 : weierstrass_equation K := ⟨ 0, 0, 1, 0, 0 ⟩,
  have hc4_0 : E0.c4 = 0 := by {
    simp [c4, b2, b4],
  },
  have hdisc_0 : E0.disc = -27 := by {
    simp [disc, b2, b4, b6, b8],
  },
  have hj_0 : E0.j = 0 := by {
    simp [j, hc4_0, hdisc_0],
  },
  let E1728 : weierstrass_equation K := ⟨ 0, 0, 0, 1, 0 ⟩,
  have hc4_1728 : E1728.c4 = -48 := by {
    simp [c4, b2, b4], norm_num,
  },
  have hdisc_1728 : E1728.disc = -64 := by {
    simp [disc, b2, b4, b6, b8], norm_num,
  },
  have hj_1728 : E1728.j = 1728 := by {
    simp [j, hc4_1728, hdisc_1728],
    by_cases hchar2 : ring_char K = 2, {
      ring_char2,
    },
    have h64 := power_of_prime_neq_char_is_non_zero K 64 2 6 (by norm_num) (by norm_num) hchar2,
    norm_num at h64,
    field_simp [h64], norm_num,
  },
  by_cases h0 : j_ = 0, {
    rw h0,
    by_cases hchar3 : ring_char K = 3, {
      use E1728,
      split, {
        simp [non_singular', hdisc_1728],
        ring_char3,
      },
      rw hj_1728,
      ring_char3,
    },
    use E0,
    split, {
      simp [non_singular', hdisc_0],
      have h27 := power_of_prime_neq_char_is_non_zero K 27 3 3 (by norm_num) (by norm_num) hchar3,
      norm_num at h27,
    },
    exact hj_0,
  },
  by_cases h1728 : j_ = 1728, {
    rw h1728,
    by_cases hchar2 : ring_char K = 2, {
      exfalso,
      ring_char2 at h1728,
      exact h0 h1728,
    },
    use E1728,
    split, {
      simp [non_singular', hdisc_1728],
      have h64 := power_of_prime_neq_char_is_non_zero K 64 2 6 (by norm_num) (by norm_num) hchar2,
      norm_num at h64,
    },
    exact hj_1728,
  },
  replace h1728 := sub_ne_zero.2 h1728,
  let E : weierstrass_equation K := ⟨ j_-1728, 0, 0, -36*(j_-1728)^3, -(j_-1728)^5 ⟩,
  have hc4 : E.c4 = j_ * (j_-1728)^3 := by {
    simp [c4, b2, b4],
    ring,
  },
  have hdisc : E.disc = j_^2 * (j_-1728)^9 := by {
    simp [disc, b2, b4, b6, b8],
    ring,
  },
  have hns : E.disc ≠ 0 := by {
    simp [hdisc, h0, h1728],
  },
  have hj : E.j = j_ := by {
    unfold j,
    field_simp [hns],
    rw [hc4, hdisc],
    ring,
  },
  exact ⟨ E, hns, hj ⟩,
end

lemma same_j_implies_isom'.char_2.solve_s_for_j_non_zero {K : Type*} [field K] (hsc : my_sep_closed K)
(E1 E1' : weierstrass_equation K)
(hchar2 : ring_char K = 2)
: ∃ s : K, s^2 + s + (E1.a2 + E1'.a2) = 0 :=
begin
  let f : polynomial K := polynomial.X^2 + polynomial.X + (polynomial.C (E1.a2 + E1'.a2)),
  have hdeg : f.degree ≠ 0 := by {
    let f1 : polynomial K := polynomial.X^2,
    let f2 : polynomial K := polynomial.X,
    let f3 : polynomial K := polynomial.C (E1.a2 + E1'.a2),
    have h1 : f1.degree = 2 := polynomial.degree_X_pow _,
    have h2 : f2.degree ≤ 1 := polynomial.degree_X_le,
    have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
    have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
    ... ≤ max 1 0 : max_le_max h2 h3
    ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
    calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw ← add_assoc, }
    ... ≠ 0 : by {
      rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
    },
  },
  let f' : polynomial K := 1,
  have hf' : f' = f.derivative := by {
    have : f = (polynomial.C (1 : K)) * polynomial.X^2 + (polynomial.C (1 : K)) * polynomial.X^1 + (polynomial.C (E1.a2 + E1'.a2)) := by simp,
    rw this,
    repeat { rw polynomial.derivative_add },
    repeat { rw polynomial.derivative_C_mul_X_pow },
    rw polynomial.derivative_C,
    have : ((2 : ℕ) : K) = ((2 : ℤ) : K) := by { norm_cast, },
    rw this,
    have h := dvd_char_is_zero hchar2 2 (by norm_num), rw h, clear h,
    simp,
  },
  have hcop : is_coprime f f.derivative := by {
    rw ← hf',
    use [-1, f+1],
    rw [add_mul, mul_one, mul_one, ← add_assoc],
    ring,
  },
  cases hsc f hcop hdeg with s hs,
  simp at hs,
  exact ⟨ s, hs ⟩,
end

lemma same_j_implies_isom'.char_2.solve_s_for_j_zero {K : Type*} [field K] (hsc : my_sep_closed K)
(u : K)
(E1 E1' : weierstrass_equation K)
(hchar2 : ring_char K = 2)
(hns : E1.a3 ≠ 0)
: ∃ s : K, s^4 + E1.a3*s + (E1.a4 - u^4*E1'.a4) = 0 :=
begin
  let f : polynomial K := polynomial.X^4 + (polynomial.C E1.a3) * polynomial.X + (polynomial.C (E1.a4 - u^4*E1'.a4)),
  have hdeg : f.degree ≠ 0 := by {
    let f1 : polynomial K := polynomial.X^4,
    set! f2 : polynomial K := (polynomial.C E1.a3) * polynomial.X^1 with hf2, rw pow_one at hf2,
    let f3 : polynomial K := polynomial.C (E1.a4 - u^4*E1'.a4),
    have h1 : f1.degree = 4 := polynomial.degree_X_pow _,
    have h2 : f2.degree ≤ 1 := polynomial.degree_C_mul_X_pow_le _ _,
    have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
    have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
    ... ≤ max 1 0 : max_le_max h2 h3
    ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
    calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw [← add_assoc, hf2], }
    ... ≠ 0 : by {
      rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
    },
  },
  let f' : polynomial K := polynomial.C E1.a3,
  have hf' : f' = f.derivative := by {
    have : f = (polynomial.C (1 : K)) *  polynomial.X^4 + (polynomial.C E1.a3) * polynomial.X^1 + (polynomial.C (E1.a4 - u^4*E1'.a4)) := by simp,
    rw this,
    repeat { rw polynomial.derivative_add },
    repeat { rw polynomial.derivative_C_mul_X_pow },
    rw polynomial.derivative_C,
    have : ((4 : ℕ) : K) = ((4 : ℤ) : K) := by { norm_cast, },
    rw this,
    have h := dvd_char_is_zero hchar2 4 (by norm_num), rw h, clear h,
    simp,
  },
  have hcop : is_coprime f f.derivative := by {
    rw ← hf',
    let a : polynomial K := -f',
    let b : polynomial K := f + polynomial.C (1/E1.a3),
    use [a, b],
    calc a * f + b * f'
    = (-f') * f + (f + polynomial.C (1/E1.a3)) * f' : rfl
    ... = polynomial.C (1/E1.a3) * f' : by ring
    ... = 1 : by {
      rw ← polynomial.C_mul,
      field_simp [hns],
    },
  },
  cases hsc f hcop hdeg with s hs,
  repeat {rw polynomial.eval₂_add at hs},
  rw [polynomial.eval₂_mul, polynomial.eval₂_X_pow, polynomial.eval₂_X] at hs,
  repeat {rw polynomial.eval₂_C at hs},
  simp at hs,
  exact ⟨ s, hs ⟩,
end

lemma same_j_implies_isom'.char_2.solve_t_for_j_zero {K : Type*} [field K] (hsc : my_sep_closed K)
(u s : K)
(E1 E1' : weierstrass_equation K)
(hchar2 : ring_char K = 2)
(hns : E1.a3 ≠ 0)
: ∃ t : K, t^2 + E1.a3*t + (s^6 + E1.a4*s^2 + E1.a6 - u^6*E1'.a6) = 0 :=
begin
  let f : polynomial K := polynomial.X^2 + (polynomial.C E1.a3) * polynomial.X + (polynomial.C (s^6 + E1.a4*s^2 + E1.a6 - u^6*E1'.a6)),
  have hdeg : f.degree ≠ 0 := by {
    let f1 : polynomial K := polynomial.X^2,
    set! f2 : polynomial K := (polynomial.C E1.a3) * polynomial.X^1 with hf2, rw pow_one at hf2,
    let f3 : polynomial K := polynomial.C (s^6 + E1.a4*s^2 + E1.a6 - u^6*E1'.a6),
    have h1 : f1.degree = 2 := polynomial.degree_X_pow _,
    have h2 : f2.degree ≤ 1 := polynomial.degree_C_mul_X_pow_le _ _,
    have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
    have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
    ... ≤ max 1 0 : max_le_max h2 h3
    ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
    calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw [← add_assoc, hf2], }
    ... ≠ 0 : by {
      rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
    },
  },
  let f' : polynomial K := polynomial.C E1.a3,
  have hf' : f' = f.derivative := by {
    have : f = (polynomial.C (1 : K)) *  polynomial.X^2 + (polynomial.C E1.a3) * polynomial.X^1 + (polynomial.C (s^6 + E1.a4*s^2 + E1.a6 - u^6*E1'.a6)) := by simp,
    rw this,
    repeat { rw polynomial.derivative_add },
    repeat { rw polynomial.derivative_C_mul_X_pow },
    rw polynomial.derivative_C,
    have : ((2 : ℕ) : K) = ((2 : ℤ) : K) := by { norm_cast, },
    rw this,
    have h := dvd_char_is_zero hchar2 2 (by norm_num), rw h, clear h,
    simp,
  },
  have hcop : is_coprime f f.derivative := by {
    rw ← hf',
    let a : polynomial K := -f',
    let b : polynomial K := f + polynomial.C (1/E1.a3),
    use [a, b],
    calc a * f + b * f'
    = (-f') * f + (f + polynomial.C (1/E1.a3)) * f' : rfl
    ... = polynomial.C (1/E1.a3) * f' : by ring
    ... = 1 : by {
      rw ← polynomial.C_mul,
      field_simp [hns],
    },
  },
  cases hsc f hcop hdeg with t ht,
  repeat {rw polynomial.eval₂_add at ht},
  rw [polynomial.eval₂_mul, polynomial.eval₂_X_pow, polynomial.eval₂_X] at ht,
  repeat {rw polynomial.eval₂_C at ht},
  simp at ht,
  exact ⟨ t, ht ⟩,
end

lemma same_j_implies_isom'.char_2.j_non_zero {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (hmod : E.is_model_of_char_2_j_non_zero) (hmod' : E'.is_model_of_char_2_j_non_zero)
(h : E.a6 = E'.a6) (hj : E.a6 ≠ 0) (hj' : E'.a6 ≠ 0)
(hchar2 : ring_char K = 2)
: E.is_isom' E' :=
begin
  cases same_j_implies_isom'.char_2.solve_s_for_j_non_zero hsc E E' hchar2 with s hs,
  let C : linear_change_of_variable K := ⟨ 1, 0, s, 0, by simp ⟩,
  use C,
  simp [ext_iff, linear_change_of_variable.change_curve,
    hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, h],
  ring_char2,
  transitivity E.a2 - s - s ^ 2  + (s ^ 2 + s + (E.a2 + E'.a2)),
  { rw hs, ring, },
  rw ← sub_eq_zero,
  ring_char2,
end

lemma same_j_implies_isom'.char_2.j_zero {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (hmod : E.is_model_of_char_2_j_zero) (hmod' : E'.is_model_of_char_2_j_zero)
(hns : E.a3 ≠ 0) (hns' : E'.a3 ≠ 0)
(hchar2 : ring_char K = 2)
: E.is_isom' E' :=
begin
  cases sep_closed_implies_pow_surj K hsc 3 (by { rw hchar2, norm_num, }) (E.a3 / E'.a3) with u hu,
  cases same_j_implies_isom'.char_2.solve_s_for_j_zero hsc u E E' hchar2 hns with s hs,
  cases same_j_implies_isom'.char_2.solve_t_for_j_zero hsc u s E E' hchar2 hns with t ht,
  let C := linear_change_of_variable.mk u (s^2) s t (by {
    intro h, field_simp [h, hns'] at hu, exact hns hu.symm,
  }),
  use C,
  simp [ext_iff, linear_change_of_variable.change_curve,
    hmod.1, hmod.2, hmod'.1, hmod'.2, hu],
  ring_char2,
  split, { field_simp [hns, hns', mul_comm], },
  split, {
    field_simp [C.hu],
    transitivity E.a4 - s * E.a3 + s ^ 4 - (s ^ 4 + E.a3 * s + (E.a4 - u ^ 4 * E'.a4)),
    { rw hs, ring, },
    rw ← sub_eq_zero,
    ring_char2,
  },
  field_simp [C.hu],
  transitivity E.a6 + s ^ 2 * E.a4 + s ^ 6 - t * E.a3 - t ^ 2 - (t ^ 2 + E.a3 * t + (s ^ 6 + E.a4 * s ^ 2 + E.a6 - u ^ 6 * E'.a6)),
  { rw ht, ring, },
  rw ← sub_eq_zero,
  ring_char2,
end

lemma same_j_implies_isom'.char_2 {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
(hchar2 : ring_char K = 2)
: E.is_isom' E' :=
begin
  change E ≈ E',
  refine quotient.exact _,
  have hj0 : E.j = isom_class'.j ⟦E⟧ := by { simp [isom_class'.j], },
  have hj'0 : E'.j = isom_class'.j ⟦E'⟧ := by { simp [isom_class'.j], },
  rw [hj0, hj'0] at h,
  replace hns : isom_class'.non_singular' ⟦E⟧ := by { simp [isom_class'.non_singular', hns], },
  replace hns' : isom_class'.non_singular' ⟦E'⟧ := by { simp [isom_class'.non_singular', hns'], },
  rcases E.have_model_of_char_2 hchar2 with ⟨ hj, C, hmod ⟩ | ⟨ hj, C, hmod ⟩, {
    replace hj := hj hns,
    rcases E'.have_model_of_char_2 hchar2 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      replace hj' := hj' hns',
      rw hj0 at hj,
      rw hj'0 at hj',
      set E1 := C.change_curve E with hE1, clear_value E1,
      set E1' := C'.change_curve E' with hE1', clear_value E1',
      replace hE1 : ⟦E⟧ = ⟦E1⟧ := quotient.sound (by { use C, exact hE1.symm, }),
      replace hE1' : ⟦E'⟧ = ⟦E1'⟧ := quotient.sound (by { use C', exact hE1'.symm, }),
      rw hE1 at *,
      rw hE1' at *,
      clear hE1 hE1' hj0 hj'0 C C' E E',
      refine quotient.sound _,
      simp [isom_class'.j, hmod, hmod', hchar2] at h hj hj',
      exact same_j_implies_isom'.char_2.j_non_zero hsc hmod hmod' h hj hj' hchar2,
    }, {
      exfalso, finish,
    },
  }, {
    rcases E'.have_model_of_char_2 hchar2 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      exfalso, finish,
    }, {
      rw hj0 at hj,
      rw hj'0 at hj',
      set E1 := C.change_curve E with hE1, clear_value E1,
      set E1' := C'.change_curve E' with hE1', clear_value E1',
      replace hE1 : ⟦E⟧ = ⟦E1⟧ := quotient.sound (by { use C, exact hE1.symm, }),
      replace hE1' : ⟦E'⟧ = ⟦E1'⟧ := quotient.sound (by { use C', exact hE1'.symm, }),
      rw hE1 at *,
      rw hE1' at *,
      clear hE1 hE1' hj0 hj'0 C C' E E',
      refine quotient.sound _,
      simp [isom_class'.non_singular', non_singular', hmod, hmod', hchar2] at hns hns',
      exact same_j_implies_isom'.char_2.j_zero hsc hmod hmod' hns hns' hchar2,
    },
  },
end

lemma same_j_implies_isom'.char_3.solve_r_for_j_zero {K : Type*} [field K] (hsc : my_sep_closed K)
(u : K)
(E1 E1' : weierstrass_equation K)
(hchar3 : ring_char K = 3)
(hns : E1.a4 ≠ 0)
: ∃ r : K, r^3 + E1.a4*r + (E1.a6 - u^6*E1'.a6) = 0 :=
begin
  let f : polynomial K := polynomial.X^3 + (polynomial.C E1.a4) * polynomial.X + (polynomial.C (E1.a6 - u^6*E1'.a6)),
  have hdeg : f.degree ≠ 0 := by {
    let f1 : polynomial K := polynomial.X^3,
    set! f2 : polynomial K := (polynomial.C E1.a4) * polynomial.X^1 with hf2, rw pow_one at hf2,
    let f3 : polynomial K := polynomial.C (E1.a6 - u^6*E1'.a6),
    have h1 : f1.degree = 3 := polynomial.degree_X_pow _,
    have h2 : f2.degree ≤ 1 := polynomial.degree_C_mul_X_pow_le _ _,
    have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
    have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
    ... ≤ max 1 0 : max_le_max h2 h3
    ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
    calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw [← add_assoc, hf2], }
    ... ≠ 0 : by {
      rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
    },
  },
  let f' : polynomial K := polynomial.C E1.a4,
  have hf' : f' = f.derivative := by {
    have : f = (polynomial.C (1 : K)) * polynomial.X^3 + (polynomial.C E1.a4) * polynomial.X^1 + (polynomial.C (E1.a6 - u^6*E1'.a6)) := by simp,
    rw this,
    repeat { rw polynomial.derivative_add },
    repeat { rw polynomial.derivative_C_mul_X_pow },
    rw polynomial.derivative_C,
    have : ((3 : ℕ) : K) = ((3 : ℤ) : K) := by { norm_cast, },
    rw this,
    have h := dvd_char_is_zero hchar3 3 (by norm_num), rw h, clear h,
    simp,
  },
  have hcop : is_coprime f f.derivative := by {
    rw ← hf',
    let a : polynomial K := -f',
    let b : polynomial K := f + polynomial.C (1/E1.a4),
    use [a, b],
    calc a * f + b * f'
    = (-f') * f + (f + polynomial.C (1/E1.a4)) * f' : rfl
    ... = polynomial.C (1/E1.a4) * f' : by ring
    ... = 1 : by {
      rw ← polynomial.C_mul,
      field_simp [hns],
    },
  },
  cases hsc f hcop hdeg with r hr,
  repeat {rw polynomial.eval₂_add at hr},
  rw [polynomial.eval₂_mul, polynomial.eval₂_X_pow, polynomial.eval₂_X] at hr,
  repeat {rw polynomial.eval₂_C at hr},
  simp at hr,
  exact ⟨ r, hr ⟩,
end

lemma same_j_implies_isom'.char_3.j_non_zero {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (hmod : E.is_model_of_char_3_j_non_zero) (hmod' : E'.is_model_of_char_3_j_non_zero)
(h : E.j = E'.j) (hj : E.j ≠ 0) (hj' : E'.j ≠ 0)
(hchar3 : ring_char K = 3)
: E.is_isom' E' :=
begin
  simp [hmod, hmod', hchar3] at h hj hj',
  push_neg at hj hj',
  cases sep_closed_implies_pow_surj K hsc 2 (by { rw hchar3, norm_num, }) (E.a2 / E'.a2) with u hu,
  let C := linear_change_of_variable.mk u 0 0 0 (by {
    intro h, field_simp [h, hj'.1] at hu, exact hj.1 hu.symm,
  }),
  use C,
  simp [ext_iff, linear_change_of_variable.change_curve,
    hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu],
  split,
  { field_simp [hj.1, hj'.1, mul_comm], },
  transitivity E.a6 / (u ^ 2) ^ 3,
  { congr' 1, ring, },
  rw hu,
  field_simp [hj.1, hj.2, hj'.1, hj'.2] at h ⊢,
  rw [mul_comm E.a6, mul_comm E'.a6, h],
end

lemma same_j_implies_isom'.char_3.j_zero {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (hmod : E.is_model_of_char_neq_2_and_3) (hmod' : E'.is_model_of_char_neq_2_and_3)
(hns : E.a4 ≠ 0) (hns' : E'.a4 ≠ 0)
(hchar3 : ring_char K = 3)
: E.is_isom' E' :=
begin
  cases sep_closed_implies_pow_surj K hsc 4 (by { rw hchar3, norm_num, }) (E.a4 / E'.a4) with u hu,
  cases same_j_implies_isom'.char_3.solve_r_for_j_zero hsc u E E' hchar3 hns with r hr,
  let C := linear_change_of_variable.mk u r 0 0 (by {
    intro h, field_simp [h, hns'] at hu, exact hns hu.symm,
  }),
  use C,
  simp [ext_iff, linear_change_of_variable.change_curve,
    hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu],
  ring_char3,
  split, { field_simp [hns, hns', mul_comm], },
  field_simp [C.hu],
  transitivity E.a6 + r * E.a4 + r ^ 3 - (r ^ 3 + E.a4 * r + (E.a6 - u ^ 6 * E'.a6)),
  { rw hr, ring, },
  rw ← sub_eq_zero,
  ring,
end

lemma same_j_implies_isom'.char_3 {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
(hchar3 : ring_char K = 3)
: E.is_isom' E' :=
begin
  change E ≈ E',
  refine quotient.exact _,
  have hj0 : E.j = isom_class'.j ⟦E⟧ := by { simp [isom_class'.j], },
  have hj'0 : E'.j = isom_class'.j ⟦E'⟧ := by { simp [isom_class'.j], },
  rw [hj0, hj'0] at h,
  replace hns : isom_class'.non_singular' ⟦E⟧ := by { simp [isom_class'.non_singular', hns], },
  replace hns' : isom_class'.non_singular' ⟦E'⟧ := by { simp [isom_class'.non_singular', hns'], },
  rcases E.have_model_of_char_3 hchar3 with ⟨ hj, C, hmod ⟩ | ⟨ hj, C, hmod ⟩, {
    replace hj := hj hns,
    rcases E'.have_model_of_char_3 hchar3 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      replace hj' := hj' hns',
      rw hj0 at hj,
      rw hj'0 at hj',
      set E1 := C.change_curve E with hE1, clear_value E1,
      set E1' := C'.change_curve E' with hE1', clear_value E1',
      replace hE1 : ⟦E⟧ = ⟦E1⟧ := quotient.sound (by { use C, exact hE1.symm, }),
      replace hE1' : ⟦E'⟧ = ⟦E1'⟧ := quotient.sound (by { use C', exact hE1'.symm, }),
      rw hE1 at *,
      rw hE1' at *,
      clear hE1 hE1' hj0 hj'0 C C' E E',
      refine quotient.sound _,
      simp [isom_class'.j] at h hj hj',
      exact same_j_implies_isom'.char_3.j_non_zero hsc hmod hmod' h hj hj' hchar3,
    }, {
      exfalso, finish,
    },
  }, {
    rcases E'.have_model_of_char_3 hchar3 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      exfalso, finish,
    }, {
      rw hj0 at hj,
      rw hj'0 at hj',
      set E1 := C.change_curve E with hE1, clear_value E1,
      set E1' := C'.change_curve E' with hE1', clear_value E1',
      replace hE1 : ⟦E⟧ = ⟦E1⟧ := quotient.sound (by { use C, exact hE1.symm, }),
      replace hE1' : ⟦E'⟧ = ⟦E1'⟧ := quotient.sound (by { use C', exact hE1'.symm, }),
      rw hE1 at *,
      rw hE1' at *,
      clear hE1 hE1' hj0 hj'0 C C' E E',
      refine quotient.sound _,
      simp [isom_class'.non_singular', non_singular', hmod, hmod', hchar3] at hns hns',
      exact same_j_implies_isom'.char_3.j_zero hsc hmod hmod' hns hns' hchar3,
    },
  },
end


/--
Non-singular Weierstrass equations with same j-invariant are isomorphic
over a separable closed field.
-/
lemma same_j_implies_isom' {K : Type*} [field K] (hsc : my_sep_closed K)
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
: E.is_isom' E' :=
begin
  by_cases hchar2 : ring_char K = 2, {
    exact same_j_implies_isom'.char_2 hsc h hns hns' hchar2,
  },
  by_cases hchar3 : ring_char K = 3, {
    exact same_j_implies_isom'.char_3 hsc h hns hns' hchar3,
  },
  have hcharndvd2 : ¬ ring_char K ∣ 2 := by {
    cases char_is_prime_or_zero' K with hh hh, {
      rw nat.prime_dvd_prime_iff_eq hh nat.prime_two, exact hchar2,
    },
    rw hh, norm_num,
  },
  have hcharndvd3 : ¬ ring_char K ∣ 3 := by {
    cases char_is_prime_or_zero' K with hh hh, {
      rw nat.prime_dvd_prime_iff_eq hh nat.prime_three, exact hchar3,
    },
    rw hh, norm_num,
  },
  have hcharndvd4 : ¬ ring_char K ∣ 4 := by {
    cases char_is_prime_or_zero' K with hh hh, {
      rw (calc 4 = 2*2 : by norm_num),
      exact nat.prime.not_dvd_mul hh hcharndvd2 hcharndvd2,
    },
    rw hh, norm_num,
  },
  have hcharndvd6 : ¬ ring_char K ∣ 6 := by {
    cases char_is_prime_or_zero' K with hh hh, {
      rw (calc 6 = 2*3 : by norm_num),
      exact nat.prime.not_dvd_mul hh hcharndvd2 hcharndvd3,
    },
    rw hh, norm_num,
  },
  change E ≈ E',
  refine quotient.exact _,
  replace h : isom_class'.j ⟦E⟧ = isom_class'.j ⟦E'⟧ := by { simp [isom_class'.j, h], },
  replace hns : isom_class'.non_singular' ⟦E⟧ := by { simp [isom_class'.non_singular', hns], },
  replace hns' : isom_class'.non_singular' ⟦E'⟧ := by { simp [isom_class'.non_singular', hns'], },
  rcases E.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C, hmod ⟩,
  rcases E'.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C', hmod' ⟩,
  set E1 := C.change_curve E with hE1, clear_value E1,
  set E1' := C'.change_curve E' with hE1', clear_value E1',
  replace hE1 : ⟦E⟧ = ⟦E1⟧ := quotient.sound (by { use C, exact hE1.symm, }),
  replace hE1' : ⟦E'⟧ = ⟦E1'⟧ := quotient.sound (by { use C', exact hE1'.symm, }),
  rw hE1 at *,
  rw hE1' at *,
  clear hE1 hE1' C C' E E',
  refine quotient.sound _,
  simp [isom_class'.non_singular', non_singular'] at hns hns',
  field_simp [isom_class'.j, j, hns, hns'] at h,
  simp [hmod, hmod'] at h,
  ring_exp at h,
  replace h := calc E1.a4 ^ 3 * E1'.a6 ^ 2 * 16^4 * 27^2
  = (E1.a4 ^ 3 * (E1'.a4 ^ 3 * 7077888) + E1.a4 ^ 3 * (E1'.a6 ^ 2 * 47775744)) - E1.a4 ^ 3 * (E1'.a4 ^ 3 * 7077888) : by ring
  ... = E1'.a4 ^ 3 * E1.a6 ^ 2 * 16^4 * 27^2 : by { rw h, ring, },
  have h4 := power_of_prime_neq_char_is_non_zero K 4 2 2 (by norm_num) (by norm_num) hchar2, norm_num at h4,
  have h16 := power_of_prime_neq_char_is_non_zero K 16 2 4 (by norm_num) (by norm_num) hchar2, norm_num at h16,
  have h27 := power_of_prime_neq_char_is_non_zero K 27 3 3 (by norm_num) (by norm_num) hchar3, norm_num at h27,
  field_simp [h16, h27] at h,
  rw E1.disc_of_model_of_char_neq_2_and_3 hmod at hns,
  rw E1'.disc_of_model_of_char_neq_2_and_3 hmod' at hns',
  by_cases ha4 : E1.a4 = 0, {
    rw ha4 at h hns,
    simp [zero_pow, h16, h27] at hns,
    simp [zero_pow, hns] at h,
    simp [h, zero_pow, h16, h27] at hns',
    cases sep_closed_implies_pow_surj K hsc 6 hcharndvd6 (E1.a6/E1'.a6) with u hu,
    let C := linear_change_of_variable.mk u 0 0 0 (by {
      intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact hns hu.symm,
    }),
    use C,
    simp [ext_iff, linear_change_of_variable.change_curve,
      hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, ha4, h, hu],
    field_simp [zero_pow, hns], ring,
  },
  by_cases ha6 : E1.a6 = 0, {
    rw ha6 at h hns,
    simp [zero_pow, ha4] at h,
    simp [h, zero_pow, h4, h16] at hns',
    cases sep_closed_implies_pow_surj K hsc 4 hcharndvd4 (E1.a4/E1'.a4) with u hu,
    let C := linear_change_of_variable.mk u 0 0 0 (by {
      intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact ha4 hu.symm,
    }),
    use C,
    simp [ext_iff, linear_change_of_variable.change_curve,
      hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, ha6, h, hu],
    field_simp [zero_pow, ha4], ring,
  },
  by_cases ha4' : E1'.a4 = 0, {
    exfalso,
    simp [ha4', zero_pow, ha4] at h,
    simp [ha4', h, zero_pow] at hns',
    exact hns',
  },
  by_cases ha6' : E1'.a6 = 0, {
    exfalso,
    simp [ha6', zero_pow, ha4', ha6] at h,
    exact h,
  },
  cases sep_closed_implies_pow_surj K hsc 2 hcharndvd2 ((E1.a6 / E1'.a6) / (E1.a4 / E1'.a4)) with u hu,
  have hu4 := calc u ^ 4 = (u ^ 2) ^ 2 : by ring
  ... = E1.a4 / E1'.a4 : by {
    rw hu,
    field_simp [zero_pow, ha4, ha6, ha4', ha6'],
    ring_exp,
    rw mul_comm (E1.a6 ^ 2) _,
    exact h.symm,
  },
  have hu6 := calc u ^ 6 = (u ^ 2) ^ 3 : by ring
  ... = E1.a6 / E1'.a6 : by {
    rw hu,
    field_simp [zero_pow, ha4, ha6, ha4', ha6'],
    calc (E1.a6 * E1'.a4) ^ 3 * E1'.a6
    = (E1'.a4 ^ 3 * E1.a6 ^ 2) * E1.a6 * E1'.a6 : by ring
    ... = (E1.a4 ^ 3 * E1'.a6 ^ 2) * E1.a6 * E1'.a6 : by rw h
    ... = E1.a6 * (E1'.a6 * E1.a4) ^ 3 : by ring,
  },
  let C := linear_change_of_variable.mk u 0 0 0 (by {
    intro h, rw h at hu, field_simp [zero_pow, ha4, ha6, ha4', ha6'] at hu, exact hu,
  }),
  use C,
  simp [ext_iff, linear_change_of_variable.change_curve,
    hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu4, hu6],
  field_simp [zero_pow, ha4, ha6], split; ring,
end

end weierstrass_equation
