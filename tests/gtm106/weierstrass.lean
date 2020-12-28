import algebra.field
import algebra.char_zero
import algebra.char_p
import data.int.basic
import data.rat.basic
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.gtm106.weierstrass_equation.models_by_characteristic
import tests.gtm106.weierstrass_equation.j_invariant
import tests.testchar
import tests.testperfect
import tactic

noncomputable theory

lemma alg_closed_implies_pow_surj (K : Type*) [field K] [is_alg_closed K] (n : ℕ) (hn : n ≠ 0)
: nth_power_surjective K n :=
begin
  intro x,
  let f : polynomial K := polynomial.X^n - (polynomial.C x),
  have hdeg : f.degree = n := polynomial.degree_X_pow_sub_C (nat.pos_of_ne_zero hn) x,
  replace hdeg : f.degree ≠ 0 := by {
    rw hdeg, norm_cast, exact hn,
  },
  have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
  replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
  cases hsplit with y hy,
  use y,
  simp at hy,
  calc y ^ n = x + (y ^ n - x) : by ring
  ... = x : by { rw hy, ring, },
end

lemma weierstrass_equation.same_j_implies_isomorphic' {K : Type*} [field K] [is_alg_closed K]
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
: E.is_isomorphic' E' :=
begin
  by_cases hchar2 : ring_char K = 2, {
    sorry,
  },
  by_cases hchar3 : ring_char K = 3, {
    sorry,
  },
  sorry,
  /-
  rcases E.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C, hmod ⟩,
  rcases E'.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C', hmod' ⟩,
  rw C.preserve_non_singular' E at hns,
  rw C'.preserve_non_singular' E' at hns',
  unfold weierstrass_equation.non_singular' at hns hns',
  rw [← C.j E, ← C'.j E'] at h,
  set E1 := C.change_curve E,
  set E1' := C'.change_curve E',
  rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
  rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
  clear_value E1 E1', clear C C' E E',
  unfold weierstrass_equation.j at h,
  field_simp [hns, hns'] at h,
  rw [E1.c4_of_model_of_char_neq_2_and_3 hmod,
  E1.disc_of_model_of_char_neq_2_and_3 hmod,
  E1'.c4_of_model_of_char_neq_2_and_3 hmod',
  E1'.disc_of_model_of_char_neq_2_and_3 hmod'] at h,
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
    field_simp [zero_pow, h16, h27] at hns,
    field_simp [zero_pow, hns] at h,
    rw h at hns',
    field_simp [zero_pow, h16, h27] at hns',
    cases alg_closed_implies_pow_surj K 6 (by norm_num) (E1.a6/E1'.a6) with u hu,
    let C := linear_change_of_variable.mk u 0 0 0 (by {
      intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact hns hu.symm,
    }),
    use C,
    rw weierstrass_equation.ext_iff,
    unfold linear_change_of_variable.change_curve
    linear_change_of_variable.u
    linear_change_of_variable.r
    linear_change_of_variable.s
    linear_change_of_variable.t
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, ha4, h, hu],
    field_simp [zero_pow, hns], ring,
  },
  by_cases ha6 : E1.a6 = 0, {
    rw ha6 at h hns,
    field_simp [zero_pow, ha4] at h,
    rw h at hns',
    field_simp [zero_pow, h4, h16] at hns',
    cases alg_closed_implies_pow_surj K 4 (by norm_num) (E1.a4/E1'.a4) with u hu,
    let C := linear_change_of_variable.mk u 0 0 0 (by {
      intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact ha4 hu.symm,
    }),
    use C,
    rw weierstrass_equation.ext_iff,
    unfold linear_change_of_variable.change_curve
    linear_change_of_variable.u
    linear_change_of_variable.r
    linear_change_of_variable.s
    linear_change_of_variable.t
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, ha6, h, hu],
    field_simp [zero_pow, ha4], ring,
  },
  by_cases ha4' : E1'.a4 = 0, {
    exfalso,
    rw ha4' at h,
    field_simp [zero_pow, ha4] at h,
    rw [ha4', h] at hns',
    field_simp [zero_pow] at hns',
    exact hns',
  },
  by_cases ha6' : E1'.a6 = 0, {
    exfalso,
    rw ha6' at h,
    field_simp [zero_pow, ha4', ha6] at h,
    exact h,
  },
  cases alg_closed_implies_pow_surj K 2 (by norm_num) ((E1.a6 / E1'.a6) / (E1.a4 / E1'.a4)) with u hu,
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
  rw weierstrass_equation.ext_iff,
  unfold linear_change_of_variable.change_curve
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6,
  rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu4, hu6],
  field_simp [zero_pow, ha4, ha6], split; ring,
  -/
end
