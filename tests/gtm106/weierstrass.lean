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
    -- TODO: take u = (E1.a4/E1'.a4)^(1/6)
    sorry,
  },
  sorry,
end

lemma alg_closed_implies_pow_surj (K : Type*) [field K] [is_alg_closed K] (n : ℕ) (hn : n ≠ 0)
: nth_power_surjective K n :=
begin
  intro x,
  sorry,
end
