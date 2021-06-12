import myhelper.char
import myhelper.perfect
import myhelper.mypoly.basic
import tactic

noncomputable theory

namespace monic_quad_poly

lemma disc_zero_implies_has_multiple_root
{K : Type*} [field K] (f : monic_quad_poly K) (hperfect : ring_char K = 2 → my_perfect_field K):
f.disc = 0 → f.has_multiple_root :=
begin
  unfold disc,
  intro hdisc,
  by_cases hchar2 : ring_char K = 2, {
    replace hperfect : nth_power_surjective K 2 := by {
      have h := hperfect hchar2,
      simp [my_perfect_field, hchar2] at h,
      exact h,
    },
    ring_char2 at hdisc,
    cases hperfect (-f.b) with x hx,
    use x,
    simp [is_multiple_root, eval_at,
      eval_dx_at, hdisc, hx],
    ring_char2,
  },
  replace hdisc := sub_eq_zero.1 hdisc,
  replace hchar2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2,
  norm_cast at hchar2,
  use (-f.a/2),
  simp only [is_multiple_root, eval_at, eval_dx_at],
  split, {
    field_simp [pow_succ, hchar2],
    transitivity -2*f.a^2 + 8*f.b,
    { norm_num, ring, },
    rw hdisc, ring,
  },
  field_simp [hchar2],
  ring,
end

end monic_quad_poly

namespace monic_cubic_poly

lemma eval_dx_at_char3 {K : Type*} [comm_ring K] (hchar3 : ring_char K = 3)
(f : monic_cubic_poly K) (x : K)
: f.eval_dx_at x = 2*f.a*x + f.b :=
sub_eq_zero.1 begin
  unfold eval_dx_at,
  ring_char3,
end

lemma disc_char3 {K : Type*} [comm_ring K] (hchar3 : ring_char K = 3)
(f : monic_cubic_poly K)
: f.disc = -f.a^3*f.c + f.a^2*f.b^2 - f.b^3 :=
sub_eq_zero.1 begin
  unfold disc,
  ring_char3,
end

lemma eval_at_mul_cube_of_a_char3 {K : Type*} [comm_ring K] (hchar3 : ring_char K = 3)
(f : monic_cubic_poly K) (x : K)
: f.eval_at x * f.a^3 = f.eval_dx_at x *
(-x^2*f.a^2 - x*(f.a^2+f.b)*f.a + (f.a^2*f.b-f.b^2)) - f.disc :=
sub_eq_zero.1 begin
  unfold disc eval_at eval_dx_at,
  ring_char3,
end

lemma disc_zero_implies_has_multiple_root
{K : Type*} [field K] (f : monic_cubic_poly K)
(hperfect : ring_char K = 2 ∨ (ring_char K = 3 ∧ f.a = 0) → my_perfect_field K):
f.disc = 0 → f.has_multiple_root :=
begin
  intro hdisc,
  by_cases hchar3 : ring_char K = 3, {
    have hdisc' := disc_char3 hchar3 f,
    by_cases ha : f.a = 0, {
      replace hperfect : nth_power_surjective K 3 := by {
        have h := hperfect (by { right, exact ⟨ hchar3, ha ⟩, }),
        unfold my_perfect_field at h,
        rw hchar3 at h,
        cases h with h h, { contradiction, },
        exact h,
      },
      simp [hdisc', ha, zero_pow] at hdisc,
      cases hperfect (-f.c) with x hx,
      use x,
      simp [is_multiple_root, eval_at,
        eval_dx_at, hx, ha, hdisc],
      ring_char3,
    },
    let x := f.b/f.a,
    have hx' : f.eval_dx_at x = 0 := by {
      rw [eval_dx_at_char3 hchar3 f],
      field_simp [ha],
      ring_char3,
    },
    have hdiv1 := eval_at_mul_cube_of_a_char3 hchar3 f x,
    simp [hx', hdisc, ha] at hdiv1,
    exact ⟨ x, hdiv1, hx' ⟩,
  },
  have h3 := prime_neq_char_is_non_zero K 3 (by norm_num) hchar3, norm_cast at h3,
  have h9 := power_of_prime_neq_char_is_non_zero K 9 3 2 (by norm_num) (by norm_num) hchar3, norm_cast at h9,
  have h27 := power_of_prime_neq_char_is_non_zero K 27 3 3 (by norm_num) (by norm_num) hchar3, norm_cast at h27,
  set! a' : K := -f.a^2*2/9 + 2*f.b/3 with ha', clear_value a',
  set! b' : K := -f.a*f.b/9 + f.c with hb', clear_value b',
  have hdiv1 : ∀ x : K, f.eval_at x = f.eval_dx_at x * (x/3 + f.a/9) + (a' * x + b') := by {
    intro x,
    unfold eval_at
    eval_dx_at,
    rw [ha', hb'],
    field_simp [h3, h9],
    ring,
  },
  by_cases hchar2 : ring_char K = 2, {
    unfold disc at hdisc,
    replace hperfect : nth_power_surjective K 2 := by {
      have h := hperfect (by { left, exact hchar2, }),
      unfold my_perfect_field at h,
      rw hchar2 at h,
      cases h with h h, { contradiction, },
      exact h,
    },
    replace hb' : b' = f.c - f.a*f.b := by {
      rw hb',
      ring_char2,
    },
    ring_char2 at ha',
    ring_char2 at hdisc,
    replace hb' := calc (b')^2 = f.a^2*f.b^2 - 2*f.a*f.b*f.c + 2*f.c^2 - f.c^2 : by { rw hb', ring, }
    ... = f.a^2*f.b^2 - f.c^2 : by { ring_char2, }
    ... = 0 : hdisc,
    simp at hb',
    cases hperfect f.b with x hx,
    have hx' : f.eval_dx_at x = 0 := by {
      unfold eval_dx_at,
      rw hx,
      ring_char2,
    },
    replace hdiv1 := hdiv1 x,
    rw [hx', ha', hb'] at hdiv1,
    simp at hdiv1,
    exact ⟨ x, hdiv1, hx' ⟩,
  },
  by_cases ha'zero : a' = 0, {
    have h2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2, norm_cast at h2,
    have hb := calc f.b = 2*f.b/3*(3/2) : by { field_simp [h2, h3], ring, }
    ... = (-f.a^2*2/9 + 2*f.b/3 + f.a^2*2/9)*(3/2) : by { congr, field_simp [h3, h9], ring, }
    ... = f.a^2/3 : by { rw [← ha', ha'zero], field_simp [h2, h3, h9], ring, },
    have hdisc' : f.disc = -27*(b')^2 := by {
      unfold disc,
      rw [hb', hb],
      field_simp [h3, h9],
      ring,
    },
    replace hb' : b' = 0 := by {
      rw hdisc at hdisc',
      simp [h27] at hdisc',
      exact hdisc',
    },
    let x := -f.a/3,
    have hx' : f.eval_dx_at x = 0 := by {
      unfold eval_dx_at,
      rw hb,
      field_simp [h3],
      ring,
    },
    replace hdiv1 := hdiv1 x,
    rw [hx', ha'zero, hb'] at hdiv1,
    simp at hdiv1,
    exact ⟨ x, hdiv1, hx' ⟩,
  },
  let x := -b'/a',
  have haxb : a' * x + b' = 0 := by {
    field_simp [ha'zero],
    ring,
  },
  have hx' : f.eval_dx_at x = 0 := by {
    unfold eval_dx_at,
    field_simp [ha'zero],
    transitivity (3 * b' ^ 2 + -(2 * f.a * b' * a') + f.b * a' ^ 2) * a',
    { simp [add_mul], ring, },
    simp [ha'zero],
    rw [ha', hb'],
    field_simp [h3, h9],
    transitivity -1594323*f.disc,
    { unfold disc, ring, },
    rw hdisc, ring,
  },
  replace hdiv1 := hdiv1 x,
  rw [haxb, hx'] at hdiv1,
  simp at hdiv1,
  exact ⟨ x, hdiv1, hx' ⟩,
end

end monic_cubic_poly
