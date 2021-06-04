import data.nat.basic
import data.nat.prime
import data.rat.basic
import algebra.field
import algebra.char_zero
import algebra.char_p
import field_theory.perfect_closure
import myhelper.char
import tactic

noncomputable theory

def nth_power_surjective (K : Type*) [comm_ring K] (n : ℕ) :=
∀ x : K, ∃ y : K, y ^ n = x

def my_perfect_field (K : Type*) [comm_ring K] :=
ring_char K = 0 ∨ nth_power_surjective K (ring_char K)

-- ad-hoc definitions for quadratic and cubic polynomials

@[ext]
structure monic_quad_poly (K : Type*) [comm_ring K] :=
mk :: (a b : K)

namespace monic_quad_poly

def eval_at {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K) : K
:= x^2 + f.a*x + f.b

def eval_dx_at {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K) : K
:= 2*x + f.a

def is_root {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
:= f.eval_at x = 0

def is_multiple_root {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
:= f.eval_at x = 0 ∧ f.eval_dx_at x = 0

def has_multiple_root {K : Type*} [comm_ring K] (f : monic_quad_poly K)
:= ∃ x : K, f.is_multiple_root x

def disc {K : Type*} [comm_ring K] (f : monic_quad_poly K) : K
:= f.a^2 - 4*f.b

lemma disc' {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
: f.disc = (f.eval_dx_at x) ^ 2 - 4 * f.eval_at x :=
begin
  simp only [eval_at, eval_dx_at, disc],
  ring,
end

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

lemma has_multiple_root_implies_disc_zero
{K : Type*} [comm_ring K] (f : monic_quad_poly K):
f.has_multiple_root → f.disc = 0 :=
begin
  simp only [has_multiple_root, is_multiple_root],
  rintro ⟨ x, h1, h2 ⟩,
  rw [disc' f x, h1, h2],
  ring,
end

end monic_quad_poly

@[ext]
structure monic_cubic_poly (K : Type*) [comm_ring K] :=
mk :: (a b c : K)

namespace monic_cubic_poly

def eval_at {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K) : K
:= x^3 + f.a*x^2 + f.b*x + f.c

def eval_dx_at {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K) : K
:= 3*x^2 + 2*f.a*x + f.b

def is_root {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K)
:= f.eval_at x = 0

def is_multiple_root {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K)
:= f.eval_at x = 0 ∧ f.eval_dx_at x = 0

def has_multiple_root {K : Type*} [comm_ring K] (f : monic_cubic_poly K)
:= ∃ x : K, f.is_multiple_root x

def disc {K : Type*} [comm_ring K] (f : monic_cubic_poly K) : K
:= -4*f.a^3*f.c + f.a^2*f.b^2 - 4*f.b^3 - 27*f.c^2 + 18*f.a*f.b*f.c

lemma disc' {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K)
: f.disc = f.eval_at x * (-3*(2*f.a^2 - 6*f.b)*x + (-4*f.a^3 + 15*f.a*f.b - 27*f.c))
+ f.eval_dx_at x * ((2*f.a^2 - 6*f.b)*x^2 + (2*f.a^3 - 7*f.a*f.b + 9*f.c)*x + (f.a^2*f.b - 4*f.b^2 + 3*f.a*f.c)) :=
begin
  simp only [eval_at, eval_dx_at, disc],
  ring,
end

lemma disc_char3 {K : Type*} [comm_ring K] (f : monic_cubic_poly K)
(hchar3 : ring_char K = 3)
: f.disc = 8*f.a^3*f.c - 2*f.a^2*f.b^2 - f.b^3 :=
sub_eq_zero.1 begin
  unfold disc,
  ring_char3,
end

lemma disc_zero_implies_has_multiple_root
{K : Type*} [field K] (f : monic_cubic_poly K)
(hperfect : ring_char K = 2 ∨ (ring_char K = 3 ∧ f.a = 0) → my_perfect_field K):
f.disc = 0 → f.has_multiple_root :=
begin
  intro hdisc,
  by_cases hchar3 : ring_char K = 3, {
    have hdisc' := disc_char3 f hchar3,
    have hchar2 : ring_char K ≠ 2 := by { rw hchar3, norm_num, },
    have h2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2, norm_cast at h2,
    have h4 := power_of_prime_neq_char_is_non_zero K 4 2 2 (by norm_num) (by norm_num) hchar2, norm_cast at h4,
    by_cases ha : f.a = 0, {
      replace hperfect : nth_power_surjective K 3 := by {
        have h := hperfect (by { right, exact ⟨ hchar3, ha ⟩, }),
        unfold my_perfect_field at h,
        rw hchar3 at h,
        cases h with h h, { contradiction, },
        exact h,
      },
      rw [hdisc', ha] at hdisc,
      field_simp [zero_pow, h4] at hdisc,
      cases hperfect (-f.c) with x hx,
      use x,
      simp [is_multiple_root, eval_at,
        eval_dx_at, hx, ha, hdisc],
      ring_char3,
    },
    have hx' : ∀ x : K, f.eval_dx_at x = 2*f.a*x + f.b := by {
      intro x,
      unfold eval_dx_at,
      ring_char3,
    },
    have hdiv1 : ∀ x : K, f.eval_at x = f.eval_dx_at x *
    (x^2/f.a/2 + x*(2*f.a^2-f.b)/f.a^2/2^2 + (2*f.a^2*f.b+f.b^2)/f.a^3/2^3) + f.disc/f.a^3/2^3 := by {
      intro x,
      unfold eval_at,
      rw [hx', hdisc'],
      field_simp [h2, ha],
      ring,
    },
    let x := -f.b/f.a/2,
    replace hx' : f.eval_dx_at x = 0 := by {
      rw hx' x,
      field_simp [h2, ha],
      ring,
    },
    replace hdiv1 := hdiv1 x,
    simp [hx', hdisc] at hdiv1,
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

lemma has_multiple_root_implies_disc_zero
{K : Type*} [comm_ring K] (f : monic_cubic_poly K):
f.has_multiple_root → f.disc = 0 :=
begin
  simp only [has_multiple_root, is_multiple_root],
  rintro ⟨ x, h1, h2 ⟩,
  rw [disc' f x, h1, h2],
  ring,
end

end monic_cubic_poly
