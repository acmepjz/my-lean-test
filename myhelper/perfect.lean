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

def nth_power_surjective (K : Type*) [field K] (n : ℕ) :=
∀ x : K, ∃ y : K, y ^ n = x

def my_perfect_field (K : Type*) [field K] :=
ring_char K = 0 ∨ nth_power_surjective K (ring_char K)

-- ad-hoc definitions for quadratic and cubic polynomials

@[ext]
structure monic_quad_poly (K : Type*) [field K] :=
mk :: (a b : K)

def monic_quad_poly.eval_at {K : Type*} [field K] (f : monic_quad_poly K) (x : K) : K
:= x^2 + f.a*x + f.b

def monic_quad_poly.eval_dx_at {K : Type*} [field K] (f : monic_quad_poly K) (x : K) : K
:= 2*x + f.a

def monic_quad_poly.is_root {K : Type*} [field K] (f : monic_quad_poly K) (x : K)
:= f.eval_at x = 0

def monic_quad_poly.is_multiple_root {K : Type*} [field K] (f : monic_quad_poly K) (x : K)
:= f.eval_at x = 0 ∧ f.eval_dx_at x = 0

def monic_quad_poly.has_multiple_root {K : Type*} [field K] (f : monic_quad_poly K)
:= ∃ x : K, f.is_multiple_root x

def monic_quad_poly.disc {K : Type*} [field K] (f : monic_quad_poly K) : K
:= f.a^2 - 4*f.b

lemma monic_quad_poly.disc_zero_implies_has_multiple_root
{K : Type*} [field K] (f : monic_quad_poly K) (hperfect : ring_char K = 2 → my_perfect_field K):
f.disc = 0 → f.has_multiple_root :=
begin
  unfold monic_quad_poly.disc,
  intro hdisc,
  by_cases hchar2 : ring_char K = 2, {
    replace hperfect : nth_power_surjective K 2 := by {
      have h := hperfect hchar2,
      unfold my_perfect_field at h,
      rw hchar2 at h,
      cases h with h h, { contradiction, },
      exact h,
    },
    have h := dvd_char_is_zero hchar2 4 (by norm_num), norm_cast at h, rw h at hdisc, clear h,
    field_simp at hdisc,
    cases hperfect (-f.b) with x hx,
    use x,
    unfold monic_quad_poly.is_multiple_root
    monic_quad_poly.eval_at
    monic_quad_poly.eval_dx_at,
    rw [hdisc, hx],
    have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h, clear h,
    simp,
  },
  replace hdisc := calc f.a^2 = (f.a^2 - 4*f.b) + 4*f.b : by ring
  ... = 4*f.b : by { rw hdisc, ring, },
  replace hchar2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2,
  norm_cast at hchar2,
  use (-f.a/2),
  unfold monic_quad_poly.is_multiple_root
  monic_quad_poly.eval_at
  monic_quad_poly.eval_dx_at,
  split, {
    field_simp [pow_succ, hchar2],
    ring,
    calc f.a * f.a * 2 - f.a * f.a * (2 * 2) + f.b * (2 * 2 * 2)
    = -2*f.a^2 + 8*f.b : by ring
    ... = 0 : by { rw hdisc, ring, },
  },
  field_simp [hchar2],
  ring,
end

@[ext]
structure monic_cubic_poly (K : Type*) [field K] :=
mk :: (a b c : K)

def monic_cubic_poly.eval_at {K : Type*} [field K] (f : monic_cubic_poly K) (x : K) : K
:= x^3 + f.a*x^2 + f.b*x + f.c

def monic_cubic_poly.eval_dx_at {K : Type*} [field K] (f : monic_cubic_poly K) (x : K) : K
:= 3*x^2 + 2*f.a*x + f.b

def monic_cubic_poly.is_root {K : Type*} [field K] (f : monic_cubic_poly K) (x : K)
:= f.eval_at x = 0

def monic_cubic_poly.is_multiple_root {K : Type*} [field K] (f : monic_cubic_poly K) (x : K)
:= f.eval_at x = 0 ∧ f.eval_dx_at x = 0

def monic_cubic_poly.has_multiple_root {K : Type*} [field K] (f : monic_cubic_poly K)
:= ∃ x : K, f.is_multiple_root x

def monic_cubic_poly.disc {K : Type*} [field K] (f : monic_cubic_poly K) : K
:= -4*f.a^3*f.c + f.a^2*f.b^2 - 4*f.b^3 - 27*f.c^2 + 18*f.a*f.b*f.c

lemma monic_cubic_poly.disc_zero_implies_has_multiple_root
{K : Type*} [field K] (f : monic_cubic_poly K)
(hperfect : ring_char K = 2 ∨ (ring_char K = 3 ∧ f.a = 0) → my_perfect_field K):
f.disc = 0 → f.has_multiple_root :=
begin
  intro hdisc,
  by_cases hchar3 : ring_char K = 3, {
    have hdisc' : f.disc = 8*f.a^3*f.c - 2*f.a^2*f.b^2 - f.b^3 := by {
      unfold monic_cubic_poly.disc,
      have h := dvd_char_is_zero hchar3 27 (by norm_num), norm_cast at h, rw h, clear h,
      have h := dvd_char_is_zero hchar3 18 (by norm_num), norm_cast at h, rw h, clear h,
      have hh2 := cong_char_is_eq hchar3 2 (-1) (by norm_num), norm_cast at hh2,
      have hh4 := cong_char_is_eq hchar3 4 1 (by norm_num), norm_cast at hh4,
      have hh8 := cong_char_is_eq hchar3 8 (-4) (by norm_num), norm_cast at hh8,
      conv in (2 * f.a ^ 2 * f.b ^ 2) { rw hh2, },
      conv in (4 * f.b ^ 3) { rw hh4, },
      conv in (8 * f.a ^ 3 * f.c) { rw hh8, },
      simp, ring,
    },
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
      unfold monic_cubic_poly.is_multiple_root
      monic_cubic_poly.eval_at
      monic_cubic_poly.eval_dx_at,
      rw [hx, ha, hdisc],
      have h := dvd_char_is_zero hchar3 3 (by norm_num), norm_cast at h, rw h, clear h,
      split; ring,
    },
    have hx' : ∀ x : K, f.eval_dx_at x = 2*f.a*x + f.b := by {
      intro x,
      unfold monic_cubic_poly.eval_dx_at,
      have h := dvd_char_is_zero hchar3 3 (by norm_num), norm_cast at h, rw h, clear h,
      ring,
    },
    have hdiv1 : ∀ x : K, f.eval_at x = f.eval_dx_at x *
    (x^2/f.a/2 + x*(2*f.a^2-f.b)/f.a^2/2^2 + (2*f.a^2*f.b+f.b^2)/f.a^3/2^3) + f.disc/f.a^3/2^3 := by {
      intro x,
      unfold monic_cubic_poly.eval_at,
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
    rw [hx', hdisc] at hdiv1,
    simp at hdiv1,
    exact ⟨ x, hdiv1, hx' ⟩,
  },
  have h3 := prime_neq_char_is_non_zero K 3 (by norm_num) hchar3, norm_cast at h3,
  have h9 := power_of_prime_neq_char_is_non_zero K 9 3 2 (by norm_num) (by norm_num) hchar3, norm_cast at h9,
  have h27 := power_of_prime_neq_char_is_non_zero K 27 3 3 (by norm_num) (by norm_num) hchar3, norm_cast at h27,
  set! a' : K := -f.a^2*2/9 + 2*f.b/3 with ha', clear_value a',
  set! b' : K := -f.a*f.b/9 + f.c with hb', clear_value b',
  have hdiv1 : ∀ x : K, f.eval_at x = f.eval_dx_at x * (x/3 + f.a/9) + (a' * x + b') := by {
    intro x,
    unfold monic_cubic_poly.eval_at
    monic_cubic_poly.eval_dx_at,
    rw [ha', hb'],
    field_simp [h3, h9],
    ring,
  },
  by_cases hchar2 : ring_char K = 2, {
    unfold monic_cubic_poly.disc at hdisc,
    replace hperfect : nth_power_surjective K 2 := by {
      have h := hperfect (by { left, exact hchar2, }),
      unfold my_perfect_field at h,
      rw hchar2 at h,
      cases h with h h, { contradiction, },
      exact h,
    },
    replace hb' : b' = f.c - f.a*f.b := by {
      rw hb',
      have h := cong_char_is_eq hchar2 9 1 (by norm_num), norm_cast at h, rw h, clear h,
      ring,
    },
    have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h at ha', clear h,
    simp at ha',
    have h := dvd_char_is_zero hchar2 18 (by norm_num), norm_cast at h, rw h at hdisc, clear h,
    have h := dvd_char_is_zero hchar2 4 (by norm_num), norm_cast at h, rw h at hdisc, clear h,
    have h := cong_char_is_eq hchar2 27 1 (by norm_num), norm_cast at h, rw h at hdisc, clear h,
    simp at hdisc,
    replace hb' := calc (b')^2 = f.a^2*f.b^2 - 2*f.a*f.b*f.c + 2*f.c^2 - f.c^2 : by { rw hb', ring, }
    ... = f.a^2*f.b^2 - f.c^2 : by {
      have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h, clear h,
      ring,
    }
    ... = 0 : hdisc,
    field_simp at hb',
    cases hperfect f.b with x hx,
    have hx' : f.eval_dx_at x = 0 := by {
      unfold monic_cubic_poly.eval_dx_at,
      rw hx,
      have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h, clear h,
      have h := cong_char_is_eq hchar2 3 (-1) (by norm_num), norm_cast at h, rw h, clear h,
      simp,
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
      unfold monic_cubic_poly.disc,
      rw [hb', hb],
      field_simp [h3, h9],
      ring,
    },
    replace hb' : b' = 0 := by {
      rw hdisc at hdisc',
      field_simp [h27] at hdisc',
      exact hdisc',
    },
    let x := -f.a/3,
    have hx' : f.eval_dx_at x = 0 := by {
      unfold monic_cubic_poly.eval_dx_at,
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
    unfold monic_cubic_poly.eval_dx_at,
    field_simp [ha'zero],
    rw (calc 3 * b' ^ 2 * a' + -(2 * f.a * b' * a' ^ 2) + f.b * (a' ^ 2 * a')
    = (3 * b' ^ 2 + -(2 * f.a * b' * a') + f.b * a' ^ 2) * a' : by ring),
    field_simp [ha'zero],
    rw [ha', hb'],
    field_simp [h3, h9],
    calc (3 * (-(f.a * f.b) + f.c * 9) ^ 2 * (9 * 3 * 9) + -(2 * f.a * (-(f.a * f.b) + f.c * 9) * (-(f.a ^ 2 * 2 * 3) + 2 * f.b * 9) * 9 ^ 2)) * (9 * 3) ^ 2 + f.b * (-(f.a ^ 2 * 2 * 3) + 2 * f.b * 9) ^ 2 * (9 ^ 2 * (9 * 3 * 9))
    = -1594323*f.disc : by { unfold monic_cubic_poly.disc, ring, }
    ... = 0 : by { rw hdisc, ring, },
  },
  replace hdiv1 := hdiv1 x,
  rw [haxb, hx'] at hdiv1,
  simp at hdiv1,
  exact ⟨ x, hdiv1, hx' ⟩,
end