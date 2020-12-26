import data.nat.basic
import data.nat.prime
import data.rat.basic
import algebra.field
import algebra.char_zero
import algebra.char_p
import field_theory.perfect_closure
import tests.testchar
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
:= -4*f.a^3*f.c + f.a^2*f.b^2 - 4*f.b^3 - 27*f.c^2 +18*f.a*f.b*f.c

lemma monic_cubic_poly.disc_zero_implies_has_multiple_root
{K : Type*} [field K] (f : monic_cubic_poly K) (hperfect : ring_char K = 2 ∨ ring_char K = 3 → my_perfect_field K):
f.disc = 0 → f.has_multiple_root :=
begin
  sorry,
end
