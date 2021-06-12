import algebra.field
import tactic

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

lemma vieta_key_b {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
(h : f.is_root x)
: f.b = x*(-f.a-x) :=
sub_eq_zero.1 begin
  unfold is_root at h,
  transitivity f.b - x*(-f.a-x) - f.eval_at x, {
    rw h, ring,
  },
  unfold eval_at,
  ring,
end

lemma vieta_key {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
(h : f.is_root x) (z : K)
: f.eval_at z = (z - x) * (z + f.a + x) :=
sub_eq_zero.1 begin
  unfold eval_at,
  rw vieta_key_b f x h,
  ring,
end

lemma vieta {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
(h : f.is_root x) : f.is_root (-f.a-x) :=
begin
  unfold is_root,
  rw vieta_key f x h,
  ring,
end

lemma vieta_iff {K : Type*} [integral_domain K] (f : monic_quad_poly K) (x : K)
(h : f.is_root x) (z : K)
: f.is_root z ↔ z = x ∨ z = -f.a-x :=
begin
  unfold is_root,
  rw vieta_key f x h z,
  split, {
    intro h1,
    simp at h1,
    cases h1 with h1 h1, {
      left, exact sub_eq_zero.1 h1,
    },
    right,
    transitivity z - (z + f.a + x), {
      rw h1, ring,
    },
    rw ← sub_eq_zero, ring,
  },
  intro h1,
  cases h1 with h1 h1,
  { rw h1, ring, },
  rw h1, ring,
end

lemma vieta_2_iff {K : Type*} [integral_domain K] (f : monic_quad_poly K) (x : K)
(h : f.is_multiple_root x) (z : K)
: f.is_root z ↔ z = x :=
begin
  unfold is_multiple_root at h,
  cases h with h1 h2,
  replace h2 : x = -f.a-x := by {
    transitivity x - f.eval_dx_at x, {
      rw h2, ring,
    },
    unfold eval_dx_at,
    ring,
  },
  have key := vieta_iff f x h1 z,
  rw [← h2, or_self] at key,
  exact key,
end

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

lemma disc_eq_prod_of_roots {K : Type*} [comm_ring K] (f : monic_quad_poly K) (x : K)
(h : f.is_root x)
: f.disc = (f.a + 2*x)^2 :=
sub_eq_zero.1 begin
  unfold disc,
  rw [vieta_key_b f x h],
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

lemma is_multiple_root'
{K : Type*} [comm_ring K] (f : monic_quad_poly K)
(x : K) (h : f.is_root x)
: x = -f.a-x ↔ f.is_multiple_root x :=
begin
  unfold is_root at h,
  unfold is_multiple_root,
  transitivity f.eval_dx_at x = 0, {
    split, {
      intro h1,
      unfold eval_dx_at,
      transitivity x - (-f.a-x),
      { rw ← sub_eq_zero, ring, },
      rw ← h1, ring,
    },
    intro h1,
    transitivity x - f.eval_dx_at x,
    { rw h1, ring, },
    unfold eval_dx_at, ring,
  },
  simp [h],
end

lemma has_multiple_root_iff_disc_zero'
{K : Type*} [integral_domain K] (f : monic_quad_poly K)
(x : K) (h : f.is_root x)
: x = -f.a-x ↔ f.disc = 0 :=
begin
  unfold is_root at h,
  rw is_multiple_root' f x h,
  split, {
    intro h1,
    exact f.has_multiple_root_implies_disc_zero ⟨ x, h1 ⟩,
  },
  intro h1,
  rw [disc' f x, h] at h1,
  simp at h1,
  exact ⟨ h, h1 ⟩,
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

lemma eval_at_sub {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x y : K)
: f.eval_at x - f.eval_at y = (x^2+x*y+y^2 + f.a*(x+y) + f.b) * (x - y) :=
begin
  unfold eval_at,
  ring,
end

lemma eval_at_sub_2 {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x y : K)
: y * f.eval_at x - x * f.eval_at y = (x*y*(f.a+x+y) - f.c) * (x - y) :=
begin
  unfold eval_at,
  ring,
end

lemma vieta_key_b {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: f.b = -x^2-x*y-y^2 - f.a*(x+y) :=
begin
  unfold is_root at hx hy,
  have key := eval_at_sub f x y,
  simp [hx, hy, sub_ne_zero.2 hneq] at key,
  transitivity f.b - (x^2+x*y+y^2 + f.a*(x+y) + f.b),
  { rw key, ring, },
  rw ← sub_eq_zero, ring,
end

lemma vieta_key_c {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: f.c = x*y*(f.a+x+y) :=
begin
  unfold is_root at hx hy,
  have key := eval_at_sub_2 f x y,
  simp [hx, hy, sub_ne_zero.2 hneq] at key,
  exact (sub_eq_zero.1 key).symm,
end

lemma vieta_key {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
(z : K)
: f.eval_at z = (z - x) * (z - y) * (z + f.a + x + y) :=
begin
  unfold eval_at,
  rw [vieta_key_b f x y hx hy hneq, vieta_key_c f x y hx hy hneq],
  ring,
end

lemma vieta {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: f.is_root (-f.a-x-y) :=
begin
  unfold is_root,
  rw vieta_key f x y hx hy hneq,
  ring,
end

lemma vieta_2_key {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K)
(h : f.is_multiple_root x) (z : K)
: f.eval_at z = (z - x)^2 * (z + f.a + 2*x) :=
sub_eq_zero.1 begin
  transitivity f.eval_at x + f.eval_dx_at x * (z-x), {
    rw ← sub_eq_zero, unfold eval_at eval_dx_at, ring,
  },
  rw [h.1, h.2],
  ring,
end

lemma vieta_2 {K : Type*} [comm_ring K] (f : monic_cubic_poly K) (x : K)
(h : f.is_multiple_root x)
: f.is_root (-f.a-2*x) :=
begin
  unfold is_root,
  rw vieta_2_key f x h,
  ring,
end

lemma vieta_iff {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
(z : K)
: f.is_root z ↔ z = x ∨ z = y ∨ z = -f.a-x-y :=
begin
  unfold is_root,
  rw vieta_key f x y hx hy hneq,
  split, {
    intro h1,
    simp at h1,
    rcases h1 with ⟨ h1 | h1 ⟩ | h1, {
      left, exact sub_eq_zero.1 h1,
    }, {
      right, left, exact sub_eq_zero.1 h1,
    },
    right, right,
    transitivity z - (z + f.a + x + y), {
      rw h1, ring,
    },
    rw ← sub_eq_zero, ring,
  },
  intro h1,
  rcases h1 with h1 | h1 | h1,
  { rw h1, ring, },
  { rw h1, ring, },
  rw h1, ring,
end

lemma vieta_2_iff {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x : K)
(h : f.is_multiple_root x)
(z : K)
: f.is_root z ↔ z = x ∨ z = -f.a-2*x :=
begin
  unfold is_root,
  rw vieta_2_key f x h,
  split, {
    intro h1,
    simp at h1,
    cases h1 with h1 h1, {
      left, exact sub_eq_zero.1 h1,
    },
    right,
    transitivity z - (z + f.a + 2*x), {
      rw h1, ring,
    },
    rw ← sub_eq_zero, ring,
  },
  intro h1,
  cases h1 with h1 h1,
  { rw h1, ring, },
  rw h1, ring,
end

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

lemma disc_eq_prod_of_roots {K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: f.disc = (x - y)^2 * (f.a + 2*x + y)^2 * (f.a + x + 2*y)^2 :=
sub_eq_zero.1 begin
  unfold disc,
  rw [vieta_key_b f x y hx hy hneq, vieta_key_c f x y hx hy hneq],
  ring,
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

lemma eval_dx_at'
{K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: f.eval_dx_at x = (f.a + 2*x + y) * (x - y) :=
begin
  unfold eval_dx_at,
  rw [vieta_key_b f x y hx hy hneq],
  ring,
end

lemma is_multiple_root'
{K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: x = -f.a-x-y ↔ f.is_multiple_root x :=
begin
  transitivity y = -f.a-2*x, {
    split, {
      intro h,
      transitivity y - f.a - x - y - (-f.a-x-y),
      { rw ← sub_eq_zero, ring, },
      rw ← h, ring,
    },
    intro h,
    rw h,
    ring,
  },
  transitivity f.eval_dx_at x = 0, {
    rw eval_dx_at' f x y hx hy hneq,
    split, {
      intro h,
      rw h,
      ring,
    },
    intro h,
    simp [sub_ne_zero.2 hneq] at h,
    transitivity y - (f.a + 2*x + y),
    { rw h, ring, },
    rw ← sub_eq_zero, ring,
  },
  unfold is_root at hx,
  unfold is_multiple_root,
  simp [hx],
end

lemma has_multiple_root_iff_disc_zero'
{K : Type*} [integral_domain K] (f : monic_cubic_poly K) (x y : K)
(hx : f.is_root x)
(hy : f.is_root y)
(hneq : x ≠ y)
: x = -f.a-x-y ∨ y = -f.a-x-y ↔ f.disc = 0 :=
begin
  split, {
    intro h1,
    cases h1 with h1 h1, {
      rw is_multiple_root' f x y hx hy hneq at h1,
      exact has_multiple_root_implies_disc_zero f ⟨ x, h1 ⟩,
    },
    replace h1 := calc y = -f.a-x-y : h1
    ... = -f.a-y-x : by ring,
    rw is_multiple_root' f y x hy hx hneq.symm at h1,
    exact has_multiple_root_implies_disc_zero f ⟨ y, h1 ⟩,
  },
  intro h1,
  rw disc_eq_prod_of_roots f x y hx hy hneq at h1,
  simp [sub_ne_zero.2 hneq] at h1,
  cases h1 with h1 h1, {
    left,
    transitivity x - (f.a + 2*x + y),
    { rw h1, ring, },
    rw ← sub_eq_zero, ring,
  },
  right,
  transitivity y - (f.a + x + 2*y),
  { rw h1, ring, },
  rw ← sub_eq_zero, ring,
end

end monic_cubic_poly
