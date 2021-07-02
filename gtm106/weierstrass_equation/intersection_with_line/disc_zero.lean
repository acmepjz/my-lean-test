import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.non_singular_criterion
import gtm106.weierstrass_equation.linear_change_of_variable
import gtm106.weierstrass_equation.intersection_with_line.basic
import gtm106.weierstrass_equation.intersection_with_line.linear_change_of_variable
import tactic

namespace weierstrass_equation

namespace intersection_with_line

lemma disc_zero_implies_tangent.p00
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(hP' : P = ⟨ 0, 0 ⟩)
(A : K)
(hP : E.affine_point_on_curve P)
(h : (from_point E P A).poly.disc = 0)
: - E.eval_dx_at_affine_point P = A * E.eval_dy_at_affine_point P
∨ ((ring_char K = 2 → my_perfect_field K) → ∃ (Q : affine_plane_point K), E.affine_point_on_curve Q ∧ Q.x ≠ 0 ∧ Q.y = A * Q.x ∧ - E.eval_dx_at_affine_point Q = A * E.eval_dy_at_affine_point Q) :=
begin
  simp [affine_point_on_curve, eval_at_affine_point, hP', zero_pow] at hP,
  simp only [eval_dx_at_affine_point,
    eval_dy_at_affine_point],
  simp only [from_point, poly, monic_cubic_poly.disc, a, b, c, hP] at h,
  simp [hP', zero_pow] at h ⊢,
  let f : monic_quad_poly K := ⟨ E.a2 - (A + E.a1) * A, E.a4 - A * E.a3 ⟩,
  have : (E.a2 - (A + E.a1) * A) ^ 2 * (E.a4 - A * E.a3) ^ 2 - 4 * (E.a4 - A * E.a3) ^ 3
  = f.disc * (E.a4 - A * E.a3) ^ 2 := by {
    simp only [monic_quad_poly.disc], ring,
  },
  rw this at h, clear this,
  simp at h,
  by_cases h1 : E.a4 - A * E.a3 = 0, {
    left,
    exact sub_eq_zero.1 h1,
  },
  right,
  simp [h1] at h,
  intro hperfect,
  rcases f.disc_zero_implies_has_multiple_root hperfect h with ⟨ x, hx1, hx2 ⟩,
  have hx0 : x ≠ 0 := by {
    intro hx,
    simp [hx, monic_quad_poly.eval_at] at hx1,
    exact h1 hx1,
  },
  let Q : affine_plane_point K := ⟨ x, A * x ⟩,
  use Q,
  simp [hx0, affine_point_on_curve, eval_at_affine_point,
    eval_dx_at_affine_point, eval_dy_at_affine_point, hP],
  split, {
    transitivity - x * f.eval_at x, {
      simp only [monic_quad_poly.eval_at], ring,
    },
    simp [hx1],
  },
  rw ← sub_eq_zero,
  transitivity f.eval_at x + x * f.eval_dx_at x, {
    rw ← sub_eq_zero,
    simp only [monic_quad_poly.eval_at, monic_quad_poly.eval_dx_at],
    ring,
  },
  simp [hx1, hx2],
end

lemma disc_zero_implies_tangent
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
(h : (from_point E P A).poly.disc = 0)
: - E.eval_dx_at_affine_point P = A * E.eval_dy_at_affine_point P
∨ ((ring_char K = 2 → my_perfect_field K) → ∃ (Q : affine_plane_point K), E.affine_point_on_curve Q ∧ Q.x ≠ P.x ∧ Q.y - P.y = A * (Q.x - P.x) ∧ - E.eval_dx_at_affine_point Q = A * E.eval_dy_at_affine_point Q) :=
begin
  set! C : linear_change_of_variable K := ⟨ 1, P.x, 0, P.y, by simp ⟩ with hC, clear_value C,
  set! E' := C.change_curve E with hE', clear_value E',
  set! P' := C.change_affine_point P with hP', clear_value P',
  replace h : (from_point E P A).poly.disc / C.u ^ 12 = 0 := by {
    simp [h],
  },
  rw [← disc_lcov _ C, ← from_point_lcov, ← hE', ← hP'] at h,
  simp [hC] at h,
  rw [C.preserve_affine_point E P, ← hE', ← hP'] at hP,
  cases disc_zero_implies_tangent.p00 E' P' (by {
    simp [hP', hC, linear_change_of_variable.change_affine_point],
  }) A hP h with h h, {
    left,
    simp [hE', hP', hC] at h,
    exact h,
  },
  right,
  intro hperfect,
  rcases h hperfect with ⟨ Q', ⟨ h1, h2, h3, h4 ⟩ ⟩,
  set! Q := C.inverse.change_affine_point Q' with hQ, clear_value Q,
  apply_fun C.change_affine_point at hQ,
  simp [linear_change_of_variable.change_affine_point.comp] at hQ,
  rw [← hQ, hE', ← linear_change_of_variable.preserve_affine_point] at h1,
  use [Q, h1],
  simp [← hQ, linear_change_of_variable.change_affine_point, hC] at h2 h3,
  use [sub_ne_zero.1 h2],
  split, { rw ← h3, ring, },
  simp [← hQ, hE', hC] at h4,
  exact h4,
end

lemma tangent_implies_disc_zero.p00
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(hP' : P = ⟨ 0, 0 ⟩)
(A : K)
(hP : E.affine_point_on_curve P)
(h : - E.eval_dx_at_affine_point P = A * E.eval_dy_at_affine_point P)
: (from_point E P A).poly.disc = 0 :=
begin
  simp [affine_point_on_curve, eval_at_affine_point, hP', zero_pow] at hP,
  simp only [eval_dx_at_affine_point,
    eval_dy_at_affine_point] at h,
  simp only [from_point, poly, monic_cubic_poly.disc, a, b, c, hP],
  simp [hP', zero_pow] at h ⊢,
  rw h,
  ring,
end

lemma tangent_implies_disc_zero
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
(h : - E.eval_dx_at_affine_point P = A * E.eval_dy_at_affine_point P)
: (from_point E P A).poly.disc = 0 :=
begin
  set! C : linear_change_of_variable K := ⟨ 1, P.x, 0, P.y, by simp ⟩ with hC, clear_value C,
  set! E' := C.change_curve E with hE', clear_value E',
  set! P' := C.change_affine_point P with hP', clear_value P',
  suffices : (from_point E P A).poly.disc / C.u ^ 12 = 0, {
    simp only [hC, one_pow, div_one] at this,
    exact this,
  },
  rw [← disc_lcov _ C, ← from_point_lcov, ← hE', ← hP'],
  rw [C.preserve_affine_point E P, ← hE', ← hP'] at hP,
  simp [hC],
  apply tangent_implies_disc_zero.p00 E' P' (by {
    simp [hP', hC, linear_change_of_variable.change_affine_point],
  }) A hP,
  simp [hE', hP'],
  simp [h, hC],
end

lemma disc_zero_iff_tangent {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
(hperfect : ring_char K = 2 → my_perfect_field K)
: (from_point E P A).poly.disc = 0
↔ - E.eval_dx_at_affine_point P = A * E.eval_dy_at_affine_point P
∨ ∃ (Q : affine_plane_point K), E.affine_point_on_curve Q ∧ Q.x ≠ P.x ∧ Q.y - P.y = A * (Q.x - P.x) ∧ - E.eval_dx_at_affine_point Q = A * E.eval_dy_at_affine_point Q :=
begin
  split, {
    intro h,
    cases disc_zero_implies_tangent E P A hP h with h h, {
      left, exact h,
    },
    right, exact h hperfect,
  },
  intro h,
  rcases h with h | ⟨ Q, h1, h2, h3, h4 ⟩, {
    exact tangent_implies_disc_zero E P A hP h,
  },
  replace h3 : Q = (from_point E P A).point Q.x := by {
    simp [from_point, point, affine_plane_point.ext_iff],
    rw [← sub_eq_zero, sub_sub, sub_eq_zero] at h3,
    rw h3, ring,
  },
  replace h3 : from_point E P A = from_point E Q A := by {
    rw [h3, from_point'' E P A Q.x],
  },
  rw h3,
  exact tangent_implies_disc_zero E Q A h1 h4,
end

end intersection_with_line

end weierstrass_equation
