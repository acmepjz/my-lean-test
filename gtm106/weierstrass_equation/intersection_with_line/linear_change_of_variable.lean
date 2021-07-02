import algebra.field
import gtm106.weierstrass_equation.linear_change_of_variable
import gtm106.weierstrass_equation.intersection_with_line.basic
import tactic

def linear_change_of_variable.change_intersection_with_line
{K : Type*} [field K] (cov : linear_change_of_variable K)
(L : weierstrass_equation.intersection_with_line K)
: weierstrass_equation.intersection_with_line K
:= ⟨ cov.change_curve L.E, (L.A - cov.s) / cov.u, (L.B + L.A * cov.r - cov.t) / cov.u ^ 3 ⟩

def linear_change_of_variable.change_x
{K : Type*} [field K] (cov : linear_change_of_variable K)
(x : K) : K
:= x / cov.u ^ 2 - cov.r / cov.u ^ 2

namespace weierstrass_equation

namespace intersection_with_line

def from_point_lcov {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: from_point (cov.change_curve E) (cov.change_affine_point P) ((A - cov.s) / cov.u)
= cov.change_intersection_with_line (from_point E P A) :=
begin
  simp [from_point, linear_change_of_variable.change_intersection_with_line,
    linear_change_of_variable.change_affine_point],
  field_simp,
  ring,
end

lemma point_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
(x : K)
: (cov.change_intersection_with_line L).point (cov.change_x x)
= cov.change_affine_point (L.point x) :=
begin
  simp only [linear_change_of_variable.change_intersection_with_line,
    linear_change_of_variable.change_affine_point,
    linear_change_of_variable.change_x,
    point],
  split, { refl, },
  field_simp,
  ring,
end

@[simp]
lemma a_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
: (cov.change_intersection_with_line L).a
= (L.a + 3 * cov.r) / cov.u ^ 2 :=
begin
  simp only [linear_change_of_variable.change_intersection_with_line,
    linear_change_of_variable.change_curve,
    a],
  field_simp,
  ring,
end

@[simp]
lemma b_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
: (cov.change_intersection_with_line L).b
= (L.b + 2 * L.a * cov.r + 3 * cov.r ^ 2) / cov.u ^ 4 :=
begin
  unfold b,
  simp only [linear_change_of_variable.change_intersection_with_line,
    linear_change_of_variable.change_curve,
    a],
  field_simp,
  ring,
end

@[simp]
lemma c_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
: (cov.change_intersection_with_line L).c
= (L.c + L.b * cov.r + L.a * cov.r ^ 2 + cov.r ^ 3) / cov.u ^ 6 :=
begin
  unfold c,
  simp only [linear_change_of_variable.change_intersection_with_line,
    linear_change_of_variable.change_curve,
    b, a],
  field_simp,
  ring,
end

@[simp]
lemma disc_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
: (cov.change_intersection_with_line L).poly.disc
= L.poly.disc / cov.u ^ 12
:=
begin
  simp only [poly, a_lcov, b_lcov, c_lcov,
    monic_cubic_poly.disc],
  field_simp [cov.hu, pow_succ],
  ring,
end

@[simp]
lemma eval_at_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
(x : K)
: (cov.change_intersection_with_line L).poly.eval_at (cov.change_x x)
= L.poly.eval_at x / cov.u ^ 6 :=
begin
  simp only [poly, monic_cubic_poly.eval_at,
    a_lcov, b_lcov, c_lcov, linear_change_of_variable.change_x],
  field_simp [cov.hu, pow_succ],
  ring,
end

@[simp]
lemma eval_dx_at_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
(x : K)
: (cov.change_intersection_with_line L).poly.eval_dx_at (cov.change_x x)
= L.poly.eval_dx_at x / cov.u ^ 4 :=
begin
  simp only [poly, monic_cubic_poly.eval_dx_at,
    a_lcov, b_lcov, c_lcov, linear_change_of_variable.change_x],
  field_simp [cov.hu, pow_succ],
  ring,
end

lemma is_on_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
(x : K)
: (cov.change_intersection_with_line L).poly.is_root (cov.change_x x)
↔ L.poly.is_root x :=
begin
  unfold monic_cubic_poly.is_root,
  simp,
end

lemma is_on_2_lcov {K : Type*} [field K]
(L : intersection_with_line K) (cov : linear_change_of_variable K)
(x : K)
: (cov.change_intersection_with_line L).poly.is_multiple_root (cov.change_x x)
↔ L.poly.is_multiple_root x :=
begin
  unfold monic_cubic_poly.is_multiple_root,
  simp,
end

end intersection_with_line

end weierstrass_equation
