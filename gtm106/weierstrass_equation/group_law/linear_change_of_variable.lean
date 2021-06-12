import algebra.field
import gtm106.weierstrass_equation.linear_change_of_variable
import gtm106.weierstrass_equation.group_law.basic
import tactic

namespace weierstrass_equation

-- ================
-- P ↦ -P
-- ================

namespace neg_of_affine_plane_point

lemma lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (cov : linear_change_of_variable K)
: cov.change_affine_point (E.neg_of_affine_plane_point P)
= (cov.change_curve E).neg_of_affine_plane_point (cov.change_affine_point P) :=
begin
  simp only [linear_change_of_variable.change_affine_point,
    linear_change_of_variable.change_curve,
    neg_of_affine_plane_point],
  split,
  { refl, },
  field_simp [cov.hu],
  ring,
end

end neg_of_affine_plane_point

-- ================
-- Intersection with line
-- ================

-- TODO:

namespace intersection_with_line

def A_lcov {K : Type*} [field K]
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K) : K
:= (A - cov.s) / cov.u

lemma B_lcov {K : Type*} [field K]
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: B (cov.change_affine_point P) (A_lcov P A cov)
= (B P A + A * cov.r - cov.t) / cov.u ^ 3 :=
begin
  simp only [linear_change_of_variable.change_affine_point,
    A_lcov, B],
  field_simp [cov.hu],
  ring,
end

lemma a_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: a (cov.change_curve E) (A_lcov P A cov)
= (a E A + 3 * cov.r) / cov.u ^ 2 :=
begin
  simp only [linear_change_of_variable.change_curve,
    a, A_lcov],
  field_simp [cov.hu],
  ring,
end

lemma b_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: b (cov.change_curve E) (cov.change_affine_point P) (A_lcov P A cov)
= (b E P A + 2 * a E A * cov.r + 3 * cov.r ^ 2) / cov.u ^ 4 :=
begin
  unfold b,
  rw B_lcov,
  simp only [linear_change_of_variable.change_curve,
    a, A_lcov, B],
  field_simp [cov.hu],
  ring,
end

lemma c_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: c (cov.change_curve E) (cov.change_affine_point P) (A_lcov P A cov)
= (c E P A + b E P A * cov.r + a E A * cov.r ^ 2 + cov.r ^ 3) / cov.u ^ 6 :=
begin
  unfold c,
  rw B_lcov,
  simp only [linear_change_of_variable.change_curve,
    b, a, B],
  field_simp [cov.hu],
  ring,
end

lemma disc_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: monic_cubic_poly.disc ⟨ a (cov.change_curve E) (A_lcov P A cov),
  b (cov.change_curve E) (cov.change_affine_point P) (A_lcov P A cov),
  c (cov.change_curve E) (cov.change_affine_point P) (A_lcov P A cov) ⟩
= monic_cubic_poly.disc ⟨ a E A,
  b E P A,
  c E P A ⟩ / cov.u ^ 12
:=
begin
  simp only [a_lcov, b_lcov, c_lcov,
    monic_cubic_poly.disc],
  simp only [a, b, c, B],
  field_simp [cov.hu],
  rw ← sub_eq_zero,
  -- ring_exp,
  sorry,
end

end intersection_with_line

-- ================
-- P ↦ -2*P
-- ================

-- TODO:

namespace neg_of_double_of_affine_plane_point

end neg_of_double_of_affine_plane_point

-- ================
-- (P1, P2) ↦ -(P1 + P2)
-- ================

-- TODO:

namespace neg_of_add_of_affine_plane_point

end neg_of_add_of_affine_plane_point

-- ================
-- (P1, P2) ↦ P1 + P2
-- ================

-- TODO:

end weierstrass_equation
