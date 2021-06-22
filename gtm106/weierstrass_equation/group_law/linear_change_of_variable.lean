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
: (cov.change_curve E).neg_of_affine_plane_point (cov.change_affine_point P)
= cov.change_affine_point (E.neg_of_affine_plane_point P) :=
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

namespace intersection_with_line

def A_lcov {K : Type*} [field K]
(A : K) (cov : linear_change_of_variable K) : K
:= (A - cov.s) / cov.u

@[simp]
lemma B_lcov {K : Type*} [field K]
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: B (cov.change_affine_point P) (A_lcov A cov)
= (B P A + A * cov.r - cov.t) / cov.u ^ 3 :=
begin
  simp only [linear_change_of_variable.change_affine_point,
    A_lcov, B],
  field_simp [cov.hu],
  ring,
end

@[simp]
lemma a_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(A : K) (cov : linear_change_of_variable K)
: a (cov.change_curve E) (A_lcov A cov)
= (a E A + 3 * cov.r) / cov.u ^ 2 :=
begin
  simp only [linear_change_of_variable.change_curve,
    a, A_lcov],
  field_simp [cov.hu],
  ring,
end

@[simp]
lemma b_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: b (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov)
= (b E P A + 2 * a E A * cov.r + 3 * cov.r ^ 2) / cov.u ^ 4 :=
begin
  unfold b,
  rw B_lcov,
  simp only [linear_change_of_variable.change_curve,
    a, A_lcov, B],
  field_simp [cov.hu],
  ring,
end

@[simp]
lemma c_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: c (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov)
= (c E P A + b E P A * cov.r + a E A * cov.r ^ 2 + cov.r ^ 3) / cov.u ^ 6 :=
begin
  unfold c,
  rw B_lcov,
  simp only [linear_change_of_variable.change_curve,
    b, a, B],
  field_simp [cov.hu],
  ring,
end

@[simp]
lemma disc_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K)
: monic_cubic_poly.disc ⟨ a (cov.change_curve E) (A_lcov A cov),
  b (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov),
  c (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov) ⟩
= monic_cubic_poly.disc ⟨ a E A,
  b E P A,
  c E P A ⟩ / cov.u ^ 12
:=
begin
  simp only [a_lcov, b_lcov, c_lcov,
    monic_cubic_poly.disc],
  field_simp [cov.hu, pow_succ],
  ring,
end

@[simp]
lemma eval_at_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K) (x : K)
: eval_at (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov) (x/cov.u^2 - cov.r/cov.u^2)
= eval_at E P A x / cov.u ^ 6 :=
begin
  simp only [eval_at, monic_cubic_poly.eval_at,
    a_lcov, b_lcov, c_lcov],
  field_simp [cov.hu, pow_succ],
  ring,
end

@[simp]
lemma eval_dx_at_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K) (x : K)
: monic_cubic_poly.eval_dx_at ⟨ a (cov.change_curve E) (A_lcov A cov),
  b (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov),
  c (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov) ⟩
  (x/cov.u^2 - cov.r/cov.u^2)
= monic_cubic_poly.eval_dx_at ⟨ a E A,
  b E P A,
  c E P A ⟩ x / cov.u ^ 4 :=
begin
  simp only [monic_cubic_poly.eval_dx_at,
    a_lcov, b_lcov, c_lcov],
  field_simp [cov.hu, pow_succ],
  ring,
end

lemma is_on_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K) (x : K)
: is_on (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov) (x/cov.u^2 - cov.r/cov.u^2)
↔ is_on E P A x :=
begin
  unfold is_on,
  rw eval_at_lcov E P A cov x,
  simp,
end

lemma is_on_2_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K) (cov : linear_change_of_variable K) (x : K)
: is_on_2 (cov.change_curve E) (cov.change_affine_point P) (A_lcov A cov) (x/cov.u^2 - cov.r/cov.u^2)
↔ is_on_2 E P A x :=
begin
  unfold is_on_2,
  rw eval_dx_at_lcov E P A cov x,
  simp,
end

end intersection_with_line

-- ================
-- P ↦ -2*P
-- ================

namespace neg_of_double_of_affine_plane_point

@[simp]
lemma A_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(cov : linear_change_of_variable K)
: A (cov.change_curve E) (cov.change_affine_point P)
= (A E P - C E P * cov.s) / cov.u ^ 4 :=
begin
  simp only [A1, C1, linear_change_of_variable.eval_dx_at_affine_point],
  ring,
end

@[simp]
lemma C_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(cov : linear_change_of_variable K)
: C (cov.change_curve E) (cov.change_affine_point P)
= C E P / cov.u ^ 3 :=
begin
  simp only [A1, C1, linear_change_of_variable.eval_dy_at_affine_point],
end

lemma x_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P) (hC : C E P ≠ 0)
(cov : linear_change_of_variable K)
: x (cov.change_curve E) (cov.change_affine_point P)
= x E P/cov.u^2 - cov.r/cov.u^2 :=
begin
  have h' := (cov.preserve_affine_point E P).1 h,
  have hC' : C (cov.change_curve E) (cov.change_affine_point P) ≠ 0 := by {
    simp [hC],
  },
  have hC2 : (C E P / cov.u ^ 3) ^ 2 = C E P ^ 2 / cov.u ^ 6 := by {
    field_simp [pow_succ],
    ring,
  },
  rw [x' _ _ h hC, x' _ _ h' hC', ← C' _ _ h, ← C' _ _ h', C_lcov, hC2],
  replace hC : C E P ^ 2 ≠ 0 := by simp [hC],
  rw C' _ _ h at hC ⊢,
  simp [linear_change_of_variable.change_affine_point],
  field_simp [hC],
  field_simp [pow_succ],
  ring,
end

lemma y_lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P) (hC : C E P ≠ 0)
(cov : linear_change_of_variable K)
: y (cov.change_curve E) (cov.change_affine_point P)
= y E P/cov.u^3 - cov.s*x E P/cov.u^3 + (cov.r*cov.s-cov.t)/cov.u^3 :=
begin
  unfold y,
  simp [x_lcov E P h hC],
  simp only [linear_change_of_variable.change_affine_point],
  field_simp [hC],
  ring,
end

lemma lcov {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P) (hC : C E P ≠ 0)
(cov : linear_change_of_variable K)
: (cov.change_curve E).neg_of_double_of_affine_plane_point (cov.change_affine_point P)
= cov.change_affine_point (E.neg_of_double_of_affine_plane_point P) :=
begin
  simp only [affine_plane_point.ext_iff],
  exact ⟨ x_lcov E P h hC cov, y_lcov E P h hC cov ⟩,
end

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
