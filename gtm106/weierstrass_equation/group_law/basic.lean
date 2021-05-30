import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import tactic

lemma Vieta_formula_cubic_2 {K : Type*} [comm_ring K] {a b c x : K}
(h : x^3 + a*x^2 + b*x + c = 0)
(h' : 3*x^2 + 2*a*x + b = 0)
: (-a-2*x)^3 + a*(-a-2*x)^2 + b*(-a-2*x) + c = 0 :=
begin
  transitivity (x^3 + a*x^2 + b*x + c) + (3*x^2 + 2*a*x + b) * (-a-3*x),
  { rw ← sub_eq_zero, ring, },
  have := congr (congr_arg has_add.add h) (congr_arg (λ f, f*(-a-3*x)) h'),
  rw [zero_mul, zero_add] at this,
  exact this,
end

lemma Vieta_formula_cubic {K : Type*} [field K] {a b c x y : K}
(hx : x^3 + a*x^2 + b*x + c = 0)
(hy : y^3 + a*y^2 + b*y + c = 0)
(hneq : x ≠ y)
: (-a-x-y)^3 + a*(-a-x-y)^2 + b*(-a-x-y) + c = 0 :=
begin
  have hxy : (x^2+x*y+y^2 + a*(x+y) + b) * (x - y) = 0 := by {
    transitivity (x^3 + a*x^2 + b*x + c) - (y^3 + a*y^2 + b*y + c),
    { rw ← sub_eq_zero, ring, },
    have := congr (congr_arg has_sub.sub hx) hy,
    rw sub_zero at this,
    exact this,
  },
  simp [sub_ne_zero.2 hneq] at hxy,
  transitivity (x^3 + a*x^2 + b*x + c) + (x^2+x*y+y^2 + a*(x+y) + b) * (-a-2*x-y),
  { rw ← sub_eq_zero, ring, },
  have := congr (congr_arg has_add.add hx) (congr_arg (λ f, f*(-a-2*x-y)) hxy),
  rw [zero_mul, zero_add] at this,
  exact this,
end

namespace weierstrass_equation

-- ================
-- P ↦ -P
-- ================

def neg_of_affine_plane_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
(P : affine_plane_point K) : affine_plane_point K
:= ⟨ P.x, -P.y - E.a1*P.x - E.a3 ⟩

lemma neg_of_affine_plane_point.self_eq_neg_iff
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
(P : affine_plane_point K)
: P = E.neg_of_affine_plane_point P ↔ 2*P.y + E.a1*P.x + E.a3 = 0 :=
begin
  simp [neg_of_affine_plane_point, affine_plane_point.ext_iff],
  split, {
    intro h,
    rw ← sub_eq_zero.2 h,
    ring,
  },
  intro h,
  rw [← sub_eq_zero, ← h],
  ring,
end

@[simp]
lemma neg_of_neg_of_affine_plane_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
(P : affine_plane_point K)
: E.neg_of_affine_plane_point (E.neg_of_affine_plane_point P) = P :=
begin
  simp [neg_of_affine_plane_point, affine_plane_point.ext_iff],
  ring,
end

@[simp]
lemma eval_at_affine_point.neg
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
(P : affine_plane_point K)
: E.eval_at_affine_point (E.neg_of_affine_plane_point P) = E.eval_at_affine_point P :=
begin
  simp [neg_of_affine_plane_point, affine_point_on_curve, eval_at_affine_point],
  ring,
end

@[simp]
lemma affine_point_on_curve.neg
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
(P : affine_plane_point K)
: E.affine_point_on_curve (E.neg_of_affine_plane_point P) ↔ E.affine_point_on_curve P :=
begin
  simp [affine_point_on_curve],
end

lemma same_x_implies_same_or_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x = 0)
: P1.y - P2.y = 0 ∨ P1.y + P2.y + E.a1*P1.x + E.a3 = 0 :=
begin
  rw sub_eq_zero at hx,
  unfold affine_point_on_curve eval_at_affine_point at h1 h2,
  rw ← hx at h2,
  repeat { rw sub_sub at h1 h2 },
  rw sub_eq_zero at h1 h2,
  have h3 := congr (congr_arg has_sub.sub h1) h2,
  simp at h3,
  replace h3 : (P1.y - P2.y) * (P1.y + P2.y + E.a1*P1.x + E.a3) = 0 := by {
    rw ← h3, ring,
  },
  exact mul_eq_zero.1 h3,
end

lemma same_x_implies_same_or_neg'
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x = 0)
: P1 = P2 ∨ P1 = E.neg_of_affine_plane_point P2 :=
begin
  cases same_x_implies_same_or_neg P1 P2 h1 h2 hx with hy hy, {
    left,
    rw sub_eq_zero at hx hy,
    simp [affine_plane_point.ext_iff, hx, hy],
  },
  right,
  rw sub_eq_zero at hx,
  simp [neg_of_affine_plane_point, affine_plane_point.ext_iff, hx],
  rw [← sub_eq_zero, ← hy, hx],
  ring,
end

namespace intersection_with_line

section

-- intersection of `y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6`
-- and `y - y0 = A*(x - x0)`
parameters {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)

def B : K := P.y - A*P.x
def a : K := E.a2 - (A + E.a1)*A
def b : K := E.a4 - (2*A + E.a1)*B - A*E.a3
def c : K := E.a6 - (B + E.a3)*B
def eval_at (x : K) := x^3 + a*x^2 + b*x + c
def is_on (x : K) : Prop := eval_at x = 0
def is_on_2 (x : K) : Prop := 3*x^2 + 2*a*x + b = 0

lemma eval_at_eq_eval_at (x : K)
: eval_at x = -E.eval_at_affine_point ⟨ x, A*x+B ⟩ :=
sub_eq_zero.1 begin
  simp only [eval_at, a, b, c, eval_at_affine_point],
  ring,
end

lemma is_on_iff_is_on (x : K)
: is_on x ↔ E.affine_point_on_curve ⟨ x, A*x+B ⟩ :=
begin
  simp [is_on, affine_point_on_curve, eval_at_eq_eval_at],
end

lemma is_on_this (h : E.affine_point_on_curve P) : is_on P.x :=
begin
  rw is_on_iff_is_on,
  simp [B],
  exact h,
end

end

end intersection_with_line

-- ================
-- P ↦ -2*P
-- ================

namespace neg_of_double_of_affine_plane_point

section

parameters {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)

def A : K := 3*P.x^2 + 2*E.a2*P.x + E.a4 - E.a1*P.y
-- def B : K := -P.x^3 + E.a4*P.x + 2*E.a6 - E.a3*P.y -- we avoid using B
def C : K := 2*P.y + E.a1*P.x + E.a3
def x : K := (A/C + E.a1)*(A/C) - E.a2 - 2*P.x -- we avoid using (A/C)^2
def y : K := P.y + (x - P.x)*(A/C) -- we avoid using B

lemma C' (h : E.affine_point_on_curve P)
: C^2 = 4*P.x^3 + E.b2*P.x^2 + 2*E.b4*P.x + E.b6 :=
sub_eq_zero.1 begin
  transitivity E.eval_at_affine_point P * 4, {
    rw ← sub_eq_zero,
    simp only [eval_at_affine_point, C, b2, b4, b6],
    ring,
  },
  unfold affine_point_on_curve at h,
  simp [h],
end

lemma x' (h : E.affine_point_on_curve P) (hC : C ≠ 0)
: x = (P.x^4 - E.b4*P.x^2 - 2*E.b6*P.x - E.b8) / (4*P.x^3 + E.b2*P.x^2 + 2*E.b4*P.x + E.b6) :=
sub_eq_zero.1 begin
  simp only [← C' E P h, x],
  field_simp [hC],
  transitivity ((A E P + E.a1 * C E P) * A E P
  - C E P * C E P * (E.a2 + 2 * P.x)
  - (P.x ^ 4 - E.b4 * P.x ^ 2 - 2 * E.b6 * P.x - E.b8)) * (C E P)^2,
  { rw ← sub_eq_zero, ring, },
  simp [hC],
  transitivity E.eval_at_affine_point P * (-E.a1^2 - 4*E.a2 - 8*P.x), {
    rw ← sub_eq_zero,
    simp only [eval_at_affine_point, A, C, b4, b6, b8],
    ring,
  },
  unfold affine_point_on_curve at h,
  simp [h],
end

end

lemma C_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
: C E (E.neg_of_affine_plane_point P) = -C E P :=
sub_eq_zero.1 begin
  simp only [C, neg_of_affine_plane_point],
  ring,
end

lemma x_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P) (hC : C E P ≠ 0)
: x E (E.neg_of_affine_plane_point P) = x E P :=
begin
  rw x' E P h hC,
  rw x' E (E.neg_of_affine_plane_point P) (by simp [h]) (by simp [C_of_neg E P, hC]),
  simp only [neg_of_affine_plane_point],
end

lemma y_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P) (hC : C E P ≠ 0)
: y E (E.neg_of_affine_plane_point P) = - y E P - E.a1 * x E P - E.a3 :=
sub_eq_zero.1 begin
  simp only [y, x_of_neg E P h hC, C_of_neg],
  simp only [neg_of_affine_plane_point, A],
  field_simp [hC],
  simp only [C],
  ring,
end

end neg_of_double_of_affine_plane_point

/--
NOTE: P should not be a 2-torsion, otherwise the result is incorrect
-/
def neg_of_double_of_affine_plane_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) : affine_plane_point K :=
⟨ neg_of_double_of_affine_plane_point.x E P,
  neg_of_double_of_affine_plane_point.y E P ⟩

namespace neg_of_double_of_affine_plane_point

lemma neg {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P) (hC : C E P ≠ 0)
: E.neg_of_double_of_affine_plane_point (E.neg_of_affine_plane_point P)
= E.neg_of_affine_plane_point (E.neg_of_double_of_affine_plane_point P) :=
begin
  simp only [neg_of_double_of_affine_plane_point, affine_plane_point.ext_iff,
    x_of_neg E P h hC, y_of_neg E P h hC],
  simp [neg_of_affine_plane_point],
end

end neg_of_double_of_affine_plane_point

lemma affine_point_on_curve.neg_of_double
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
(hy : 2*P.y + E.a1*P.x + E.a3 ≠ 0)
: E.affine_point_on_curve (E.neg_of_double_of_affine_plane_point P) :=
begin
  set! A := (neg_of_double_of_affine_plane_point.A E P)/(neg_of_double_of_affine_plane_point.C E P) with hA, clear_value A,
  have hC : neg_of_double_of_affine_plane_point.C E P = 2*P.y + E.a1*P.x + E.a3 := rfl,
  have h1 : intersection_with_line.is_on E P A P.x := intersection_with_line.is_on_this E P A h,
  have h2 : intersection_with_line.is_on_2 E P A P.x := by {
    simp only [intersection_with_line.is_on_2,
      intersection_with_line.a, intersection_with_line.b, intersection_with_line.B,
      hA],
    rw ← hC at hy,
    field_simp [hy],
    simp only [neg_of_double_of_affine_plane_point.A,
      neg_of_double_of_affine_plane_point.C],
    ring,
  },
  have h3 := Vieta_formula_cubic_2 h1 h2,
  have h4 : -intersection_with_line.a E A - 2 * P.x = (E.neg_of_double_of_affine_plane_point P).x := by {
    simp only [hA, neg_of_double_of_affine_plane_point,
      neg_of_double_of_affine_plane_point.x,
      intersection_with_line.a],
    ring,
  },
  rw h4 at h3,
  change intersection_with_line.is_on E P A (E.neg_of_double_of_affine_plane_point P).x at h3,
  rw intersection_with_line.is_on_iff_is_on at h3,
  have h5 : A * (E.neg_of_double_of_affine_plane_point P).x + (intersection_with_line.B P A) = (E.neg_of_double_of_affine_plane_point P).y := by {
    simp only [hA, intersection_with_line.B, neg_of_double_of_affine_plane_point,
      neg_of_double_of_affine_plane_point.y],
    ring,
  },
  rw [h5] at h3,
  exact h3,
end

-- ================
-- (P1, P2) ↦ -(P1 + P2)
-- ================


namespace neg_of_add_of_affine_plane_point

section

parameters {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)

def A : K := P1.y - P2.y
-- def B : K := P2.y*P1.x - P1.y*P2.x -- we avoid using B
def C : K := P1.x - P2.x
def x : K := (A/C + E.a1)*(A/C) - E.a2 - P1.x - P2.x -- we avoid using (A/C)^2
def y : K := P1.y + (x - P1.x)*(A/C) -- we avoid using B

lemma y' (hC : C ≠ 0) : y = P2.y + (x - P2.x)*(A/C) :=
begin
  simp only [y, A],
  field_simp [hC],
  unfold C,
  ring,
end

end

lemma A_of_comm {K : Type*} [field K]
(P1 P2 : affine_plane_point K)
: A P2 P1 = - A P1 P2 := by simp [A]

lemma C_of_comm {K : Type*} [field K]
(P1 P2 : affine_plane_point K)
: C P2 P1 = - C P1 P2 := by simp [C]

lemma A_over_C_of_comm {K : Type*} [field K]
(P1 P2 : affine_plane_point K)
: A P2 P1 / C P2 P1 = A P1 P2 / C P1 P2 :=
begin
  rw [A_of_comm P1 P2, C_of_comm P1 P2],
  by_cases hC : C P1 P2 = 0, {
    simp [hC],
  },
  field_simp [hC],
end

lemma x_of_comm {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
: x E P2 P1 = x E P1 P2 :=
sub_eq_zero.1 begin
  simp only [x, A_over_C_of_comm P1 P2],
  ring,
end

lemma y_of_comm {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(hx : P1.x - P2.x ≠ 0)
: y E P2 P1 = y E P1 P2 :=
begin
  simp only [y, y' E P1 P2 hx, x_of_comm E P1 P2, A_over_C_of_comm P1 P2],
end

lemma A_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
: A (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2)
= - A P1 P2 - E.a1 * C P1 P2 :=
begin
  simp [A, C, neg_of_affine_plane_point],
  ring,
end

lemma C_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
: C (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2)
= C P1 P2 :=
begin
  simp [C, neg_of_affine_plane_point],
end

lemma A_over_C_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(hx : P1.x - P2.x ≠ 0)
: A (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2)
/ C (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2)
= - A P1 P2 / C P1 P2 - E.a1 :=
begin
  simp [A_of_neg, C_of_neg],
  change C P1 P2 ≠ 0 at hx,
  field_simp [hx],
  ring,
end

lemma x_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(hx : P1.x - P2.x ≠ 0)
: x E (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2) = x E P1 P2 :=
sub_eq_zero.1 begin
  simp only [x, A_over_C_of_neg E P1 P2 hx],
  simp only [neg_of_affine_plane_point],
  ring,
end

lemma y_of_neg {K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(hx : P1.x - P2.x ≠ 0)
: y E (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2)
= - y E P1 P2 - E.a1 * x E P1 P2 - E.a3 :=
sub_eq_zero.1 begin
  simp only [y, x_of_neg E P1 P2 hx, A_over_C_of_neg E P1 P2 hx],
  simp only [neg_of_affine_plane_point],
  ring,
end

end neg_of_add_of_affine_plane_point

/--
NOTE: P1.x and P2.x should be different, otherwise the result is incorrect
-/
def neg_of_add_of_affine_plane_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K) : affine_plane_point K :=
⟨ neg_of_add_of_affine_plane_point.x E P1 P2,
  neg_of_add_of_affine_plane_point.y E P1 P2 ⟩

namespace neg_of_add_of_affine_plane_point

lemma comm
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(hx : P1.x - P2.x ≠ 0)
: E.neg_of_add_of_affine_plane_point P1 P2 = E.neg_of_add_of_affine_plane_point P2 P1 :=
begin
  simp [neg_of_add_of_affine_plane_point, affine_plane_point.ext_iff,
    x_of_comm E P1 P2, y_of_comm E P1 P2 hx],
end

lemma neg
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(hx : P1.x - P2.x ≠ 0)
: E.neg_of_add_of_affine_plane_point (E.neg_of_affine_plane_point P1) (E.neg_of_affine_plane_point P2)
= E.neg_of_affine_plane_point (E.neg_of_add_of_affine_plane_point P1 P2) :=
begin
  simp only [neg_of_add_of_affine_plane_point, affine_plane_point.ext_iff,
    x_of_neg E P1 P2 hx, y_of_neg E P1 P2 hx],
  simp [neg_of_affine_plane_point],
end

end neg_of_add_of_affine_plane_point

lemma affine_point_on_curve.neg_of_add
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x ≠ 0)
: E.affine_point_on_curve (E.neg_of_add_of_affine_plane_point P1 P2) :=
begin
  have hx' := sub_ne_zero.2 (sub_ne_zero.1 hx).symm,
  set! A := (neg_of_add_of_affine_plane_point.A P1 P2)/(neg_of_add_of_affine_plane_point.C P1 P2) with hA, clear_value A,
  replace h1 : intersection_with_line.is_on E P1 A P1.x := intersection_with_line.is_on_this E P1 A h1,
  replace h2 : intersection_with_line.is_on E P1 A P2.x := by {
    rw intersection_with_line.is_on_iff_is_on,
    have h5 : A * P2.x + intersection_with_line.B P1 A = P2.y := by {
      simp only [hA, intersection_with_line.B, neg_of_add_of_affine_plane_point.A,
        neg_of_add_of_affine_plane_point.C],
      field_simp [hx, hx'],
      ring,
    },
    rw h5,
    exact h2,
  },
  have h3 := Vieta_formula_cubic h1 h2 (sub_ne_zero.1 hx),
  have h4 : -intersection_with_line.a E A - P1.x - P2.x = (E.neg_of_add_of_affine_plane_point P1 P2).x := by {
    simp only [hA, neg_of_add_of_affine_plane_point,
      neg_of_add_of_affine_plane_point.x,
      intersection_with_line.a],
    ring,
  },
  rw h4 at h3,
  change intersection_with_line.is_on E P1 A (E.neg_of_add_of_affine_plane_point P1 P2).x at h3,
  rw intersection_with_line.is_on_iff_is_on at h3,
  have h5 : A * (E.neg_of_add_of_affine_plane_point P1 P2).x + intersection_with_line.B P1 A = (E.neg_of_add_of_affine_plane_point P1 P2).y := by {
    simp only [hA, intersection_with_line.B, neg_of_add_of_affine_plane_point,
      neg_of_add_of_affine_plane_point.y],
    ring,
  },
  rw [h5] at h3,
  exact h3,
end

namespace affine_point

def neg
{K : Type*} [comm_ring K] {E : weierstrass_equation K}
: affine_point E → affine_point E
| infinite := infinite
| (finite P h) := finite (E.neg_of_affine_plane_point P)
  ((affine_point_on_curve.neg E P).2 h)

@[simp]
lemma neg_of_neg
{K : Type*} [comm_ring K] {E : weierstrass_equation K}
(P : affine_point E) : P.neg.neg = P :=
match P with
| infinite := by {
  simp [neg],
}
| (finite P h) := by {
  simp [neg],
}
end

noncomputable def neg_of_add
{K : Type*} [field K] {E : weierstrass_equation K}
: affine_point E → affine_point E → affine_point E
| infinite P := P.neg
| P infinite := P.neg
| (finite P1 h1) (finite P2 h2) := by {
  by_cases hx : P1.x - P2.x = 0, {
    by_cases hy : P1.y + P2.y + E.a1*P1.x + E.a3 = 0, {
      exact infinite,
    },
    exact finite (E.neg_of_double_of_affine_plane_point P1)
      (affine_point_on_curve.neg_of_double E P1 h1 (by {
        have h := same_x_implies_same_or_neg P1 P2 h1 h2 hx,
        simp [hy, sub_eq_zero] at h,
        rw [← h, ← two_mul] at hy,
        exact hy,
      })),
  },
  exact finite (E.neg_of_add_of_affine_plane_point P1 P2)
    (affine_point_on_curve.neg_of_add E P1 P2 h1 h2 hx),
}

lemma neg_of_add.comm
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.neg_of_add P2 = P2.neg_of_add P1 :=
match P1, P2 with
| infinite, infinite := by {
  simp [neg_of_add],
}
| infinite, (finite P2 h2) := by {
  simp [neg_of_add],
}
| (finite P1 h1), infinite := by {
  simp [neg_of_add],
}
| (finite P1 h1), (finite P2 h2) := by {
  simp [neg_of_add],
  by_cases hx : P1.x - P2.x = 0, {
    have hx' := sub_eq_zero.2 (sub_eq_zero.1 hx).symm,
    simp [hx, hx'],
    by_cases hy : P1.y + P2.y + E.a1*P1.x + E.a3 = 0, {
      have hy' := hy,
      rw [add_comm P1.y P2.y, sub_eq_zero.1 hx] at hy',
      simp [hy, hy'],
    },
    have hy' := hy,
    rw [add_comm P1.y P2.y, sub_eq_zero.1 hx] at hy',
    have h := same_x_implies_same_or_neg P1 P2 h1 h2 hx,
    simp [hy] at h,
    replace h := (affine_plane_point.ext_iff P1 P2).2 ⟨ sub_eq_zero.1 hx, sub_eq_zero.1 h ⟩,
    simp [hy, hy', h],
  },
  have hx' := sub_ne_zero.2 (sub_ne_zero.1 hx).symm,
  simp [hx, hx'],
  exact neg_of_add_of_affine_plane_point.comm E P1 P2 hx,
}
end

end affine_point

-- ================
-- (P1, P2) ↦ P1 + P2
-- ================

/--
NOTE: P should not be a 2-torsion, otherwise the result is incorrect
-/
def double_of_affine_plane_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) : affine_plane_point K :=
E.neg_of_affine_plane_point (E.neg_of_double_of_affine_plane_point P)

/--
NOTE: P1.x and P2.x should be different, otherwise the result is incorrect
-/
def add_of_affine_plane_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K) : affine_plane_point K :=
E.neg_of_affine_plane_point (E.neg_of_add_of_affine_plane_point P1 P2)

namespace affine_point

noncomputable def add
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E) : affine_point E
:= (P1.neg_of_add P2).neg

lemma add.comm
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.add P2 = P2.add P1 :=
begin
  unfold add,
  congr' 1,
  exact neg_of_add.comm P1 P2,
end

lemma add.zero_add
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: infinite.add P = P :=
match P with
| infinite := by {
  simp [add, neg_of_add],
}
| (finite P h) := by {
  simp [add, neg_of_add],
}
end

lemma add.add_zero
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: P.add infinite = P :=
match P with
| infinite := by {
  simp [add, neg_of_add],
}
| (finite P h) := by {
  simp [add, neg_of_add],
}
end

lemma add.add_left_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: P.neg.add P = infinite :=
match P with
| infinite := by {
  simp [add, neg_of_add, neg],
}
| (finite P h) := by {
  simp [add, neg_of_add, neg,
    neg_of_affine_plane_point],
  dsimp only,
  have h : -P.y - E.a1 * P.x - E.a3 + P.y + E.a1 * P.x + E.a3 = 0 := by ring,
  simp [h, neg],
}
end

lemma add.add_right_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: P.add P.neg = infinite :=
match P with
| infinite := by {
  simp [add, neg_of_add, neg],
}
| (finite P h) := by {
  simp [add, neg_of_add, neg,
    neg_of_affine_plane_point],
  dsimp only,
  have h : P.y + (-P.y - E.a1 * P.x - E.a3) + E.a1 * P.x + E.a3 = 0 := by ring,
  simp [h, neg],
}
end

lemma add.neg_add_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: (P1.neg).add P2.neg = P1.neg_of_add P2 :=
match P1, P2 with
| infinite, infinite := by {
  simp [add, neg, neg_of_add],
}
| infinite, (finite P2 h2) := by {
  simp [add, neg, neg_of_add],
}
| (finite P1 h1), infinite := by {
  simp [add, neg, neg_of_add],
}
| (finite P1 h1), (finite P2 h2) := by {
  simp [add, neg],
  by_cases hx : P1.x - P2.x = 0, {
    have hx' : (E.neg_of_affine_plane_point P1).x - (E.neg_of_affine_plane_point P2).x = 0 := by {
      simp only [neg_of_affine_plane_point, hx],
    },
    by_cases hy : P1.y + P2.y + E.a1*P1.x + E.a3 = 0, {
      have hy' : (E.neg_of_affine_plane_point P1).y + (E.neg_of_affine_plane_point P2).y + E.a1*(E.neg_of_affine_plane_point P1).x + E.a3 = 0, {
        replace hx := sub_eq_zero.1 hx,
        replace hy := congr_arg (λ x, -x) hy.symm,
        simp only [neg_zero] at hy,
        simp only [neg_of_affine_plane_point, hx, hy],
        ring,
      },
      simp [neg_of_add, hx, hx', hy, hy', neg],
    },
    have hP := same_x_implies_same_or_neg P1 P2 h1 h2 hx,
    simp [hy] at hP,
    replace hP : P1 = P2 := by {
      simp [affine_plane_point.ext_iff, sub_eq_zero.1 hx, sub_eq_zero.1 hP],
    },
    have hy' : (E.neg_of_affine_plane_point P1).y + (E.neg_of_affine_plane_point P2).y + E.a1*(E.neg_of_affine_plane_point P1).x + E.a3 ≠ 0, {
      replace hx := sub_eq_zero.1 hx,
      revert hy,
      contrapose,
      push_neg,
      intro hy,
      simp [neg_of_affine_plane_point] at hy,
      replace hy := congr (congr_arg has_add.add (eq.refl P1.y)) hy.symm,
      rw add_zero at hy,
      rw [hy, hx],
      ring,
    },
    simp [neg_of_add, hx, hx', hy, hy', neg],
    rw [← hP, ← two_mul] at hy,
    simp [neg_of_double_of_affine_plane_point.neg E P1 h1 hy],
  },
  have hx' : (E.neg_of_affine_plane_point P1).x - (E.neg_of_affine_plane_point P2).x ≠ 0 := by {
    simp only [neg_of_affine_plane_point], exact hx,
  },
  simp [neg_of_add, hx, hx', neg, neg_of_add_of_affine_plane_point.neg E P1 P2 hx],
}
end

lemma add.add_to_zero_iff_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.add P2 = infinite ↔ P2 = P1.neg :=
match P1, P2 with
| infinite, infinite := by {
  simp [add, neg_of_add, neg],
}
| infinite, (finite P2 h2) := by {
  simp [add, neg_of_add, neg],
}
| (finite P1 h1), infinite := by {
  simp [add, neg_of_add, neg],
}
| (finite P1 h1), (finite P2 h2) := by {
  by_cases hx : P1.x - P2.x = 0, {
    by_cases hy : P1.y + P2.y + E.a1*P1.x + E.a3 = 0, {
      simp [add, neg_of_add, neg, hx, hy],
      replace hx := (sub_eq_zero.1 hx).symm,
      simp [neg_of_affine_plane_point, affine_plane_point.ext_iff, hx],
      rw [← sub_eq_zero, ← hy],
      ring,
    },
    simp [add, neg_of_add, neg, hx, hy],
    replace hx := (sub_eq_zero.1 hx).symm,
    simp [neg_of_affine_plane_point, affine_plane_point.ext_iff, hx],
    revert hy,
    contrapose,
    push_neg,
    intro hy,
    rw hy,
    ring,
  },
  simp [add, neg_of_add, neg, hx],
  simp [neg_of_affine_plane_point, affine_plane_point.ext_iff, (sub_ne_zero.1 hx).symm],
}
end

end affine_point

end weierstrass_equation
