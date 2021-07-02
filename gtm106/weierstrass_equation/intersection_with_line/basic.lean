import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import myhelper.mypoly.basic
import tactic

namespace weierstrass_equation

/--
intersection of `y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6`
and `y = A*x + B`
-/
@[ext]
structure intersection_with_line (K : Type*) [field K] :=
mk :: (E : weierstrass_equation K)
(A B : K)

namespace intersection_with_line

/--
intersection of `y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6`
and `y - y0 = A*(x - x0)`
-/
def from_point {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
: intersection_with_line K
:= ⟨ E, A, P.y - A * P.x ⟩

@[simp]
lemma from_point.E {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
: (from_point E P A).E = E := rfl

@[simp]
lemma from_point.A {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
: (from_point E P A).A = A := rfl

section

parameters {K : Type*} [field K] (L : intersection_with_line K)

def a : K := L.E.a2 - (L.A + L.E.a1) * L.A
def b : K := L.E.a4 - (2 * L.A + L.E.a1) * L.B - L.A * L.E.a3
def c : K := L.E.a6 - (L.B + L.E.a3) * L.B
def poly : monic_cubic_poly K := ⟨ L.a, L.b, L.c ⟩
def point (x : K) : affine_plane_point K := ⟨ x, L.A * x + L.B ⟩

lemma from_point' (x : K)
: from_point L.E (L.point x) L.A = L :=
begin
  simp [from_point, point, intersection_with_line.ext_iff],
end

lemma eval_at' (x : K)
: L.poly.eval_at x = - L.E.eval_at_affine_point (L.point x) :=
sub_eq_zero.1 begin
  simp only [monic_cubic_poly.eval_at, poly, a, b, c, eval_at_affine_point, point],
  ring,
end

lemma eval_dx_at' (x : K)
: L.poly.eval_dx_at x = - L.E.eval_dx_at_affine_point (L.point x) - L.A * L.E.eval_dy_at_affine_point (L.point x) :=
sub_eq_zero.1 begin
  simp only [monic_cubic_poly.eval_dx_at, poly, a, b, c,
    eval_dx_at_affine_point, eval_dy_at_affine_point, point],
  ring,
end

lemma is_on' (x : K)
: L.poly.is_root x ↔ L.E.affine_point_on_curve (L.point x) :=
begin
  simp [monic_cubic_poly.is_root, affine_point_on_curve, eval_at'],
end

lemma is_on_2' (x : K)
: L.poly.is_multiple_root x
↔ L.E.affine_point_on_curve (L.point x)
∧ - L.E.eval_dx_at_affine_point (L.point x) = L.A * L.E.eval_dy_at_affine_point (L.point x) :=
begin
  simp [monic_cubic_poly.is_multiple_root, affine_point_on_curve,
    eval_at', eval_dx_at', sub_eq_zero],
end

end

lemma point_this {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
: (from_point E P A).point P.x = P :=
begin
  simp [from_point, point, affine_plane_point.ext_iff],
end

lemma is_on_this {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
: (from_point E P A).poly.is_root P.x ↔ E.affine_point_on_curve P :=
begin
  rw [is_on', point_this],
  simp [from_point],
end

lemma from_point'' {K : Type*} [field K]
(E : weierstrass_equation K)
(P : affine_plane_point K)
(A x : K)
: from_point E ((from_point E P A).point x) A = from_point E P A :=
begin
  have := from_point' (from_point E P A) x,
  simp at this,
  exact this,
end

end intersection_with_line

end weierstrass_equation
