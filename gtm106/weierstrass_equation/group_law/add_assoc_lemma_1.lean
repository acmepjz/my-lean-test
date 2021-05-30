import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.group_law.basic
import tactic

namespace weierstrass_equation

namespace affine_point

-- copied from [Fri17] An elementary proof of the group law for elliptic curves

lemma add.assoc.lemma_2_1
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 P3 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(h3 : E.affine_point_on_curve P3)
(hx12 : P1.x - P2.x ≠ 0)
(hx23 : P2.x - P3.x ≠ 0)
(hx123 : (E.add_of_affine_plane_point P1 P2).x - P3.x ≠ 0)
(hx231 : (E.add_of_affine_plane_point P2 P3).x - P1.x ≠ 0)
: E.add_of_affine_plane_point (E.add_of_affine_plane_point P1 P2) P3
= E.add_of_affine_plane_point P1 (E.add_of_affine_plane_point P2 P3) :=
begin
  sorry,
end

lemma add.assoc.lemma_2_2
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(h1not2tors : neg_of_double_of_affine_plane_point.C E P1 ≠ 0)
(hx12 : P1.x - P2.x ≠ 0)
(hx112 : (E.double_of_affine_plane_point P1).x - P2.x ≠ 0)
(hx121 : (E.add_of_affine_plane_point P1 P2).x - P1.x ≠ 0)
: E.add_of_affine_plane_point (E.double_of_affine_plane_point P1) P2
= E.add_of_affine_plane_point P1 (E.add_of_affine_plane_point P1 P2) :=
begin
  sorry,
end

lemma add.assoc.lemma_2_3
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_plane_point K)
(h : E.affine_point_on_curve P)
(hnot2tors : neg_of_double_of_affine_plane_point.C E P ≠ 0)
(h2not2tors : neg_of_double_of_affine_plane_point.C E (E.double_of_affine_plane_point P) ≠ 0)
(hx31 : (E.add_of_affine_plane_point (E.double_of_affine_plane_point P) P).x - P.x ≠ 0)
(hx21 : (E.double_of_affine_plane_point P).x - P.x ≠ 0)
: (E.double_of_affine_plane_point (E.double_of_affine_plane_point P))
= E.add_of_affine_plane_point P (E.add_of_affine_plane_point P (E.double_of_affine_plane_point P)) :=
begin
  sorry,
end

end affine_point

end weierstrass_equation
