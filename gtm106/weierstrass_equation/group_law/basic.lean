import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.intersection_with_line
import myhelper.mypoly.basic
import tactic

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

def iwl : intersection_with_line K := intersection_with_line.from_point E P (A/C)

@[simp]
lemma iwl_E
: iwl.E = E := rfl

lemma A1 : A = - E.eval_dx_at_affine_point P :=
sub_eq_zero.1 begin
  simp only [A, eval_dx_at_affine_point],
  ring,
end

lemma C1 : C = E.eval_dy_at_affine_point P :=
begin
  simp only [C, eval_dy_at_affine_point],
end

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

lemma iwl_x0 (h : E.affine_point_on_curve P) (hC : C ≠ 0)
: iwl.poly.is_multiple_root P.x :=
begin
  unfold iwl,
  rw [intersection_with_line.is_on_2', intersection_with_line.point_this],
  simp [h, A1, ← C1, hC],
end

lemma iwl_x'
: x = - iwl.poly.a - 2 * P.x :=
begin
  simp only [iwl, intersection_with_line.from_point,
    intersection_with_line.poly,
    intersection_with_line.a, x],
  ring,
end

lemma iwl_x1 (h : E.affine_point_on_curve P) (hC : C ≠ 0)
: iwl.poly.is_root x :=
begin
  rw iwl_x',
  exact (iwl E P).poly.vieta_2 _ (iwl_x0 E P h hC),
end

lemma iwl_p
: iwl.point x = ⟨ x, y ⟩ :=
begin
  simp [iwl, intersection_with_line.from_point,
    intersection_with_line.point, y],
  ring,
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
  change neg_of_double_of_affine_plane_point.C E P ≠ 0 at hy,
  unfold neg_of_double_of_affine_plane_point,
  rw [← neg_of_double_of_affine_plane_point.iwl_p],
  have h1 := intersection_with_line.is_on'
    (neg_of_double_of_affine_plane_point.iwl E P)
    (neg_of_double_of_affine_plane_point.x E P),
  simp at h1,
  rw ← h1,
  exact neg_of_double_of_affine_plane_point.iwl_x1 E P h hy,
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

def iwl : intersection_with_line K := intersection_with_line.from_point E P1 (A/C)

@[simp]
lemma iwl_E
: iwl.E = E := rfl

lemma iwl_p1
: iwl.point P1.x = P1 :=
begin
  unfold iwl,
  exact intersection_with_line.point_this E P1 _,
end

lemma iwl_p2
(hx : P1.x - P2.x ≠ 0)
: iwl.point P2.x = P2 :=
begin
  simp [iwl, intersection_with_line.from_point,
    intersection_with_line.point,
    affine_plane_point.ext_iff, A, C],
  field_simp [hx],
  ring,
end

lemma iwl_p3
(hx : P1.x - P2.x ≠ 0)
: iwl.point x = ⟨ x, y ⟩ :=
begin
  simp [iwl, intersection_with_line.from_point,
    intersection_with_line.point, y, A, C],
  field_simp [hx],
  ring,
end

lemma iwl_x1 (h : E.affine_point_on_curve P1)
: iwl.poly.is_root P1.x :=
begin
  rw [intersection_with_line.is_on', iwl_p1],
  exact h,
end

lemma iwl_x2 (h : E.affine_point_on_curve P2)
(hx : P1.x - P2.x ≠ 0)
: iwl.poly.is_root P2.x :=
begin
  rw [intersection_with_line.is_on', iwl_p2 E P1 P2 hx],
  exact h,
end

lemma iwl_x'
: x = - iwl.poly.a - P1.x - P2.x :=
begin
  simp [iwl, intersection_with_line.poly, intersection_with_line.a,
    intersection_with_line.from_point, x],
end

lemma iwl_x3 (h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x ≠ 0)
: iwl.poly.is_root x :=
begin
  rw iwl_x',
  exact (iwl E P1 P2).poly.vieta P1.x P2.x (iwl_x1 E P1 P2 h1)
    (iwl_x2 E P1 P2 h2 hx) (sub_ne_zero.1 hx),
end

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
  unfold neg_of_add_of_affine_plane_point,
  rw [← neg_of_add_of_affine_plane_point.iwl_p3 E P1 P2 hx],
  have h := intersection_with_line.is_on'
    (neg_of_add_of_affine_plane_point.iwl E P1 P2)
    (neg_of_add_of_affine_plane_point.x E P1 P2),
  simp at h,
  rw ← h,
  exact neg_of_add_of_affine_plane_point.iwl_x3 E P1 P2 h1 h2 hx,
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

@[simp]
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

@[simp]
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

@[simp]
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

@[simp]
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
