import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import tactic

namespace weierstrass_equation

-- ================
-- P ↦ -P
-- ================

def neg_of_affine_plane_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
(P : affine_plane_point K) : affine_plane_point K
:= ⟨ P.x, -P.y - E.a1*P.x - E.a3 ⟩

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

def affine_point.neg
{K : Type*} [comm_ring K] {E : weierstrass_equation K}
: affine_point E → affine_point E
| affine_point.infinite := affine_point.infinite
| (affine_point.finite P h) := affine_point.finite (E.neg_of_affine_plane_point P)
  ((affine_point_on_curve.neg E P).2 h)

@[simp]
lemma affine_point.neg_of_neg
{K : Type*} [comm_ring K] {E : weierstrass_equation K}
(P : affine_point E) : P.neg.neg = P :=
match P with
| affine_point.infinite := by {
  simp [affine_point.neg],
}
| (affine_point.finite P h) := by {
  simp [affine_point.neg],
}
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

-- ================
-- P ↦ -2*P
-- ================

/--
NOTE: P should not be a 2-torsion, otherwise the result is incorrect
-/
def neg_of_double_of_affine_plane_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) : affine_plane_point K :=
let A := 3*P.x^2 + 2*E.a2*P.x + E.a4 - E.a1*P.y,
  B := -P.x^3 + E.a4*P.x + 2*E.a6 - E.a3*P.y,
  C := 2*P.y + E.a1*P.x + E.a3,
  x' := (A/C)^2 + E.a1*(A/C) - E.a2 - 2*P.x,
  y' := (A/C)*x' + (B/C) in ⟨ x', y' ⟩

/-
sorry = -2*a1^4*a2*x^3 - a1^4*x^4 + 2*a1^5*x^2*y - 2*a1^3*a2*a3*x^2 -
2*a1^4*a4*x^2 - 16*a1^2*a2^2*x^3 + 2*a1^3*a3*x^3 - 40*a1^2*a2*x^4 -
22*a1^2*x^5 + 4*a1^4*a3*x*y + 16*a1^3*a2*x^2*y + 32*a1^3*x^3*y +
2*a1^4*x*y^2 + 2*a1^2*a2*a3^2*x - 4*a1^3*a3*a4*x - 8*a1*a2^2*a3*x^2 +
6*a1^2*a3^2*x^2 - 20*a1^2*a2*a4*x^2 - 32*a2^3*x^3 - 8*a1*a2*a3*x^3 -
28*a1^2*a4*x^3 - 144*a2^2*x^4 + 10*a1*a3*x^4 - 216*a2*x^5 - 108*x^6 +
2*a1^3*a3^2*y + 24*a1^2*a2*a3*x*y + 4*a1^3*a4*x*y + 32*a1*a2^2*x^2*y +
48*a1^2*a3*x^2*y + 128*a1*a2*x^3*y + 128*a1*x^4*y + 2*a1^3*a3*y^2 +
16*a1^2*a2*x*y^2 + 32*a1^2*x^2*y^2 + 2*a1*a2*a3^3 - 2*a1^2*a3^2*a4 +
8*a2^2*a3^2*x + 2*a1*a3^3*x - 16*a1*a2*a3*a4*x - 6*a1^2*a4^2*x +
32*a2*a3^2*x^2 - 48*a2^2*a4*x^2 - 20*a1*a3*a4*x^2 - 4*a1^2*a6*x^2 +
32*a3^2*x^3 - 144*a2*a4*x^3 - 108*a4*x^4 + 8*a1*a2*a3^2*y +
4*a1^2*a3*a4*y + 32*a2^2*a3*x*y + 12*a1*a3^2*x*y + 16*a1*a2*a4*x*y +
128*a2*a3*x^2*y + 32*a1*a4*x^2*y + 128*a3*x^3*y + 8*a1*a2*a3*y^2 +
4*a1^2*a4*y^2 + 32*a2^2*x*y^2 + 16*a1*a3*x*y^2 + 128*a2*x^2*y^2 +
128*x^3*y^2 - a3^4 + 4*a2*a3^2*a4 - 6*a1*a3*a4^2 + 8*a3^2*a4*x -
24*a2*a4^2*x - 8*a1*a3*a6*x - 36*a4^2*x^2 - 4*a3^3*y + 16*a2*a3*a4*y +
32*a3*a4*x*y - 16*a1*a6*x*y - 4*a3^2*y^2 + 16*a2*a4*y^2 + 32*a4*x*y^2 -
4*a4^3 - 4*a3^2*a6 - 16*a3*a6*y - 16*a6*y^2
-/

lemma eval_at_affine_point.neg_of_double
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (hy : 2*P.y + E.a1*P.x + E.a3 ≠ 0)
: E.eval_at_affine_point (E.neg_of_double_of_affine_plane_point P)
= (E.eval_at_affine_point P) * sorry
/ (2*P.y + E.a1*P.x + E.a3)^4
:=
begin
  sorry,
end

lemma affine_point_on_curve.neg_of_double
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
(hy : 2*P.y + E.a1*P.x + E.a3 ≠ 0)
: E.affine_point_on_curve (E.neg_of_double_of_affine_plane_point P) :=
begin
  simp [affine_point_on_curve] at h ⊢,
  rw [eval_at_affine_point.neg_of_double E P hy, h, zero_mul, zero_div],
end

-- ================
-- (P1, P2) ↦ -(P1 + P2)
-- ================

/--
NOTE: P1.x and P2.x should be different, otherwise the result is incorrect
-/
def neg_of_add_of_affine_plane_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K) : affine_plane_point K :=
let A := P1.y - P2.y,
  B := P2.y*P1.x - P1.y*P2.x,
  C := P1.x - P2.x,
  x' := (A/C)^2 + E.a1*(A/C) - E.a2 - P1.x - P2.x,
  y' := (A/C)*x' + (B/C) in ⟨ x', y' ⟩

lemma neg_of_add_of_affine_plane_point.comm
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
: E.neg_of_add_of_affine_plane_point P1 P2 = E.neg_of_add_of_affine_plane_point P2 P1 :=
begin
  simp only [neg_of_add_of_affine_plane_point, affine_plane_point.ext_iff],
  have h1 : (P1.y - P2.y) / (P1.x - P2.x) = (P2.y - P1.y) / (P2.x - P1.x) := by {
    by_cases hx : P1.x - P2.x = 0, {
      simp [sub_eq_zero.1 hx],
    },
    have hx' := sub_ne_zero.2 (sub_ne_zero.1 hx).symm,
    field_simp [hx, hx'],
    ring,
  },
  have h2 : (P2.y*P1.x - P1.y*P2.x) / (P1.x - P2.x) = (P1.y*P2.x - P2.y*P1.x) / (P2.x - P1.x) := by {
    by_cases hx : P1.x - P2.x = 0, {
      simp [sub_eq_zero.1 hx],
    },
    have hx' := sub_ne_zero.2 (sub_ne_zero.1 hx).symm,
    field_simp [hx, hx'],
    ring,
  },
  rw [h1, h2, sub_sub _ P1.x P2.x, sub_sub _ P2.x P1.x, add_comm P1.x P2.x],
  split; refl,
end

lemma affine_point_on_curve.neg_of_add
{K : Type*} [field K] (E : weierstrass_equation K)
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x ≠ 0)
: E.affine_point_on_curve (E.neg_of_add_of_affine_plane_point P1 P2) :=
begin
  sorry,
end

noncomputable def affine_point.neg_of_add
{K : Type*} [field K] {E : weierstrass_equation K}
: affine_point E → affine_point E → affine_point E
| affine_point.infinite P := P.neg
| P affine_point.infinite := P.neg
| (affine_point.finite P1 h1) (affine_point.finite P2 h2) := by {
  by_cases hx : P1.x - P2.x = 0, {
    by_cases hy : P1.y + P2.y + E.a1*P1.x + E.a3 = 0, {
      exact affine_point.infinite,
    },
    exact affine_point.finite (E.neg_of_double_of_affine_plane_point P1)
      (affine_point_on_curve.neg_of_double E P1 h1 (by {
        have h := same_x_implies_same_or_neg P1 P2 h1 h2 hx,
        simp [hy, sub_eq_zero] at h,
        rw [← h, ← two_mul] at hy,
        exact hy,
      })),
  },
  exact affine_point.finite (E.neg_of_add_of_affine_plane_point P1 P2)
    (affine_point_on_curve.neg_of_add E P1 P2 h1 h2 hx),
}

lemma affine_point.neg_of_add.comm
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.neg_of_add P2 = P2.neg_of_add P1 :=
match P1, P2 with
| affine_point.infinite, affine_point.infinite := by {
  simp [affine_point.neg_of_add],
}
| affine_point.infinite, (affine_point.finite P2 h2) := by {
  simp [affine_point.neg_of_add],
}
| (affine_point.finite P1 h1), affine_point.infinite := by {
  simp [affine_point.neg_of_add],
}
| (affine_point.finite P1 h1), (affine_point.finite P2 h2) := by {
  simp [affine_point.neg_of_add],
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
  exact neg_of_add_of_affine_plane_point.comm E P1 P2,
}
end

-- ================
-- (P1, P2) ↦ P1 + P2
-- ================

noncomputable def affine_point.add
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E) : affine_point E
:= (P1.neg_of_add P2).neg

lemma affine_point.add.comm
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.add P2 = P2.add P1 :=
begin
  unfold affine_point.add,
  congr' 1,
  exact affine_point.neg_of_add.comm P1 P2,
end

lemma affine_point.add.zero_add
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: affine_point.infinite.add P = P :=
match P with
| affine_point.infinite := by {
  simp [affine_point.add, affine_point.neg_of_add],
}
| (affine_point.finite P h) := by {
  simp [affine_point.add, affine_point.neg_of_add],
}
end

lemma affine_point.add.add_zero
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: P.add affine_point.infinite = P :=
match P with
| affine_point.infinite := by {
  simp [affine_point.add, affine_point.neg_of_add],
}
| (affine_point.finite P h) := by {
  simp [affine_point.add, affine_point.neg_of_add],
}
end

lemma affine_point.add.add_left_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: P.neg.add P = affine_point.infinite :=
match P with
| affine_point.infinite := by {
  simp [affine_point.add, affine_point.neg_of_add, affine_point.neg],
}
| (affine_point.finite P h) := by {
  simp [affine_point.add, affine_point.neg_of_add, affine_point.neg,
    neg_of_affine_plane_point],
  dsimp only,
  have h : -P.y - E.a1 * P.x - E.a3 + P.y + E.a1 * P.x + E.a3 = 0 := by ring,
  simp [h, affine_point.neg],
}
end

lemma affine_point.add.add_right_neg
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E)
: P.add P.neg = affine_point.infinite :=
match P with
| affine_point.infinite := by {
  simp [affine_point.add, affine_point.neg_of_add, affine_point.neg],
}
| (affine_point.finite P h) := by {
  simp [affine_point.add, affine_point.neg_of_add, affine_point.neg,
    neg_of_affine_plane_point],
  dsimp only,
  have h : P.y + (-P.y - E.a1 * P.x - E.a3) + E.a1 * P.x + E.a3 = 0 := by ring,
  simp [h, affine_point.neg],
}
end

lemma affine_point.add.assoc
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 P3 : affine_point E)
: (P1.add P2).add P3 = P1.add (P2.add P3) :=
begin
  unfold affine_point.add,
  congr' 1,
  sorry,
end

noncomputable instance affine_point.to_add_comm_group
{K : Type*} [field K] (E : weierstrass_equation K)
: add_comm_group (affine_point E)
:= ⟨ affine_point.add, affine_point.add.assoc, affine_point.infinite,
  affine_point.add.zero_add, affine_point.add.add_zero, affine_point.neg,
  (λ P1 P2, P1.add P2.neg), by {
    intros _ _, simp [has_add.add, add_zero_class.add],
  }, affine_point.add.add_left_neg, affine_point.add.comm ⟩

end weierstrass_equation
