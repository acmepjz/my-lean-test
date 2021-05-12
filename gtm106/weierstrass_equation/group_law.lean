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

namespace intersection_with_line

section

-- intersection of `y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6`
-- and `y = A*x + B`
parameters {K : Type*} [field K] (E : weierstrass_equation K)
(A B : K)

def a : K := E.a2 - A^2 - A*E.a1
def b : K := E.a4 - 2*A*B - B*E.a1 - A*E.a3
def c : K := E.a6 - B^2 - B*E.a3
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
def B : K := -P.x^3 + E.a4*P.x + 2*E.a6 - E.a3*P.y
def C : K := 2*P.y + E.a1*P.x + E.a3
def x : K := (A/C)^2 + E.a1*(A/C) - E.a2 - 2*P.x
def y : K := (A/C)*x + (B/C)

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

lemma affine_point_on_curve.neg_of_double
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
(hy : 2*P.y + E.a1*P.x + E.a3 ≠ 0)
: E.affine_point_on_curve (E.neg_of_double_of_affine_plane_point P) :=
begin
  set! A := (neg_of_double_of_affine_plane_point.A E P)/(neg_of_double_of_affine_plane_point.C E P) with hA, clear_value A,
  set! B := (neg_of_double_of_affine_plane_point.B E P)/(neg_of_double_of_affine_plane_point.C E P) with hB, clear_value B,
  have hC : neg_of_double_of_affine_plane_point.C E P = 2*P.y + E.a1*P.x + E.a3 := rfl,
  have h1 : intersection_with_line.is_on E A B P.x := by {
    rw intersection_with_line.is_on_iff_is_on E A B P.x,
    have h5 : A * P.x + B = P.y := by {
      simp only [hA, hB, neg_of_double_of_affine_plane_point.A,
        neg_of_double_of_affine_plane_point.B, neg_of_double_of_affine_plane_point.C],
      field_simp [hy],
      rw ← sub_eq_zero,
      simp only [affine_point_on_curve] at h,
      transitivity -2*E.eval_at_affine_point P,
      {
        simp [eval_at_affine_point],
        ring,
      },
      simp [h],
    },
    rw h5,
    exact h,
  },
  have h2 : intersection_with_line.is_on_2 E A B P.x := by {
    simp only [intersection_with_line.is_on_2,
      intersection_with_line.a, intersection_with_line.b,
      hA, hB],
    rw ← hC at hy,
    field_simp [pow_succ, hy],
    transitivity neg_of_double_of_affine_plane_point.C E P ^ 5 * (P.x * neg_of_double_of_affine_plane_point.A E P ^ 2 * -2
      + P.x * neg_of_double_of_affine_plane_point.C E P * neg_of_double_of_affine_plane_point.A E P * E.a1 * -2
      + P.x * neg_of_double_of_affine_plane_point.C E P ^ 2 * E.a2 * 2
      + P.x ^ 2 * neg_of_double_of_affine_plane_point.C E P ^ 2 * 3
      + neg_of_double_of_affine_plane_point.A E P * neg_of_double_of_affine_plane_point.B E P * -2
      + neg_of_double_of_affine_plane_point.C E P * neg_of_double_of_affine_plane_point.A E P * -E.a3
      + neg_of_double_of_affine_plane_point.C E P * E.a1 * -neg_of_double_of_affine_plane_point.B E P
      + neg_of_double_of_affine_plane_point.C E P ^ 2 * E.a4),
    { rw ← sub_eq_zero, ring, },
    simp [hy],
    transitivity (2*E.a1^2*P.x + 2*E.a1*E.a3 + 8*E.a2*P.x + 12*P.x^2 + 4*E.a4) * E.eval_at_affine_point P,
    {
      simp only [neg_of_double_of_affine_plane_point.A,
        neg_of_double_of_affine_plane_point.B, neg_of_double_of_affine_plane_point.C,
        eval_at_affine_point],
      rw ← sub_eq_zero, ring,
    },
    simp [affine_point_on_curve] at h,
    simp [h],
  },
  have h3 := Vieta_formula_cubic_2 h1 h2,
  have h4 : -intersection_with_line.a E A - 2 * P.x = (E.neg_of_double_of_affine_plane_point P).x := by {
    simp [hA, neg_of_double_of_affine_plane_point,
      neg_of_double_of_affine_plane_point.x,
      intersection_with_line.a],
    ring,
  },
  rw h4 at h3,
  change intersection_with_line.is_on E A B (E.neg_of_double_of_affine_plane_point P).x at h3,
  rw intersection_with_line.is_on_iff_is_on at h3,
  have h5 : A * (E.neg_of_double_of_affine_plane_point P).x + B = (E.neg_of_double_of_affine_plane_point P).y := by {
    rw [hA, hB],
    refl,
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
def B : K := P2.y*P1.x - P1.y*P2.x
def C : K := P1.x - P2.x
def x : K := (A/C)^2 + E.a1*(A/C) - E.a2 - P1.x - P2.x
def y : K := (A/C)*x + (B/C)

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
  unfold neg_of_add_of_affine_plane_point.y neg_of_add_of_affine_plane_point.x
    neg_of_add_of_affine_plane_point.C neg_of_add_of_affine_plane_point.B
    neg_of_add_of_affine_plane_point.A,
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
  have hx' := sub_ne_zero.2 (sub_ne_zero.1 hx).symm,
  set! A := (neg_of_add_of_affine_plane_point.A P1 P2)/(neg_of_add_of_affine_plane_point.C P1 P2) with hA, clear_value A,
  set! B := (neg_of_add_of_affine_plane_point.B P1 P2)/(neg_of_add_of_affine_plane_point.C P1 P2) with hB, clear_value B,
  replace h1 : intersection_with_line.is_on E A B P1.x := by {
    rw intersection_with_line.is_on_iff_is_on E A B P1.x,
    have h5 : A * P1.x + B = P1.y := by {
      simp only [hA, hB, neg_of_add_of_affine_plane_point.A,
        neg_of_add_of_affine_plane_point.B, neg_of_add_of_affine_plane_point.C],
      field_simp [hx, hx'],
      ring,
    },
    rw h5,
    exact h1,
  },
  replace h2 : intersection_with_line.is_on E A B P2.x := by {
    rw intersection_with_line.is_on_iff_is_on E A B P2.x,
    have h5 : A * P2.x + B = P2.y := by {
      simp only [hA, hB, neg_of_add_of_affine_plane_point.A,
        neg_of_add_of_affine_plane_point.B, neg_of_add_of_affine_plane_point.C],
      field_simp [hx, hx'],
      ring,
    },
    rw h5,
    exact h2,
  },
  have h3 := Vieta_formula_cubic h1 h2 (sub_ne_zero.1 hx),
  have h4 : -intersection_with_line.a E A - P1.x - P2.x = (E.neg_of_add_of_affine_plane_point P1 P2).x := by {
    simp [hA, neg_of_add_of_affine_plane_point,
      neg_of_add_of_affine_plane_point.x,
      intersection_with_line.a],
    ring,
  },
  rw h4 at h3,
  change intersection_with_line.is_on E A B (E.neg_of_add_of_affine_plane_point P1 P2).x at h3,
  rw intersection_with_line.is_on_iff_is_on at h3,
  have h5 : A * (E.neg_of_add_of_affine_plane_point P1 P2).x + B = (E.neg_of_add_of_affine_plane_point P1 P2).y := by {
    rw [hA, hB],
    refl,
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
  exact neg_of_add_of_affine_plane_point.comm E P1 P2,
}
end

-- ================
-- (P1, P2) ↦ P1 + P2
-- ================

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

lemma add.assoc
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 P3 : affine_point E)
: (P1.add P2).add P3 = P1.add (P2.add P3) :=
begin
  unfold add,
  congr' 1,
  sorry,
end

noncomputable instance to_add_comm_group
{K : Type*} [field K] (E : weierstrass_equation K)
: add_comm_group (affine_point E)
:= ⟨ add, add.assoc, infinite,
  add.zero_add, add.add_zero, neg,
  (λ P1 P2, P1.add P2.neg), by {
    intros _ _, simp only [has_add.add, add_zero_class.add],
  }, add.add_left_neg, add.comm ⟩

end affine_point

end weierstrass_equation
