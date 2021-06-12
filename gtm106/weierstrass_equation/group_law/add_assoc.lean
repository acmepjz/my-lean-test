import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.group_law.basic
import tactic

namespace weierstrass_equation

namespace affine_point

-- copied from [Fri17] An elementary proof of the group law for elliptic curves

-- WRONG !!!
lemma add.assoc.lemma_2_5
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.add P2 = P1.add P2.neg → P1 ≠ P1.neg → P2 = P2.neg :=
match P1, P2 with
| infinite, infinite := by {
  simp [neg],
}
| infinite, (finite P2 h2) := by {
  simp [neg],
}
| (finite P1 h1), infinite := by {
  simp [neg],
}
| (finite P1 h1), (finite P2 h2) := by {
  intros hh1 hh2,
  by_cases hx : P1.x - P2.x = 0, {
    exfalso,
    cases same_x_implies_same_or_neg' P1 P2 h1 h2 hx with hP hP, {
      replace hP : finite P1 h1 = finite P2 h2 := by {
        simp only [hP],
      },
      rw [← hP, add.add_right_neg, add.add_to_zero_iff_neg] at hh1,
      exact hh2 hh1,
    },
    replace hP : finite P1 h1 = (finite P2 h2).neg := by {
      simp only [neg, hP],
    },
    replace hh1 := hh1.symm,
    rw [hP, add.add_left_neg, add.add_to_zero_iff_neg, ← hP] at hh1,
    exact hh2 hh1,
  },
  simp [neg, neg_of_affine_plane_point.self_eq_neg_iff] at hh2,
  simp [add, neg_of_add, neg, hx, neg_of_affine_plane_point,
    neg_of_add_of_affine_plane_point] at hh1,
  replace hh1 := sub_eq_zero.2 hh1.1.symm,
  simp only [neg_of_add_of_affine_plane_point.x,
    neg_of_add_of_affine_plane_point.A,
    neg_of_add_of_affine_plane_point.C] at hh1,
  field_simp [hx] at hh1,
  replace hh1 : (2*P1.y + E.a1*P1.x + E.a3) * (2*P2.y + E.a1*P2.x + E.a3) * (P1.x - P2.x)^2 = 0 := by {
    rw [← hh1, ← sub_eq_zero],
    ring,
  },
  simp [hx, hh2] at hh1,
  simp [neg],
  exact (neg_of_affine_plane_point.self_eq_neg_iff E P2).2 hh1,
}
end

lemma add.a_add_b_eq_a_iff
{K : Type*} [field K] {E : weierstrass_equation K}
(hns : E.non_singular')
(P1 P2 : affine_point E)
: P1.add P2 = P1 ↔ P2 = infinite :=
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
  simp only [iff_false],
  intro h0,
  have h := h0,
  by_cases hx : P1.x - P2.x = 0, {
    by_cases hy : P1.y + P2.y + E.a1*P1.x + E.a3 = 0, {
      simp [add, neg_of_add, hx, hy] at h,
      simp only [neg] at h,
      exact h,
    },
    simp [add, neg_of_add, hx, hy, neg,
      neg_of_double_of_affine_plane_point, affine_plane_point.ext_iff,
      neg_of_affine_plane_point] at h,
    cases h with h h',
    simp [h, neg_of_double_of_affine_plane_point.y] at h',
    have hP := same_x_implies_same_or_neg P1 P2 h1 h2 hx,
    simp [hy] at hP,
    have hy' : P1.y + P2.y + E.a1*P1.x + E.a3 = 0 := by {
      rw [← h', ← sub_eq_zero.1 hP],
      ring,
    },
    exact hy hy',
  },
  simp [add, neg_of_add, hx, neg,
    neg_of_add_of_affine_plane_point, affine_plane_point.ext_iff,
    neg_of_affine_plane_point] at h,
  cases h with h h',
  simp [h, neg_of_add_of_affine_plane_point.y] at h',
  replace h' : 2*P1.y + E.a1*P1.x + E.a3 = 0 := by {
    rw [← sub_eq_zero.2 h'.symm],
    ring,
  },
  replace h' : finite P1 h1 = (finite P1 h1).neg := by {
    simp only [neg],
    exact (neg_of_affine_plane_point.self_eq_neg_iff E P1).2 h',
  },
  have := add.assoc.lemma_2_5 (finite P1 h1) (finite P2 h2) (by {
    sorry,
  }) (by sorry),
  sorry,
}
end

lemma add.assoc
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 P3 : affine_point E)
: (P1.add P2).add P3 = P1.add (P2.add P3) :=
begin
  sorry,
end

lemma add.assoc.lemma_2_5'
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_point E)
: P1.add P2 = P1.add P2.neg → (P1 = P1.neg → P1.regular) → P2 = P2.neg :=
match P1, P2 with
| infinite, infinite := by {
  intros _ _,
  simp [neg],
}
| infinite, (finite P2 h2) := by {
  simp [neg, regular],
}
| (finite P1 h1), infinite := by {
  intros _ _,
  simp [neg],
}
| (finite P1 h1), (finite P2 h2) := by {
  intros hh1 hhreg,
  by_cases hx : P1.x - P2.x = 0, {
    cases same_x_implies_same_or_neg' P1 P2 h1 h2 hx with hP hP, {
      replace hP : finite P1 h1 = finite P2 h2 := by {
        simp only [hP],
      },
      rw [← hP, add.add_right_neg, add.add_to_zero_iff_neg, hP] at hh1,
      exact hh1,
    },
    replace hP : finite P1 h1 = (finite P2 h2).neg := by {
      simp only [neg, hP],
    },
    replace hh1 := hh1.symm,
    rw [hP, add.add_left_neg, add.add_to_zero_iff_neg, neg_of_neg] at hh1,
    exact hh1.symm,
  },
  simp [add, neg_of_add, neg, hx, neg_of_affine_plane_point,
    neg_of_add_of_affine_plane_point] at hh1,
  cases hh1 with hh1 hh1',
  simp only [← hh1, neg_of_add_of_affine_plane_point.y,
    neg_of_add_of_affine_plane_point.A,
    neg_of_add_of_affine_plane_point.C] at hh1',
  rw ← sub_eq_zero at hh1',
  field_simp [hx] at hh1',
  replace hh1' : (neg_of_add_of_affine_plane_point.x E P1 P2 - P1.x) * (2*P2.y + E.a1*P2.x + E.a3) * (P1.x - P2.x) = 0 := by {
    rw [← hh1', ← sub_eq_zero],
    ring,
  },
  replace hh1 := sub_eq_zero.2 hh1.symm,
  simp only [neg_of_add_of_affine_plane_point.x,
    neg_of_add_of_affine_plane_point.A,
    neg_of_add_of_affine_plane_point.C] at hh1,
  field_simp [hx] at hh1,
  replace hh1 : (2*P1.y + E.a1*P1.x + E.a3) * (2*P2.y + E.a1*P2.x + E.a3) * (P1.x - P2.x)^2 = 0 := by {
    rw [← hh1, ← sub_eq_zero],
    ring,
  },
  simp only [neg, neg_of_affine_plane_point.self_eq_neg_iff],
  by_cases hh2 : 2*P1.y + E.a1*P1.x + E.a3 = 0, swap, {
    simp [hx, hh2] at hh1,
    exact hh1,
  },
  by_cases hh3 : neg_of_add_of_affine_plane_point.x E P1 P2 - P1.x = 0, swap, {
    simp [hx, hh3] at hh1',
    exact hh1',
  },
  exfalso,
  replace hhreg := hhreg (by {
    simp only [neg, neg_of_affine_plane_point.self_eq_neg_iff],
    exact hh2,
  }),
  simp [regular, affine_point_regular, h1,
    eval_dx_at_affine_point,
    eval_dy_at_affine_point, hh2] at hhreg,
  sorry,
}
end

lemma add.x_of_a_add_b_eq_x_of_a_iff
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x ≠ 0)
(hk : (P1.x - P2.x) * E.eval_dy_at_affine_point P1 + (P1.y - P2.y) * E.eval_dx_at_affine_point P1 = 0)
: (E.neg_of_add_of_affine_plane_point P1 P2).x = P1.x :=
sub_eq_zero.1 begin
  simp only [neg_of_add_of_affine_plane_point,
    neg_of_add_of_affine_plane_point.y,
    neg_of_add_of_affine_plane_point.x,
    neg_of_add_of_affine_plane_point.A,
    neg_of_add_of_affine_plane_point.C],
  simp only [eval_dx_at_affine_point, eval_dy_at_affine_point] at hk,
  field_simp [hx],
  ring_exp,
  ring_exp at hk,
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

namespace intersection_with_line

lemma disc_zero_iff {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
: monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0
↔ neg_of_double_of_affine_plane_point.C E P = A * neg_of_double_of_affine_plane_point.A E P :=
begin
  sorry,
  simp only [neg_of_double_of_affine_plane_point.A,
    neg_of_double_of_affine_plane_point.C,
    monic_cubic_poly.disc, a, b, c, B],
  split,
  { sorry, },
  sorry,
end

end intersection_with_line

end weierstrass_equation
