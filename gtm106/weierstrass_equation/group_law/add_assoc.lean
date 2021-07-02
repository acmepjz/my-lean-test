import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.non_singular_criterion
import gtm106.weierstrass_equation.linear_change_of_variable
import gtm106.weierstrass_equation.group_law.basic
import gtm106.weierstrass_equation.group_law.linear_change_of_variable
import tactic

namespace weierstrass_equation

namespace affine_point

-- copied from [Fri17] An elementary proof of the group law for elliptic curves

lemma add.x_of_a_add_b_eq_x_of_a_iff
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 : affine_plane_point K)
(h1 : E.affine_point_on_curve P1)
(h2 : E.affine_point_on_curve P2)
(hx : P1.x - P2.x ≠ 0)
: P1.x = neg_of_add_of_affine_plane_point.x E P1 P2
↔ (P1.x - P2.x) * E.eval_dx_at_affine_point P1 + (P1.y - P2.y) * E.eval_dy_at_affine_point P1 = 0 :=
begin
  simp [neg_of_add_of_affine_plane_point.iwl_x'],
  rw (neg_of_add_of_affine_plane_point.iwl E P1 P2).poly.is_multiple_root'
    P1.x P2.x (neg_of_add_of_affine_plane_point.iwl_x1 E P1 P2 h1)
    (neg_of_add_of_affine_plane_point.iwl_x2 E P1 P2 h2 hx) (sub_ne_zero.1 hx),
  rw intersection_with_line.is_on_2',
  simp [neg_of_add_of_affine_plane_point.iwl,
    intersection_with_line.point_this, h1],
  simp [neg_of_add_of_affine_plane_point.A, neg_of_add_of_affine_plane_point.C],
  field_simp [hx],
  split, {
    intro hk,
    rw [← hk],
    ring,
  },
  intro hk,
  transitivity - E.eval_dx_at_affine_point P1 * (P1.x - P2.x) + 0, {
    rw ← sub_eq_zero, ring,
  },
  rw [← hk, ← sub_eq_zero],
  ring,
end

-- Lemma 2.5 (modified)
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
  replace hh3 := (sub_eq_zero.1 hh3).symm,
  rw add.x_of_a_add_b_eq_x_of_a_iff P1 P2 h1 h2 hx at hh3,
  replace hhreg := hhreg (by {
    simp only [neg, neg_of_affine_plane_point.self_eq_neg_iff],
    exact hh2,
  }),
  change E.eval_dy_at_affine_point P1 = 0 at hh2,
  simp [regular, affine_point_regular, h1, hh2] at hhreg,
  simp [hh2, hx, hhreg] at hh3,
  exact hh3,
}
end

-- Lemma 2.6 (modified)
lemma add.a_add_b_eq_a_iff
{K : Type*} [field K] {E : weierstrass_equation K}
(hns : E.non_singular')
(P1 P2 : affine_point E)
: (P1 = P1.neg → P1.regular) → (P1.add P2 = P1 ↔ P2 = infinite) :=
match P1, P2 with
| infinite, infinite := by {
  intro _,
  simp [add, neg_of_add, neg],
}
| infinite, (finite P2 h2) := by {
  intro _,
  simp [add, neg_of_add, neg],
}
| (finite P1 h1), infinite := by {
  intro _,
  simp [add, neg_of_add, neg],
}
| (finite P1 h1), (finite P2 h2) := by {
  intro hreg,
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
  have h'' : E.eval_dy_at_affine_point P1 = 0 := h',
  replace h' : finite P1 h1 = (finite P1 h1).neg := by {
    simp only [neg],
    exact (neg_of_affine_plane_point.self_eq_neg_iff E P1).2 h',
  },
  replace hreg := hreg h',
  replace h := h.symm,
  rw add.x_of_a_add_b_eq_x_of_a_iff P1 P2 h1 h2 hx at h,
  simp [regular, affine_point_regular, h1, h''] at hreg,
  simp [h'', hx, hreg] at h,
  exact h,
}
end

lemma add.assoc
{K : Type*} [field K] {E : weierstrass_equation K}
(P1 P2 P3 : affine_point E)
: (P1.add P2).add P3 = P1.add (P2.add P3) :=
begin
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
