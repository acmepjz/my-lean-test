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

lemma disc_zero_implies_tangent_or_through_singular_point.p00
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(hP' : P = ⟨ 0, 0 ⟩)
(A : K)
(hP : E.affine_point_on_curve P)
(h : monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0)
: neg_of_double_of_affine_plane_point.A E P = A * neg_of_double_of_affine_plane_point.C E P
∨ ∃ (Q : affine_plane_point K), E.affine_point_singular Q ∧ Q.x ≠ 0 ∧ Q.y = A * Q.x :=
begin
  simp [affine_point_on_curve, eval_at_affine_point, hP', zero_pow] at hP,
  simp only [neg_of_double_of_affine_plane_point.A,
    neg_of_double_of_affine_plane_point.C],
  simp only [monic_cubic_poly.disc, a, b, c, B, hP] at h,
  simp [hP', zero_pow] at h ⊢,
  have : (E.a2 - (A + E.a1) * A) ^ 2 * (E.a4 - A * E.a3) ^ 2 - 4 * (E.a4 - A * E.a3) ^ 3
  = ((E.a2 - (A + E.a1) * A) ^ 2 - 4 * (E.a4 - A * E.a3)) * (E.a4 - A * E.a3) ^ 2 := by {
    ring,
  },
  rw this at h, clear this,
  simp at h,
  by_cases h1 : E.a4 - A * E.a3 = 0, {
    left,
    exact sub_eq_zero.1 h1,
  },
  right,
  simp [h1] at h,
  sorry,
end

lemma disc_zero_implies_tangent_or_through_singular_point
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
(h : monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0)
: neg_of_double_of_affine_plane_point.A E P = A * neg_of_double_of_affine_plane_point.C E P
∨ ∃ (Q : affine_plane_point K), E.affine_point_singular Q ∧ Q.x ≠ P.x ∧ Q.y - P.y = A * (Q.x - P.x) :=
begin
  set! C : linear_change_of_variable K := ⟨ 1, P.x, 0, P.y, by simp ⟩ with hC, clear_value C,
  set! E' := C.change_curve E with hE', clear_value E',
  set! P' := C.change_affine_point P with hP', clear_value P',
  replace h : monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ / C.u ^ 12 = 0 := by {
    simp [h],
  },
  rw [← disc_lcov E P A C, ← hE', ← hP'] at h,
  rw [C.preserve_affine_point E P, ← hE', ← hP'] at hP,
  have hA : A_lcov A C = A := by {
    simp [A_lcov, hC],
  },
  rw hA at h,
  cases disc_zero_implies_tangent_or_through_singular_point.p00 E' P' (by {
    simp [hP', hC, linear_change_of_variable.change_affine_point],
  }) A hP h with h h, {
    left,
    simp [hE', hP', hC] at h,
    exact h,
  },
  right,
  rcases h with ⟨ Q', ⟨ h1, h2, h3 ⟩ ⟩,
  use C.inverse.change_affine_point Q',
  rw [← linear_change_of_variable.change_affine_point.id Q',
    ← linear_change_of_variable.comp_inv C,
    ← linear_change_of_variable.change_affine_point.comp, hE',
    ← linear_change_of_variable.preserve_affine_singular_point] at h1,
  use h1,
  simp [linear_change_of_variable.change_affine_point,
    linear_change_of_variable.inverse, hC],
  exact ⟨ h2, h3 ⟩,
end

lemma tangent_implies_disc_zero.p00
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(hP' : P = ⟨ 0, 0 ⟩)
(A : K)
(hP : E.affine_point_on_curve P)
(h : neg_of_double_of_affine_plane_point.A E P = A * neg_of_double_of_affine_plane_point.C E P)
: monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0 :=
begin
  simp [affine_point_on_curve, eval_at_affine_point, hP', zero_pow] at hP,
  simp only [neg_of_double_of_affine_plane_point.A,
    neg_of_double_of_affine_plane_point.C] at h,
  simp only [monic_cubic_poly.disc, a, b, c, B, hP],
  simp [hP', zero_pow] at h ⊢,
  rw h,
  ring,
end

lemma tangent_implies_disc_zero
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
(h : neg_of_double_of_affine_plane_point.A E P = A * neg_of_double_of_affine_plane_point.C E P)
: monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0 :=
begin
  set! C : linear_change_of_variable K := ⟨ 1, P.x, 0, P.y, by simp ⟩ with hC, clear_value C,
  set! E' := C.change_curve E with hE', clear_value E',
  set! P' := C.change_affine_point P with hP', clear_value P',
  suffices : monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ / C.u ^ 12 = 0, {
    simp only [hC, one_pow, div_one] at this,
    exact this,
  },
  rw [← disc_lcov E P A C, ← hE', ← hP'],
  rw [C.preserve_affine_point E P, ← hE', ← hP'] at hP,
  have hA : A_lcov A C = A := by {
    simp [A_lcov, hC],
  },
  rw hA,
  apply tangent_implies_disc_zero.p00 E' P' (by {
    simp [hP', hC, linear_change_of_variable.change_affine_point],
  }) A hP,
  simp [hE', hP'],
  simp [h, hC],
end

lemma through_singular_point_implies_disc_zero
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(Q : affine_plane_point K)
(hQ : E.affine_point_singular Q)
(h : Q.y - P.y = A * (Q.x - P.x))
: monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0 :=
begin
  set! C : linear_change_of_variable K := ⟨ 1, Q.x, 0, Q.y, by simp ⟩ with hC, clear_value C,
  set! E' := C.change_curve E with hE', clear_value E',
  set! P' := C.change_affine_point P with hP', clear_value P',
  set! Q' := C.change_affine_point Q with hQ', clear_value Q',
  suffices : monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ / C.u ^ 12 = 0, {
    simp only [hC, one_pow, div_one] at this,
    exact this,
  },
  rw [← disc_lcov E P A C, ← hE', ← hP'],
  rw [linear_change_of_variable.preserve_affine_singular_point E C Q,
    ← hE', ← hQ'] at hQ,
  have hA : A_lcov A C = A := by {
    simp [A_lcov, hC],
  },
  rw hA,
  replace h : P'.y = A * P'.x := by {
    rw [← sub_eq_zero, sub_sub, sub_eq_zero] at h,
    simp [hP', linear_change_of_variable.change_affine_point, hC],
    rw h,
    ring,
  },
  replace hQ' : Q' = ⟨ 0, 0 ⟩ := by {
    simp [hQ', linear_change_of_variable.change_affine_point, hC],
  },
  simp only [affine_point_singular, affine_point_on_curve,
    eval_at_affine_point, eval_dx_at_affine_point, eval_dy_at_affine_point, hQ'] at hQ,
  simp [zero_pow] at hQ,
  simp only [monic_cubic_poly.disc, a, b, c, B, hQ.1, hQ.2.1, hQ.2.2, h],
  ring,
end

lemma disc_zero_iff_tangent_or_through_singular_point {K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K)
(A : K)
(hP : E.affine_point_on_curve P)
: monic_cubic_poly.disc ⟨ a E A, b E P A, c E P A ⟩ = 0
↔ neg_of_double_of_affine_plane_point.A E P = A * neg_of_double_of_affine_plane_point.C E P
∨ ∃ (Q : affine_plane_point K), E.affine_point_singular Q ∧ Q.x ≠ P.x ∧ Q.y - P.y = A * (Q.x - P.x) :=
begin
  split, {
    exact disc_zero_implies_tangent_or_through_singular_point E P A hP,
  },
  intro h,
  rcases h with h | ⟨ Q, h ⟩, {
    exact tangent_implies_disc_zero E P A hP h,
  },
  exact through_singular_point_implies_disc_zero E P A Q h.1 h.2.2,
end

end intersection_with_line

end weierstrass_equation
