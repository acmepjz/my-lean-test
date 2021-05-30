import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.group_law.basic
import gtm106.weierstrass_equation.group_law.add_assoc_lemma_1
import tactic

namespace weierstrass_equation

namespace affine_point

-- copied from [Fri17] An elementary proof of the group law for elliptic curves

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

lemma add.add_eq_self_iff
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
  intro h,
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
