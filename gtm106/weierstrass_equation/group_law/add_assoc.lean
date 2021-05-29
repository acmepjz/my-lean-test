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
(h1not2tors : 2*P1.y + E.a1*P1.x + E.a3 ≠ 0)
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
(hnot2tors : 2*P.y + E.a1*P.x + E.a3 ≠ 0)
(h2not2tors : 2*(E.double_of_affine_plane_point P).y + E.a1*(E.double_of_affine_plane_point P).x + E.a3 ≠ 0)
(hx31 : (E.add_of_affine_plane_point (E.double_of_affine_plane_point P) P).x - P.x ≠ 0)
(hx21 : (E.double_of_affine_plane_point P).x - P.x ≠ 0)
: (E.double_of_affine_plane_point (E.double_of_affine_plane_point P))
= E.add_of_affine_plane_point P (E.add_of_affine_plane_point P (E.double_of_affine_plane_point P)) :=
begin
  sorry,
end

lemma add.assoc.lemma_2_4
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
        replace hy := congr (congr_arg has_sub.sub (eq.refl P1.y)) hy.symm,
        ring_nf at hy,
        simp only [neg_of_affine_plane_point, hx, hy],
        ring,
      },
      simp [neg_of_add, hx, hx', hy, hy', neg],
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
    sorry,
  },
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
