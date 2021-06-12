import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.linear_change_of_variable.basic
import gtm106.weierstrass_equation.linear_change_of_variable.change_curve
import tactic

namespace linear_change_of_variable

-- ================
-- Linear change of variables act on points
-- ================

def change_affine_point_back {K : Type*} [field K]
(C : linear_change_of_variable K) (P : affine_plane_point K) : affine_plane_point K :=
⟨ C.u^2*P.x + C.r, C.u^3*P.y + C.u^2*C.s*P.x + C.t ⟩

def change_projective_point_back' {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point' K) : projective_plane_point' K :=
⟨ C.u^2*P.X + C.r*P.Z, C.u^3*P.Y + C.u^2*C.s*P.X + C.t*P.Z, P.Z, by {
  rintros ⟨ hX, hY, hZ ⟩,
  simp [hZ] at hX,
  simp [hZ, hX] at hY,
  exact P.h ⟨ hX, hY, hZ ⟩,
} ⟩

def change_projective_point_back {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point K) : projective_plane_point K :=
quotient.lift (λ (P : projective_plane_point' K), quotient.mk (C.change_projective_point_back' P))
(by {
  rintros P P' ⟨ k, h1, h2, h3, h4 ⟩,
  simp,
  use k,
  simp [change_projective_point_back', h1, h2, h3, h4],
  split, { ring, }, ring,
}) P

def change_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (P : affine_plane_point K) : affine_plane_point K :=
⟨ P.x/C.u^2 - C.r/C.u^2, P.y/C.u^3 - C.s*P.x/C.u^3 + (C.r*C.s-C.t)/C.u^3 ⟩

namespace change_affine_point

@[simp]
lemma id {K : Type*} [field K]
(P : affine_plane_point K) :
(identity K).change_affine_point P = P :=
begin
  simp [identity, change_affine_point, affine_plane_point.ext_iff],
end

lemma comp {K : Type*} [field K]
(C C' : linear_change_of_variable K) (P : affine_plane_point K) :
C.change_affine_point (C'.change_affine_point P) = (C.composite C').change_affine_point P :=
begin
  simp [composite, change_affine_point, affine_plane_point.ext_iff],
  split, { field_simp, ring, },
  field_simp, ring,
end

instance to_has_scalar (K : Type*) [h : field K]
: has_scalar (linear_change_of_variable K) (affine_plane_point K)
:= ⟨ change_affine_point ⟩

instance to_mul_action (K : Type*) [h : field K]
: mul_action (linear_change_of_variable K) (affine_plane_point K)
:= ⟨ @id K h, by {
  intros _ _ _, simp only [has_mul.mul, has_scalar.smul,
    mul_one_class.mul, monoid.mul, div_inv_monoid.mul, group.mul, comp],
} ⟩

end change_affine_point

-- no denominator version
def change_projective_point' {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point' K) : projective_plane_point' K :=
⟨ P.X*C.u - P.Z*C.r*C.u, P.Y - C.s*P.X + P.Z*(C.r*C.s-C.t), P.Z*C.u^3, by {
  rintros ⟨ hX, hY, hZ ⟩,
  simp at hZ,
  simp [hZ] at hX,
  simp [hZ, hX] at hY,
  exact P.h ⟨ hX, hY, hZ ⟩,
} ⟩

def change_projective_point {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point K) : projective_plane_point K :=
quotient.lift (λ (P : projective_plane_point' K), quotient.mk (C.change_projective_point' P))
(by {
  rintros P P' ⟨ k, h1, h2, h3, h4 ⟩,
  simp,
  use k,
  simp [change_projective_point', h1, h2, h3, h4],
  split, { ring, }, split, { ring, }, ring,
}) P

namespace change_projective_point

@[simp]
lemma id {K : Type*} [field K]
(P : projective_plane_point K) :
(identity K).change_projective_point P = P :=
begin
  revert P,
  refine quotient.ind _,
  intro P,
  simp [identity, change_projective_point, change_projective_point'],
  use 1,
  simp,
end

lemma comp {K : Type*} [field K]
(C C' : linear_change_of_variable K) (P : projective_plane_point K) :
C.change_projective_point (C'.change_projective_point P) = (C.composite C').change_projective_point P :=
begin
  revert P,
  refine quotient.ind _,
  intro P,
  simp [composite, change_projective_point, change_projective_point'],
  use 1,
  simp,
  split, { ring, }, split, { ring, }, ring,
end

instance to_has_scalar (K : Type*) [h : field K]
: has_scalar (linear_change_of_variable K) (projective_plane_point K)
:= ⟨ change_projective_point ⟩

instance to_mul_action (K : Type*) [h : field K]
: mul_action (linear_change_of_variable K) (projective_plane_point K)
:= ⟨ @id K h, by {
  intros _ _ _, simp only [has_mul.mul, has_scalar.smul,
    mul_one_class.mul, monoid.mul, div_inv_monoid.mul, group.mul, comp],
} ⟩

end change_projective_point

-- ================
-- Properties of linear change of variables on points
-- ================

@[simp]
lemma change_affine_point_back.inv {K : Type*} [field K]
(C : linear_change_of_variable K) (P : affine_plane_point K) :
C.change_affine_point_back P = C.inverse.change_affine_point P :=
begin
  simp [change_affine_point_back, inverse, change_affine_point],
  split, { field_simp [pow_succ], ring, },
  field_simp [pow_succ], ring,
end

@[simp]
lemma change_projective_point_back.inv {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point K) :
C.change_projective_point_back P = C.inverse.change_projective_point P :=
begin
  revert P,
  refine quotient.ind _,
  intro P,
  simp [change_projective_point_back, inverse, change_projective_point,
    change_projective_point_back', change_projective_point'],
  use 1/C.u^3,
  simp,
  split, { field_simp [pow_succ], ring, },
  split, { field_simp [pow_succ], ring, },
  field_simp [pow_succ],
end

@[simp]
lemma eval_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_at_affine_point (C.change_affine_point P) = (E.eval_at_affine_point P)/C.u^6 :=
begin
  simp [weierstrass_equation.eval_at_affine_point,
    change_curve, change_affine_point],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma eval_dx_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_dx_at_affine_point (C.change_affine_point P)
= (E.eval_dx_at_affine_point P + C.s * E.eval_dy_at_affine_point P)/C.u^4 :=
begin
  simp [weierstrass_equation.eval_dx_at_affine_point,
    weierstrass_equation.eval_dy_at_affine_point,
    change_curve, change_affine_point],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma eval_dy_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_dy_at_affine_point (C.change_affine_point P) = (E.eval_dy_at_affine_point P)/C.u^3 :=
begin
  simp [weierstrass_equation.eval_dy_at_affine_point,
    change_curve, change_affine_point],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma eval_hessian_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_hessian_at_affine_point (C.change_affine_point P) = (E.eval_hessian_at_affine_point P)/C.u^2 :=
begin
  simp [weierstrass_equation.eval_hessian_at_affine_point,
    weierstrass_equation.b2,
    change_curve, change_affine_point],
  field_simp [pow_succ],
  ring,
end

lemma preserve_affine_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_on_curve P ↔ (C.change_curve E).affine_point_on_curve
(C.change_affine_point P) :=
begin
  simp [weierstrass_equation.affine_point_on_curve],
end

lemma preserve_affine_regular_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_regular P ↔ (C.change_curve E).affine_point_regular
(C.change_affine_point P) :=
begin
  simp [weierstrass_equation.affine_point_regular, (C.preserve_affine_point E P).symm],
  intro h,
  split, {
    intros h1 h2 h3,
    simp [h3] at h1 h2,
    exact h1 h2,
  }, {
    intros h1 h2 h3,
    simp [h2, h3] at h1,
    exact h1,
  },
end

lemma preserve_affine_singular_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_singular P ↔ (C.change_curve E).affine_point_singular
(C.change_affine_point P) :=
begin
  by_cases h : E.affine_point_on_curve P, {
    rw [← E.affine_point_is_regular_or_singular P h,
      ← (C.change_curve E).affine_point_is_regular_or_singular _
      ((C.preserve_affine_point E P).1 h),
      C.preserve_affine_regular_point E P],
  },
  have h2 := h,
  rw C.preserve_affine_point E P at h,
  simp [weierstrass_equation.affine_point_singular, h, h2],
end

lemma preserve_node
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_is_node P ↔ (C.change_curve E).affine_point_is_node
(C.change_affine_point P) :=
begin
  simp [weierstrass_equation.affine_point_is_node,
    C.preserve_affine_singular_point E P],
end

lemma preserve_cusp
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_is_cusp P ↔ (C.change_curve E).affine_point_is_cusp
(C.change_affine_point P) :=
begin
  simp [weierstrass_equation.affine_point_is_cusp,
    C.preserve_affine_singular_point E P],
end

/-
lemma weierstrass_equation.change_curve_preserve_projective_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (X Y Z : K) :
let P' := C.change_projective_point X Y Z in
E.projective_point_on_curve X Y Z ↔ (C.change_curve E).projective_point_on_curve P'.1 P'.2.1 P'.2.2 :=
begin
  sorry,
end
-/

lemma preserve_non_singular {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.non_singular ↔ (C.change_curve E).non_singular :=
begin
  repeat { rw weierstrass_equation.non_singular_iff_affine_non_singular },
  unfold weierstrass_equation.affine_non_singular,
  split, {
    intros h P,
    replace h := h (C.inverse.change_affine_point P),
    rw [C.preserve_affine_point E _,
      C.preserve_affine_regular_point E _] at h,
    simp [change_affine_point.comp] at h,
    exact h,
  }, {
    intros h P,
    replace h := h (C.change_affine_point P),
    rw [← C.preserve_affine_point E _,
      ← C.preserve_affine_regular_point E _] at h,
    exact h,
  },
end

lemma preserve_has_node {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_node ↔ (C.change_curve E).has_node :=
begin
  unfold weierstrass_equation.has_node,
  split, {
    rintros ⟨ P, hP ⟩,
    use C.change_affine_point P,
    exact (C.preserve_node E P).1 hP,
  }, {
    rintros ⟨ P, hP ⟩,
    use C.inverse.change_affine_point P,
    rw [C.inverse.preserve_node _, ← change_curve.comp] at hP,
    simp at hP,
    exact hP,
  },
end

lemma preserve_has_cusp {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_cusp ↔ (C.change_curve E).has_cusp :=
begin
  unfold weierstrass_equation.has_cusp,
  split, {
    rintros ⟨ P, hP ⟩,
    use C.change_affine_point P,
    exact (C.preserve_cusp E P).1 hP,
  }, {
    rintros ⟨ P, hP ⟩,
    use C.inverse.change_affine_point P,
    rw [C.inverse.preserve_cusp _, ← change_curve.comp] at hP,
    simp at hP,
    exact hP,
  },
end

end linear_change_of_variable
