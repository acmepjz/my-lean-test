import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import tactic

/--
Linear change of variable defined in GTM106,
also viewed as a matrix
```
u^2   0   r
u^2*s u^3 t
0     0   1
```
-/
@[ext]
structure linear_change_of_variable (K : Type*) [field K] :=
mk :: (u r s t : K) (hu : u ≠ 0)

namespace linear_change_of_variable

@[simp]
lemma u_non_zero {K : Type*} [field K]
(C : linear_change_of_variable K) : C.u ≠ 0 := C.hu

-- ================
-- Linear change of variables form a group
-- ================

def identity (K : Type*) [field K] : linear_change_of_variable K :=
⟨ 1, 0, 0, 0, by simp ⟩

def composite {K : Type*} [field K]
(C C' : linear_change_of_variable K) : linear_change_of_variable K :=
⟨ C.u*C'.u, C.r*C'.u^2 + C'.r, C'.u*C.s + C'.s,
  C.t*C'.u^3 + C.r*C'.s*C'.u^2 + C'.t, by simp ⟩

lemma comp_assoc {K : Type*} [field K]
(C C' C'' : linear_change_of_variable K) : ((C.composite C').composite C'') = (C.composite (C'.composite C'')) :=
begin
  simp [composite, ext_iff],
  split, { ring, }, split, { ring, }, split, { ring, }, ring,
end

@[simp]
lemma id_comp {K : Type*} [field K]
(C : linear_change_of_variable K) : (identity K).composite C = C :=
begin
  simp [composite, identity, ext_iff],
end

@[simp]
lemma comp_id {K : Type*} [field K]
(C : linear_change_of_variable K) : C.composite (identity K) = C :=
begin
  simp [composite, identity, ext_iff],
end

def inverse {K : Type*} [field K]
(C : linear_change_of_variable K) : linear_change_of_variable K :=
⟨ 1/C.u, -C.r/C.u^2, -C.s/C.u, (C.r*C.s-C.t)/C.u^3, by simp ⟩

@[simp]
lemma inv_comp {K : Type*} [field K]
(C : linear_change_of_variable K) : C.inverse.composite C = identity K :=
begin
  simp [composite, inverse, identity, ext_iff],
  split, { field_simp, ring, },
  field_simp [pow_succ], ring,
end

@[simp]
lemma comp_inv {K : Type*} [field K]
(C : linear_change_of_variable K) : C.composite C.inverse = identity K :=
begin
  simp [composite, inverse, identity, ext_iff],
  split, { field_simp [pow_succ], }, split, { field_simp [mul_comm], },
  field_simp [pow_succ], ring,
end

instance to_group (K : Type*) [field K] : group (linear_change_of_variable K)
:= ⟨ composite, comp_assoc, identity K, id_comp, comp_id, inverse,
  (λ C C', C.composite (C'.inverse)), by {
    intros _ _, simp [has_mul.mul, mul_one_class.mul],
  }, inv_comp ⟩

-- ================
-- Linear change of variables act on Weierstrass equations
-- ================

def change_curve {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K) : weierstrass_equation K :=
⟨ ((E.a1 + 2*C.s)/C.u),
  ((E.a2 - C.s*E.a1 + 3*C.r - C.s^2)/C.u^2),
  ((E.a3 + C.r*E.a1 + 2*C.t)/C.u^3),
  ((E.a4 - C.s*E.a3 + 2*C.r*E.a2 - (C.t+C.r*C.s)*E.a1 + 3*C.r^2 - 2*C.s*C.t)/C.u^4),
  ((E.a6 + C.r*E.a4 + C.r^2*E.a2 + C.r^3 - C.t*E.a3 - C.t^2 - C.r*C.t*E.a1)/C.u^6) ⟩

namespace change_curve

@[simp]
lemma id {K : Type*} [field K]
(E : weierstrass_equation K) :
(identity K).change_curve E = E :=
begin
  simp [weierstrass_equation.ext_iff, identity, change_curve, zero_pow],
end

lemma comp {K : Type*} [field K]
(C C' : linear_change_of_variable K) (E : weierstrass_equation K) :
(C'.composite C).change_curve E = C'.change_curve (C.change_curve E) :=
begin
  simp [weierstrass_equation.ext_iff, composite, change_curve],
  split, { field_simp, ring, },
  split, { field_simp, ring, },
  split, { field_simp, ring, },
  split, { field_simp, ring, },
  field_simp, ring,
end

instance to_has_scalar (K : Type*) [h : field K]
: has_scalar (linear_change_of_variable K) (weierstrass_equation K)
:= ⟨ change_curve ⟩

instance to_mul_action (K : Type*) [h : field K]
: mul_action (linear_change_of_variable K) (weierstrass_equation K)
:= ⟨ @id K h, by {
  intros _ _ _, simp [has_mul.mul, has_scalar.smul,
    mul_one_class.mul, monoid.mul, div_inv_monoid.mul, group.mul, comp],
} ⟩

end change_curve

-- ================
-- Change of invariants under linear change of variables
-- ================

@[simp]
lemma a1 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a1 = (E.a1 + 2*C.s)/C.u :=
begin
  simp [change_curve],
end

@[simp]
lemma a2 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a2 = (E.a2 - C.s*E.a1 + 3*C.r - C.s^2)/C.u^2 :=
begin
  simp [change_curve],
end

@[simp]
lemma a3 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a3 = (E.a3 + C.r*E.a1 + 2*C.t)/C.u^3 :=
begin
  simp [change_curve],
end

@[simp]
lemma a4 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a4 = (E.a4 - C.s*E.a3 + 2*C.r*E.a2 - (C.t+C.r*C.s)*E.a1 + 3*C.r^2 - 2*C.s*C.t)/C.u^4 :=
begin
  simp [change_curve],
end

@[simp]
lemma a6 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a6 = (E.a6 + C.r*E.a4 + C.r^2*E.a2 + C.r^3 - C.t*E.a3 - C.t^2 - C.r*C.t*E.a1)/C.u^6 :=
begin
  simp [change_curve],
end

@[simp]
lemma b2 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b2 = (E.b2 + 12*C.r)/C.u^2 :=
begin
  simp [weierstrass_equation.b2],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma b4 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b4 = (E.b4 + C.r*E.b2 + 6*C.r^2)/C.u^4 :=
begin
  simp [weierstrass_equation.b4, weierstrass_equation.b2],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma b6 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b6 = (E.b6 + 2*C.r*E.b4 + C.r^2*E.b2 + 4*C.r^3)/C.u^6 :=
begin
  simp [weierstrass_equation.b6, weierstrass_equation.b4, weierstrass_equation.b2],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma b8 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b8 = (E.b8 + 3*C.r*E.b6 + 3*C.r^2*E.b4 + C.r^3*E.b2 + 3*C.r^4)/C.u^8 :=
begin
  simp [weierstrass_equation.b8, weierstrass_equation.b6,
    weierstrass_equation.b4, weierstrass_equation.b2],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma c4 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).c4 = E.c4/C.u^4 :=
begin
  simp [weierstrass_equation.c4],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma c6 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).c6 = E.c6/C.u^6 :=
begin
  simp [weierstrass_equation.c6],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma disc {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).disc = E.disc/C.u^12 :=
begin
  simp [weierstrass_equation.disc],
  simp [weierstrass_equation.b8, weierstrass_equation.b6,
    weierstrass_equation.b4, weierstrass_equation.b2],
  field_simp [pow_succ],
  ring,
end

@[simp]
lemma j {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).j = E.j :=
begin
  simp [weierstrass_equation.j],
  by_cases h : E.disc = 0, {
    simp [h],
  },
  field_simp [pow_succ, h],
  ring,
end

lemma preserve_non_singular' {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.non_singular' ↔ (C.change_curve E).non_singular' :=
begin
  simp [weierstrass_equation.non_singular', hu],
end

lemma preserve_has_node' {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_node' ↔ (C.change_curve E).has_node' :=
begin
  simp [weierstrass_equation.has_node'],
end

lemma preserve_has_cusp' {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_cusp' ↔ (C.change_curve E).has_cusp' :=
begin
  simp [weierstrass_equation.has_cusp'],
end

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
  intros _ _ _, simp [has_mul.mul, has_scalar.smul,
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
  intros _ _ _, simp [has_mul.mul, has_scalar.smul,
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

-- ================
-- Isomorphism class of Weierstrass equations under linear change of variable
-- ================

namespace weierstrass_equation

def is_isom' {K : Type*} [field K]
(E E' : weierstrass_equation K) := ∃ C : linear_change_of_variable K,
(C.change_curve E) = E'

lemma is_isom'.refl {K : Type*} [field K]
(E : weierstrass_equation K) : E.is_isom' E :=
begin
  use linear_change_of_variable.identity K,
  exact linear_change_of_variable.change_curve.id E,
end

lemma is_isom'.symm {K : Type*} [field K]
(E E' : weierstrass_equation K) (h : E.is_isom' E') : E'.is_isom' E :=
begin
  rcases h with ⟨ C, h ⟩,
  use C.inverse,
  rw [← h, ← linear_change_of_variable.change_curve.comp],
  simp,
end

lemma is_isom'.trans {K : Type*} [field K]
(E E' E'' : weierstrass_equation K) (h : E.is_isom' E') (h' : E'.is_isom' E'')
: E.is_isom' E'' :=
begin
  rcases h with ⟨ C, h ⟩,
  rcases h' with ⟨ C', h' ⟩,
  use C'.composite C,
  rw [linear_change_of_variable.change_curve.comp, h, h'],
end

lemma is_isom'.is_equivalence (K : Type*) [h : field K]
: equivalence (@is_isom' K h) :=
mk_equivalence (@is_isom' K h)
(@is_isom'.refl K h)
(@is_isom'.symm K h)
(@is_isom'.trans K h)

instance isom_class'.setoid (K : Type*) [h : field K]
: setoid (weierstrass_equation K) :=
setoid.mk (@is_isom' K h)
(is_isom'.is_equivalence K)

/--
Isomorphism class of Weierstrass equations under linear change of variable
-/
def isom_class' (K : Type*) [field K] : Type* :=
quotient (isom_class'.setoid K)

def isom_class'.j {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@j K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.j],
}) E

def isom_class'.non_singular' {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@non_singular' K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_non_singular'],
}) E

def isom_class'.has_node' {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_node' K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_node'],
}) E

def isom_class'.has_cusp' {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_cusp' K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_cusp'],
}) E

def isom_class'.non_singular {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@non_singular K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_non_singular],
}) E

def isom_class'.has_node {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_node K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_node],
}) E

def isom_class'.has_cusp {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_cusp K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_cusp],
}) E

end weierstrass_equation
