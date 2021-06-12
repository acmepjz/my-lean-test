import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.linear_change_of_variable.basic
import tactic

namespace linear_change_of_variable

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
  intros _ _ _, simp only [has_mul.mul, has_scalar.smul,
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

end linear_change_of_variable
