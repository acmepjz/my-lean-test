import algebra.field
import algebra.char_zero
import algebra.char_p
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.linear_change_of_variable
import myhelper.char
import tactic

namespace weierstrass_equation

/--
An automorphism of an elliptic curve is a linear change of variable
which changes it to itself.
-/
@[ext]
structure automorphism {K : Type*} [field K] (E : weierstrass_equation K) :=
mk :: (C : linear_change_of_variable K) (h : C.change_curve E = E)

namespace automorphism

@[simp]
lemma preserve_curve {K : Type*} [field K] {E : weierstrass_equation K}
(C : automorphism E) : C.C.change_curve E = E := C.h

def identity {K : Type*} [field K] (E : weierstrass_equation K) : automorphism E
:= ⟨ @linear_change_of_variable.identity K _,
  @linear_change_of_variable.change_curve.id K _ E ⟩

def composite {K : Type*} [field K] {E : weierstrass_equation K}
(C C' : automorphism E) : automorphism E
:= ⟨ C.C.composite C'.C, by rw [linear_change_of_variable.change_curve.comp, C'.h, C.h] ⟩

def inverse {K : Type*} [field K] {E : weierstrass_equation K}
(C : automorphism E) : automorphism E
:= ⟨ C.C.inverse, by {
  have h := C.h,
  apply_fun C.C.inverse.change_curve at h,
  rw [← linear_change_of_variable.change_curve.comp,
    linear_change_of_variable.inv_comp,
    linear_change_of_variable.change_curve.id] at h,
  exact h.symm,
} ⟩

instance to_group {K : Type*} [field K] {E : weierstrass_equation K}
: group (automorphism E)
:= ⟨ composite,
  (λ C C' C'', by {
    simp only [has_mul.mul, mul_one_class.mul,
      composite, linear_change_of_variable.comp_assoc],
  }), identity E,
  (λ C, by {
    simp only [has_mul.mul, mul_one_class.mul, has_one.one,
      identity, composite, linear_change_of_variable.id_comp, ext_iff],
  }),
  (λ C, by {
    simp only [has_mul.mul, mul_one_class.mul, has_one.one,
      identity, composite, linear_change_of_variable.comp_id, ext_iff],
  }), inverse,
  (λ C C', C.composite (C'.inverse)), by {
    intros _ _, simp only [has_mul.mul, mul_one_class.mul],
  }, (λ C, by {
    simp only [has_mul.mul, has_inv.inv, mul_one_class.mul, monoid.mul,
      has_one.one, mul_one_class.one, monoid.one,
      identity, composite, inverse, linear_change_of_variable.inv_comp],
  }) ⟩

/--
The automorphism which sends P to -P.
-/
def involution {K : Type*} [field K] (E : weierstrass_equation K)
: automorphism E
:= ⟨ ⟨ -1, 0, -E.a1, -E.a3, by simp ⟩, by {
  simp [linear_change_of_variable.change_curve, weierstrass_equation.ext_iff, zero_pow],
  split, { ring, },
  split, { ring, },
  split, { ring, },
  split, { ring, },
  ring,
} ⟩

@[simp]
lemma involution.is_involution {K : Type*} [field K] (E : weierstrass_equation K)
: (involution E).composite (involution E) = identity E :=
begin
  simp [involution, composite, identity,
    linear_change_of_variable.composite,
    linear_change_of_variable.identity],
end

lemma involution.non_trivial {K : Type*} [field K] (E : weierstrass_equation K)
(h : ring_char K = 2 → E.non_singular')
: involution E ≠ identity E :=
begin
  by_cases hchar2 : ring_char K = 2, {
    simp [involution, identity,
      linear_change_of_variable.identity],
    by_cases ha1 : E.a1 = 0, {
      by_cases ha3 : E.a3 = 0, {
        exfalso,
        replace h := h hchar2,
        simp [non_singular', disc, b2, b4, b6, b8, ha1, ha3, zero_pow] at h,
        ring_char2 at h,
        exact h,
      },
      simp [ha3],
    },
    simp [ha1],
  },
  replace h := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2,
  norm_cast at h,
  replace h : (1:K) ≠ -1 := by {
    intro h0,
    apply_fun has_add.add 1 at h0,
    norm_num at h0,
  },
  simp [involution, identity,
    linear_change_of_variable.identity, h.symm],
end

end automorphism

end weierstrass_equation
