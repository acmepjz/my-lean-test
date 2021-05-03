import algebra.field
import algebra.char_zero
import algebra.char_p
import gtm106.naive_plane
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.linear_change_of_variable
import myhelper.char
import tactic

namespace weierstrass_equation

def is_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a3 = 0

@[simp]
lemma b2_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b2 = 4*E.a2 :=
begin
  simp [b2, h.1, zero_pow],
end

@[simp]
lemma b4_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b4 = 2*E.a4 :=
begin
  simp [b4, h.1, h.2],
end

@[simp]
lemma b6_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b6 = 4*E.a6 :=
begin
  simp [b6, h.2, zero_pow],
end

@[simp]
lemma b8_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b8 = 4*E.a2*E.a6 - E.a4^2 :=
begin
  simp [b8, h.1, h.2, zero_pow],
end

@[simp]
lemma c4_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.c4 = 16*E.a2^2 - 48*E.a4 :=
begin
  simp [c4, h],
  ring,
end

@[simp]
lemma c6_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.c6 = -64*E.a2^3 + 288*E.a2*E.a4 - 864*E.a6 :=
begin
  simp [c6, h],
  ring,
end

@[simp]
lemma disc_of_model_of_char_neq_2 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.disc = -64*E.a2^3*E.a6 + 16*E.a2^2*E.a4^2 - 64*E.a4^3 - 432*E.a6^2 +288*E.a2*E.a4*E.a6 :=
begin
  simp [disc, h],
  ring,
end

lemma have_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K ≠ 2)
: ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_neq_2 :=
begin
  replace hchar2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2,
  norm_cast at hchar2,
  use ⟨ 1, 0, -E.a1/2, -E.a3/2, by simp ⟩,
  simp [is_model_of_char_neq_2, linear_change_of_variable.change_curve],
  field_simp [hchar2],
  simp [mul_comm],
end

def is_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a2 = 0 ∧ E.a3 = 0

@[simp]
lemma b2_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b2 = 0 :=
begin
  simp [b2, h.1, h.2.1, zero_pow],
end

@[simp]
lemma b4_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b4 = 2*E.a4 := E.b4_of_model_of_char_neq_2 ⟨ h.1, h.2.2 ⟩

@[simp]
lemma b6_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b6 = 4*E.a6 := E.b6_of_model_of_char_neq_2 ⟨ h.1, h.2.2 ⟩

@[simp]
lemma b8_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b8 = -E.a4^2 :=
begin
  simp [b8, h.1, h.2.1, h.2.2, zero_pow],
end

@[simp]
lemma c4_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.c4 = -48*E.a4 :=
begin
  simp [c4, h],
  ring,
end

@[simp]
lemma c6_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.c6 = -864*E.a6 :=
begin
  simp [c6, h],
  ring,
end

@[simp]
lemma disc_of_model_of_char_neq_2_and_3 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.disc = -16*(4*E.a4^3 + 27*E.a6^2) :=
begin
  simp [disc, h],
  ring,
end

@[simp]
lemma j_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar2 : ring_char K ≠ 2) :
E.j = 6912*E.a4^3/(4*E.a4^3 + 27*E.a6^2) :=
begin
  simp [j, h],
  by_cases h : 4*E.a4^3 + 27*E.a6^2 = 0, {
    rw h, simp,
  },
  have h16 := power_of_prime_neq_char_is_non_zero K 16 2 4 (by norm_num) (by norm_num) hchar2,
  norm_num at h16,
  field_simp [h, h16],
  ring,
end

lemma have_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K ≠ 2) (hchar3 : ring_char K ≠ 3)
: ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_neq_2_and_3 :=
begin
  rcases E.have_model_of_char_neq_2 hchar2 with ⟨ C, h1 ⟩,
  set E' := C.change_curve E with hE,
  replace hchar3 := prime_neq_char_is_non_zero K 3 (by norm_num) hchar3,
  norm_cast at hchar3,
  let C' : linear_change_of_variable K := ⟨ 1, -E'.a2/3, 0, 0, by simp ⟩,
  use C'.composite C,
  rw [linear_change_of_variable.change_curve.comp, ← hE],
  simp [is_model_of_char_neq_2_and_3,
    linear_change_of_variable.change_curve,
    h1.1, h1.2, zero_pow],
  field_simp [hchar3],
  ring,
end

def is_model_of_char_3_j_non_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a3 = 0 ∧ E.a4 = 0

@[simp]
lemma c4_of_model_of_char_3_j_non_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_3_j_non_zero) (hchar3 : ring_char K = 3) :
E.c4 = E.a2^2 :=
begin
  simp [c4, b2, b4,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char3,
end

@[simp]
lemma disc_of_model_of_char_3_j_non_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_3_j_non_zero) (hchar3 : ring_char K = 3) :
E.disc = -E.a2^3*E.a6 :=
begin
  simp [disc, b2, b4,
    b6, b8,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char3,
end

@[simp]
lemma j_of_model_of_char_3_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_3_j_non_zero) (hchar3 : ring_char K = 3) :
E.j = -E.a2^3/E.a6 :=
begin
  simp [j, h, hchar3],
  by_cases ha6 : E.a6 = 0, {
    rw ha6, simp,
  },
  by_cases ha2 : E.a2 = 0, {
    rw ha2, simp [zero_pow],
  },
  field_simp [ha2, ha6], ring,
end

@[simp]
lemma c4_of_model_of_char_3_j_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar3 : ring_char K = 3) :
E.c4 = 0 :=
begin
  simp [h],
  ring_char3,
end

@[simp]
lemma disc_of_model_of_char_3_j_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar3 : ring_char K = 3) :
E.disc = -E.a4^3 :=
begin
  simp [h],
  ring_char3,
end

@[simp]
lemma j_of_model_of_char_3_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar3 : ring_char K = 3) :
E.j = 0 :=
begin
  simp [j, h, hchar3],
end

lemma have_model_of_char_3 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar3 : ring_char K = 3)
: ((E.non_singular' → E.j ≠ 0) ∧ ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_3_j_non_zero)
∨ (E.j = 0 ∧ ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_neq_2_and_3) :=
begin
  have hchar2 : ring_char K ≠ 2 := by {
    rw hchar3, norm_num,
  },
  rcases E.have_model_of_char_neq_2 hchar2 with ⟨ C, h1 ⟩,
  set E' := C.change_curve E with hE,
  have hdisc : E'.disc = E'.a2^2*E'.a4^2 - E'.a2^3*E'.a6 - E'.a4^3 := by {
    clear_value E',
    simp [h1],
    ring_char3,
  },
  have hc4 : E'.c4 = E'.a2^2 := by {
    clear_value E',
    simp [h1],
    ring_char3,
  },
  have hj : E'.j = E.j := C.j E,
  have hnonsing : E.non_singular' ↔ E'.non_singular' := C.preserve_non_singular' E,
  rw [← hj, hnonsing],
  unfold j non_singular',
  rw hc4,
  by_cases ha2 : E'.a2 = 0, {
    right,
    split, { rw ha2, ring, },
    use C,
    exact ⟨ h1.1, ha2, h1.2 ⟩,
  },
  left,
  clear_value E',
  split, {
    intro hdisc,
    simp [ha2, hdisc],
  },
  let C' : linear_change_of_variable K := ⟨ 1, E'.a4/E'.a2, 0, 0, by simp ⟩,
  use C'.composite C,
  rw [linear_change_of_variable.change_curve.comp, ← hE],
  simp [is_model_of_char_3_j_non_zero,
    linear_change_of_variable.change_curve,
    h1.1, h1.2],
  field_simp [ha2],
  ring_char3,
end

def is_model_of_char_2_j_non_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
E.a1 = 1 ∧ E.a3 = 0 ∧ E.a4 = 0

def is_model_of_char_2_j_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a2 = 0

@[simp]
lemma c4_of_model_of_char_2_j_non_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_non_zero) (hchar2 : ring_char K = 2) :
E.c4 = 1 :=
begin
  simp [c4, b2, b4,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char2,
end

@[simp]
lemma disc_of_model_of_char_2_j_non_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_non_zero) (hchar2 : ring_char K = 2) :
E.disc = E.a6 :=
sub_eq_zero.1 begin
  simp [disc, b2, b4,
    b6, b8,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char2,
end

@[simp]
lemma j_of_model_of_char_2_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_non_zero) (hchar2 : ring_char K = 2) :
E.j = 1/E.a6 :=
begin
  simp [j, h, hchar2],
end

@[simp]
lemma c4_of_model_of_char_2_j_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_zero) (hchar2 : ring_char K = 2) :
E.c4 = 0 :=
begin
  simp [c4, b2, b4,
    h.1, h.2, zero_pow],
  ring_char2,
end

@[simp]
lemma disc_of_model_of_char_2_j_zero {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_zero) (hchar2 : ring_char K = 2) :
E.disc = E.a3^4 :=
sub_eq_zero.1 begin
  simp [disc, b2, b4,
    b6, b8,
    h.1, h.2, zero_pow],
  ring_char2,
end

@[simp]
lemma j_of_model_of_char_2_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_zero) (hchar2 : ring_char K = 2) :
E.j = 0 :=
begin
  simp [j, h, hchar2],
end

lemma have_model_of_char_2 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K = 2)
: ((E.non_singular' → E.j ≠ 0) ∧ ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_2_j_non_zero)
∨ (E.j = 0 ∧ ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_2_j_zero) :=
begin
  have hc4 : E.c4 = E.a1^4 := by {
    simp [c4, b2, b4],
    ring_char2,
  },
  unfold j,
  rw hc4,
  by_cases ha1 : E.a1 = 0, {
    right,
    split, {
      rw ha1,
      ring,
    },
    use ⟨ 1, E.a2, 0, 0, by simp ⟩,
    simp [is_model_of_char_2_j_zero,
      linear_change_of_variable.change_curve,
      ha1],
    ring_char2,
  },
  left,
  split, {
    unfold non_singular',
    intro hdisc,
    field_simp [ha1, hdisc],
  },
  use ⟨ E.a1, E.a3/E.a1, 0, (E.a1^2*E.a4+E.a3^2)/E.a1^3, ha1 ⟩,
  simp [is_model_of_char_2_j_non_zero,
    linear_change_of_variable.change_curve,
    ha1],
  split, {
    field_simp [ha1], ring_char2,
  },
  field_simp [pow_succ, ha1], ring_char2,
end

end weierstrass_equation
