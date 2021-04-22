import algebra.field
import algebra.char_zero
import algebra.char_p
import gtm106.naive_plane
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.linear_change_of_variable
import myhelper.char
import tactic

noncomputable theory

def weierstrass_equation.is_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a3 = 0

@[simp]
lemma weierstrass_equation.b2_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b2 = 4*E.a2 :=
begin
  simp [weierstrass_equation.b2, h.1],
end

@[simp]
lemma weierstrass_equation.b4_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b4 = 2*E.a4 :=
begin
  simp [weierstrass_equation.b4, h.1, h.2],
end

@[simp]
lemma weierstrass_equation.b6_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b6 = 4*E.a6 :=
begin
  simp [weierstrass_equation.b6, h.2],
end

@[simp]
lemma weierstrass_equation.b8_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.b8 = 4*E.a2*E.a6 - E.a4^2 :=
begin
  simp [weierstrass_equation.b8, h.1, h.2, zero_pow],
end

@[simp]
lemma weierstrass_equation.c4_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.c4 = 16*E.a2^2 - 48*E.a4 :=
begin
  simp [weierstrass_equation.c4, h],
  ring,
end

@[simp]
lemma weierstrass_equation.c6_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.c6 = -64*E.a2^3 + 288*E.a2*E.a4 - 864*E.a6 :=
begin
  simp [weierstrass_equation.c6, h],
  ring,
end

@[simp]
lemma weierstrass_equation.disc_of_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2) :
E.disc = -64*E.a2^3*E.a6 + 16*E.a2^2*E.a4^2 - 64*E.a4^3 - 432*E.a6^2 +288*E.a2*E.a4*E.a6 :=
begin
  simp [weierstrass_equation.disc, h],
  ring,
end

lemma weierstrass_equation.have_model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K ≠ 2)
: ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_neq_2 :=
begin
  replace hchar2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2,
  norm_cast at hchar2,
  let C : linear_change_of_variable K := linear_change_of_variable.mk 1 0 (-E.a1/2) (-E.a3/2) (by simp),
  use C,
  unfold weierstrass_equation.is_model_of_char_neq_2
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a3
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  field_simp [hchar2],
  simp [mul_comm],
end

def weierstrass_equation.is_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a2 = 0 ∧ E.a3 = 0

@[simp]
lemma weierstrass_equation.b2_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b2 = 0 :=
begin
  simp [weierstrass_equation.b2, h.1, h.2.1],
end

@[simp]
lemma weierstrass_equation.b4_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b4 = 2*E.a4 := E.b4_of_model_of_char_neq_2 ⟨ h.1, h.2.2 ⟩

@[simp]
lemma weierstrass_equation.b6_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b6 = 4*E.a6 := E.b6_of_model_of_char_neq_2 ⟨ h.1, h.2.2 ⟩

@[simp]
lemma weierstrass_equation.b8_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.b8 = -E.a4^2 :=
begin
  simp [weierstrass_equation.b8, h.1, h.2.1, h.2.2, zero_pow],
end

@[simp]
lemma weierstrass_equation.c4_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.c4 = -48*E.a4 :=
begin
  simp [weierstrass_equation.c4, h],
  ring,
end

@[simp]
lemma weierstrass_equation.c6_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.c6 = -864*E.a6 :=
begin
  simp [weierstrass_equation.c6, h],
  ring,
end

@[simp]
lemma weierstrass_equation.disc_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) :
E.disc = -16*(4*E.a4^3 + 27*E.a6^2) :=
begin
  simp [weierstrass_equation.disc, h],
  ring,
end

@[simp]
lemma weierstrass_equation.j_of_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar2 : ring_char K ≠ 2) :
E.j = 6912*E.a4^3/(4*E.a4^3 + 27*E.a6^2) :=
begin
  simp [weierstrass_equation.j, h],
  by_cases h : 4*E.a4^3 + 27*E.a6^2 = 0, {
    rw h, simp,
  },
  have h16 := power_of_prime_neq_char_is_non_zero K 16 2 4 (by norm_num) (by norm_num) hchar2,
  norm_num at h16,
  field_simp [h, h16],
  ring,
end

lemma weierstrass_equation.have_model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K ≠ 2) (hchar3 : ring_char K ≠ 3)
: ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_neq_2_and_3 :=
begin
  rcases E.have_model_of_char_neq_2 hchar2 with ⟨ C, h1 ⟩,
  set E' := C.change_curve E with hE,
  replace hchar3 := prime_neq_char_is_non_zero K 3 (by norm_num) hchar3,
  norm_cast at hchar3,
  let C' : linear_change_of_variable K := linear_change_of_variable.mk 1 (-E'.a2/3) 0 0 (by simp),
  use C.composite C',
  rw [← linear_change_of_variable.change_curve.comp, ← hE],
  unfold weierstrass_equation.is_model_of_char_neq_2_and_3
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  rw [h1.1, h1.2],
  field_simp [hchar3],
  ring,
end

def weierstrass_equation.is_model_of_char_3_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a3 = 0 ∧ E.a4 = 0

@[simp]
lemma weierstrass_equation.c4_of_model_of_char_3_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_3_j_non_zero) (hchar3 : ring_char K = 3) :
E.c4 = E.a2^2 :=
begin
  simp [weierstrass_equation.c4, weierstrass_equation.b2, weierstrass_equation.b4,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char3,
end

@[simp]
lemma weierstrass_equation.disc_of_model_of_char_3_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_3_j_non_zero) (hchar3 : ring_char K = 3) :
E.disc = -E.a2^3*E.a6 :=
begin
  simp [weierstrass_equation.disc, weierstrass_equation.b2, weierstrass_equation.b4,
    weierstrass_equation.b6, weierstrass_equation.b8,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char3,
end

@[simp]
lemma weierstrass_equation.j_of_model_of_char_3_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_3_j_non_zero) (hchar3 : ring_char K = 3) :
E.j = -E.a2^3/E.a6 :=
begin
  simp [weierstrass_equation.j, h, hchar3],
  by_cases ha6 : E.a6 = 0, {
    rw ha6, simp,
  },
  by_cases ha2 : E.a2 = 0, {
    rw ha2, simp [zero_pow],
  },
  field_simp [ha2, ha6], ring,
end

@[simp]
lemma weierstrass_equation.c4_of_model_of_char_3_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar3 : ring_char K = 3) :
E.c4 = 0 :=
begin
  simp [h],
  ring_char3,
end

@[simp]
lemma weierstrass_equation.disc_of_model_of_char_3_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar3 : ring_char K = 3) :
E.disc = -E.a4^3 :=
begin
  simp [h],
  ring_char3,
end

@[simp]
lemma weierstrass_equation.j_of_model_of_char_3_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_neq_2_and_3) (hchar3 : ring_char K = 3) :
E.j = 0 :=
begin
  simp [weierstrass_equation.j, h, hchar3],
end

lemma weierstrass_equation.have_model_of_char_3 {K : Type*} [field K]
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
    simp [h1],
    ring_char3,
  },
  have hc4 : E'.c4 = E'.a2^2 := by {
    simp [h1],
    ring_char3,
  },
  have hj : E'.j = E.j := C.j E,
  have hnonsing : E.non_singular' ↔ E'.non_singular' := C.preserve_non_singular' E,
  rw [← hj, hnonsing],
  unfold weierstrass_equation.j
  weierstrass_equation.non_singular',
  rw hc4,
  by_cases ha2 : E'.a2 = 0, {
    right,
    split, { rw ha2, ring, },
    use C,
    exact ⟨ h1.1, ha2, h1.2 ⟩,
  },
  left,
  split, {
    intro hdisc,
    field_simp [ha2, hdisc],
  },
  let C' : linear_change_of_variable K := linear_change_of_variable.mk 1 (E'.a4/E'.a2) 0 0 (by simp),
  use C.composite C',
  rw [← linear_change_of_variable.change_curve.comp, ← hE],
  unfold weierstrass_equation.is_model_of_char_3_j_non_zero
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  rw [h1.1, h1.2],
  split, { ring, }, split, { ring, },
  field_simp [ha2],
  ring_char3,
end

def weierstrass_equation.is_model_of_char_2_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) :=
E.a1 = 1 ∧ E.a3 = 0 ∧ E.a4 = 0

def weierstrass_equation.is_model_of_char_2_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) :=
E.a1 = 0 ∧ E.a2 = 0

@[simp]
lemma weierstrass_equation.c4_of_model_of_char_2_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_non_zero) (hchar2 : ring_char K = 2) :
E.c4 = 1 :=
begin
  simp [weierstrass_equation.c4, weierstrass_equation.b2, weierstrass_equation.b4,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char2,
end

@[simp]
lemma weierstrass_equation.disc_of_model_of_char_2_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_non_zero) (hchar2 : ring_char K = 2) :
E.disc = E.a6 :=
sub_eq_zero.1 begin
  simp [weierstrass_equation.disc, weierstrass_equation.b2, weierstrass_equation.b4,
    weierstrass_equation.b6, weierstrass_equation.b8,
    h.1, h.2.1, h.2.2, zero_pow],
  ring_char2,
end

@[simp]
lemma weierstrass_equation.j_of_model_of_char_2_j_non_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_non_zero) (hchar2 : ring_char K = 2) :
E.j = 1/E.a6 :=
begin
  simp [weierstrass_equation.j, h, hchar2],
end

@[simp]
lemma weierstrass_equation.c4_of_model_of_char_2_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_zero) (hchar2 : ring_char K = 2) :
E.c4 = 0 :=
begin
  simp [weierstrass_equation.c4, weierstrass_equation.b2, weierstrass_equation.b4,
    h.1, h.2, zero_pow],
  ring_char2,
end

@[simp]
lemma weierstrass_equation.disc_of_model_of_char_2_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_zero) (hchar2 : ring_char K = 2) :
E.disc = E.a3^4 :=
sub_eq_zero.1 begin
  simp [weierstrass_equation.disc, weierstrass_equation.b2, weierstrass_equation.b4,
    weierstrass_equation.b6, weierstrass_equation.b8,
    h.1, h.2, zero_pow],
  ring_char2,
end

@[simp]
lemma weierstrass_equation.j_of_model_of_char_2_j_zero {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_model_of_char_2_j_zero) (hchar2 : ring_char K = 2) :
E.j = 0 :=
begin
  simp [weierstrass_equation.j, h, hchar2],
end

lemma weierstrass_equation.have_model_of_char_2 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K = 2)
: ((E.non_singular' → E.j ≠ 0) ∧ ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_2_j_non_zero)
∨ (E.j = 0 ∧ ∃ (C : linear_change_of_variable K), (C.change_curve E).is_model_of_char_2_j_zero) :=
begin
  have hc4 : E.c4 = E.a1^4 := by {
    simp [weierstrass_equation.c4, weierstrass_equation.b2, weierstrass_equation.b4],
    ring_char2,
  },
  unfold weierstrass_equation.j,
  rw hc4,
  by_cases ha1 : E.a1 = 0, {
    right,
    split, {
      rw ha1,
      ring,
    },
    use linear_change_of_variable.mk 1 E.a2 0 0 (by simp),
    unfold weierstrass_equation.is_model_of_char_2_j_zero
    linear_change_of_variable.change_curve
    weierstrass_equation.a1
    weierstrass_equation.a2
    linear_change_of_variable.u
    linear_change_of_variable.r
    linear_change_of_variable.s
    linear_change_of_variable.t,
    rw ha1,
    ring_char2,
  },
  left,
  split, {
    unfold weierstrass_equation.non_singular',
    intro hdisc,
    field_simp [ha1, hdisc],
  },
  use linear_change_of_variable.mk E.a1 (E.a3/E.a1) 0 ((E.a1^2*E.a4+E.a3^2)/E.a1^3) ha1,
  unfold weierstrass_equation.is_model_of_char_2_j_non_zero
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a3
  weierstrass_equation.a4
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { field_simp [ha1], },
  split, {
    field_simp [ha1], ring_char2,
  },
  field_simp [pow_succ, ha1], ring_char2,
end
