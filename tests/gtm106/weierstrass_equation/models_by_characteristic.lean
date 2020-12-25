import algebra.field
import algebra.char_zero
import algebra.char_p
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.testchar
import tactic

noncomputable theory

lemma weierstrass_equation.model_of_char_neq_2 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K ≠ 2)
: ∃ (C : linear_change_of_variable K),
(C.change_curve E).a1 = 0 ∧ (C.change_curve E).a3 = 0 :=
begin
  replace hchar2 := prime_neq_char_is_non_zero K 2 (by norm_num) hchar2,
  norm_cast at hchar2,
  let C : linear_change_of_variable K := linear_change_of_variable.mk 1 0 (-E.a1/2) (-E.a3/2) (by simp),
  use C,
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a3
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  field_simp [hchar2],
  simp [mul_comm],
end

lemma weierstrass_equation.model_of_char_neq_2_and_3 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K ≠ 2) (hchar3 : ring_char K ≠ 3)
: ∃ (C : linear_change_of_variable K),
(C.change_curve E).a1 = 0 ∧ (C.change_curve E).a2 = 0 ∧ (C.change_curve E).a3 = 0 :=
begin
  rcases E.model_of_char_neq_2 hchar2 with ⟨ C, h1 ⟩,
  set E' := C.change_curve E with hE,
  replace hchar3 := prime_neq_char_is_non_zero K 3 (by norm_num) hchar3,
  norm_cast at hchar3,
  let C' : linear_change_of_variable K := linear_change_of_variable.mk 1 (-E'.a2/3) 0 0 (by simp),
  use C.composite C',
  rw [← linear_change_of_variable.change_curve.comp, ← hE],
  unfold linear_change_of_variable.change_curve
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

lemma weierstrass_equation.model_of_char_3 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar3 : ring_char K = 3)
: ((E.non_singular → E.j ≠ 0) ∧ ∃ (C : linear_change_of_variable K),
(C.change_curve E).a1 = 0 ∧ (C.change_curve E).a3 = 0 ∧ (C.change_curve E).a4 = 0)
∨ (E.j = 0 ∧ ∃ (C : linear_change_of_variable K),
(C.change_curve E).a1 = 0 ∧ (C.change_curve E).a2 = 0 ∧ (C.change_curve E).a3 = 0) :=
begin
  have hchar2 : ring_char K ≠ 2 := by {
    rw hchar3, norm_num,
  },
  rcases E.model_of_char_neq_2 hchar2 with ⟨ C, h1 ⟩,
  set E' := C.change_curve E with hE,
  have hdisc : E'.disc = E'.a2^2*E'.a4^2 -E'.a2^3*E'.a6 -E'.a4^3 := by {
    unfold weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [h1.1, h1.2],
    simp [zero_pow],
    ring,
    have h := cong_char_is_eq hchar3 64 1 (by norm_num), norm_cast at h, rw h, clear h,
    have h := cong_char_is_eq hchar3 16 1 (by norm_num), norm_cast at h, rw h, clear h,
    have h := dvd_char_is_zero hchar3 288 (by norm_num), norm_cast at h, rw h, clear h,
    have h := dvd_char_is_zero hchar3 432 (by norm_num), norm_cast at h, rw h, clear h,
    ring,
  },
  have hc4 : E'.c4 = E'.a2^2 := by {
    unfold weierstrass_equation.c4
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4,
    rw h1.1,
    have h := dvd_char_is_zero hchar3 24 (by norm_num), norm_cast at h, rw h, clear h,
    have h := cong_char_is_eq hchar3 4 1 (by norm_num), norm_cast at h, rw h, clear h,
    ring,
  },
  have hj : E'.j = E.j := C.j E,
  have hnonsing : E.non_singular ↔ E'.non_singular := C.preserve_non_singular E,
  rw [← hj, hnonsing],
  unfold weierstrass_equation.j
  weierstrass_equation.non_singular,
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
  unfold linear_change_of_variable.change_curve
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
  ring,
  have h := dvd_char_is_zero hchar3 3 (by norm_num), norm_cast at h, rw h, clear h,
  ring,
end

lemma weierstrass_equation.model_of_char_2 {K : Type*} [field K]
(E : weierstrass_equation K) (hchar2 : ring_char K = 2)
: ((E.non_singular → E.j ≠ 0) ∧ ∃ (C : linear_change_of_variable K),
(C.change_curve E).a1 = 1 ∧ (C.change_curve E).a3 = 0 ∧ (C.change_curve E).a4 = 0)
∨ (E.j = 0 ∧ ∃ (C : linear_change_of_variable K),
(C.change_curve E).a1 = 0 ∧ (C.change_curve E).a2 = 0) :=
begin
  have hc4 : E.c4 = E.a1^4 := by {
    unfold weierstrass_equation.c4
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4,
    have h := dvd_char_is_zero hchar2 4 (by norm_num), norm_cast at h, rw h, clear h,
    have h := dvd_char_is_zero hchar2 24 (by norm_num), norm_cast at h, rw h, clear h,
    ring,
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
    unfold linear_change_of_variable.change_curve
    weierstrass_equation.a1
    weierstrass_equation.a2
    linear_change_of_variable.u
    linear_change_of_variable.r
    linear_change_of_variable.s
    linear_change_of_variable.t,
    rw ha1,
    have h := cong_char_is_eq hchar2 3 (-1) (by norm_num), norm_cast at h, rw h, clear h,
    split, { ring, }, simp,
  },
  left,
  split, {
    unfold weierstrass_equation.non_singular,
    intro hdisc,
    field_simp [ha1, hdisc],
  },
  use linear_change_of_variable.mk E.a1 (E.a3/E.a1) 0 ((E.a1^2*E.a4+E.a3^2)/E.a1^3) ha1,
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a3
  weierstrass_equation.a4
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { field_simp [ha1], },
  split, {
    field_simp [ha1], ring,
    have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h, clear h,
    ring,
  },
  field_simp [pow_succ, ha1], ring,
  have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h, clear h,
  ring,
end
