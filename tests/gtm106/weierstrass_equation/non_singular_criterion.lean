import algebra.field
import algebra.char_zero
import algebra.char_p
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.gtm106.weierstrass_equation.models_by_characteristic
import tests.testchar
import tests.testperfect
import tactic

noncomputable theory

def weierstrass_equation.is_singular_model
{K : Type*} [field K] (E : weierstrass_equation K) :=
E.a3 = 0 ∧ E.a4 = 0 ∧ E.a6 = 0

lemma weierstrass_equation.c4_of_singular_model {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_singular_model) :
E.c4 = E.b2^2 :=
begin
  unfold weierstrass_equation.c4
  weierstrass_equation.b2
  weierstrass_equation.b4,
  rw [h.1, h.2.1],
  ring,
end

lemma weierstrass_equation.disc_of_singular_model {K : Type*} [field K]
(E : weierstrass_equation K) (h : E.is_singular_model) :
E.disc = 0 :=
begin
  unfold weierstrass_equation.disc
  weierstrass_equation.b2
  weierstrass_equation.b4
  weierstrass_equation.b6
  weierstrass_equation.b8,
  rw [h.1, h.2.1, h.2.2],
  ring,
end

lemma weierstrass_equation.has_singular_model
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (hP : E.affine_point_singular P) :
∃ C : linear_change_of_variable K, (C.change_curve E).is_singular_model
∧ (C.change_affine_point P) = affine_plane_point.mk 0 0 :=
begin
  let C : linear_change_of_variable K := linear_change_of_variable.mk 1 P.x 0 P.y (by simp),
  use C,
  rw E.change_curve_preserve_affine_singular_point C at hP,
  set E' : weierstrass_equation K := C.change_curve E,
  set P' := C.change_affine_point P with hP',
  unfold linear_change_of_variable.change_affine_point at hP',
  simp at hP',
  split, {
    rw affine_plane_point.ext_iff at hP',
    unfold affine_plane_point.x
    affine_plane_point.y at hP',
    unfold weierstrass_equation.affine_point_singular
    weierstrass_equation.affine_point_on_curve
    weierstrass_equation.eval_at_affine_point
    weierstrass_equation.eval_dx_at_affine_point
    weierstrass_equation.eval_dy_at_affine_point at hP,
    rw [hP'.1, hP'.2] at hP,
    simp [zero_pow] at hP,
    exact ⟨ hP.2.2, hP.2.1, hP.1 ⟩,
  },
  exact hP',
end

lemma weierstrass_equation.disc_non_zero_implies_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :
E.non_singular' → E.non_singular :=
begin
  contrapose,
  rw E.singular_iff_has_affine_singular_point,
  rintros ⟨ P, hP ⟩,
  rcases E.has_singular_model P hP with ⟨ C, h2, h3 ⟩,
  rw C.preserve_non_singular',
  set E' : weierstrass_equation K := C.change_curve E,
  intro h1,
  exact h1 (E'.disc_of_singular_model h2),
end

lemma weierstrass_equation.non_singular_implies_disc_non_zero
{K : Type*} [field K] (E : weierstrass_equation K) (hperfect : ring_char K = 2 ∨ ring_char K = 3 → my_perfect_field K):
E.non_singular → E.non_singular' :=
begin
  by_cases hchar2 : ring_char K = 2, {
    replace hperfect : nth_power_surjective K 2 := by {
      have h := hperfect (by { left, exact hchar2, }),
      unfold my_perfect_field at h,
      rw hchar2 at h,
      cases h with h h, { contradiction, },
      exact h,
    },
    rcases E.have_model_of_char_2 hchar2 with ⟨ hj, C, ha1, ha3, ha4 ⟩ | ⟨ hj, C, ha1, ha2 ⟩, {
      rw C.preserve_non_singular E,
      rw C.preserve_non_singular' E,
      rw weierstrass_equation.non_singular_iff_affine_non_singular,
      set E' := C.change_curve E with hE,
      intros hsmooth hdisc,
      rw E'.disc_of_model_of_char_2_j_non_zero ⟨ ha1, ha3, ha4 ⟩ hchar2 at hdisc,
      let P : affine_plane_point K := affine_plane_point.mk 0 0,
      have hP : E'.affine_point_on_curve P := by {
        unfold weierstrass_equation.affine_point_on_curve
        weierstrass_equation.eval_at_affine_point
        affine_plane_point.x
        affine_plane_point.y,
        rw [ha1, ha3, ha4, hdisc],
        simp [zero_pow],
      },
      replace hsmooth := (hsmooth P hP).2,
      unfold weierstrass_equation.eval_dx_at_affine_point
      weierstrass_equation.eval_dy_at_affine_point
      affine_plane_point.x
      affine_plane_point.y at hsmooth,
      rw [ha1, ha3, ha4] at hsmooth,
      simp [zero_pow] at hsmooth,
      exact hsmooth,
    }, {
      rw C.preserve_non_singular E,
      rw C.preserve_non_singular' E,
      rw weierstrass_equation.non_singular_iff_affine_non_singular,
      set E' := C.change_curve E with hE,
      intros hsmooth hdisc,
      rw E'.disc_of_model_of_char_2_j_zero ⟨ ha1, ha2 ⟩ hchar2 at hdisc,
      field_simp at hdisc,
      cases hperfect E'.a4 with x hx,
      cases hperfect (x^3+E'.a4*x+E'.a6) with y hy,
      let P := affine_plane_point.mk x y,
      have hP : E'.affine_point_on_curve P := by {
        unfold weierstrass_equation.affine_point_on_curve
        weierstrass_equation.eval_at_affine_point
        affine_plane_point.x
        affine_plane_point.y,
        rw [ha1, ha2, hdisc, hy],
        ring,
      },
      replace hsmooth := (hsmooth P hP).2,
      unfold weierstrass_equation.eval_dx_at_affine_point
      weierstrass_equation.eval_dy_at_affine_point
      affine_plane_point.x
      affine_plane_point.y at hsmooth,
      rw [ha1, ha2, hdisc, hx] at hsmooth,
      have h := cong_char_is_eq hchar2 3 (-1) (by norm_num), norm_cast at h, rw h at hsmooth, clear h,
      have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h at hsmooth, clear h,
      simp at hsmooth,
      exact hsmooth,
    },
  },
  rcases E.have_model_of_char_neq_2 hchar2 with ⟨ C, ha1, ha3 ⟩,
  rw C.preserve_non_singular E,
  rw C.preserve_non_singular' E,
  rw weierstrass_equation.non_singular_iff_affine_non_singular,
  set E' := C.change_curve E with hE,
  intros hsmooth hdisc,
  let f : monic_cubic_poly K := monic_cubic_poly.mk E'.a2 E'.a4 E'.a6,
  have hdisc' : E'.disc = 16*f.disc := by {
    rw E'.disc_of_model_of_char_neq_2 ⟨ ha1, ha3 ⟩,
    unfold monic_cubic_poly.disc,
    ring,
  },
  have h16 := power_of_prime_neq_char_is_non_zero K 16 2 4 (by norm_num) (by norm_num) hchar2,
  norm_num at h16,
  field_simp [hdisc, h16] at hdisc',
  rcases f.disc_zero_implies_has_multiple_root hperfect hdisc' with ⟨ x, h1, h2 ⟩,
  unfold monic_cubic_poly.eval_at
  monic_cubic_poly.a
  monic_cubic_poly.b
  monic_cubic_poly.c at h1,
  replace h1 := calc x^3 = -E'.a2*x^2 - E'.a4*x - E'.a6 + (x^3 + E'.a2*x^2 + E'.a4*x + E'.a6) : by ring
  ... = -E'.a2*x^2 - E'.a4*x - E'.a6 : by { rw h1, ring, },
  unfold monic_cubic_poly.eval_dx_at
  monic_cubic_poly.a
  monic_cubic_poly.b at h2,
  replace h2 := calc 3*x^2 = -2*E'.a2*x - E'.a4 + (3*x^2 + 2*E'.a2*x + E'.a4) : by ring
  ... = -2*E'.a2*x - E'.a4 : by { rw h2, ring, },
  let P := affine_plane_point.mk x 0,
  have hP : E'.affine_point_on_curve P := by {
    unfold weierstrass_equation.affine_point_on_curve
    weierstrass_equation.eval_at_affine_point
    affine_plane_point.x
    affine_plane_point.y,
    rw [h1, ha1, ha3], ring,
  },
  replace hsmooth := (hsmooth P hP).2,
  unfold weierstrass_equation.eval_dx_at_affine_point
  weierstrass_equation.eval_dy_at_affine_point
  affine_plane_point.x
  affine_plane_point.y at hsmooth,
  rw [h2, ha1, ha3] at hsmooth,
  simp at hsmooth,
  exact hsmooth,
end

lemma weierstrass_equation.at_most_one_singular_point
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : affine_plane_point K)
(hP : E.affine_point_singular P) (hP' : E.affine_point_singular P') : P = P' :=
begin
  rcases E.has_singular_model P hP with ⟨ C, hsing, h0 ⟩,
  rw ← linear_change_of_variable.change_affine_point.id P,
  rw ← linear_change_of_variable.change_affine_point.id P',
  rw ← C.comp_inv,
  repeat { rw ← linear_change_of_variable.change_affine_point.comp },
  rw E.change_curve_preserve_affine_singular_point C _ at hP hP',
  set Q := C.change_affine_point P,
  set Q' := C.change_affine_point P',
  set E' := C.change_curve E,
  congr,
  rw [h0, affine_plane_point.ext_iff],
  unfold affine_plane_point.x affine_plane_point.y,
  unfold weierstrass_equation.affine_point_singular
  weierstrass_equation.affine_point_on_curve
  weierstrass_equation.eval_at_affine_point
  weierstrass_equation.eval_dx_at_affine_point
  weierstrass_equation.eval_dy_at_affine_point at hP',
  rw [hsing.1, hsing.2.1, hsing.2.2] at hP',
  simp at hP',
  rcases hP' with ⟨ h1, h2, h3 ⟩,
  by_cases hx : Q'.x = 0, {
    rw hx at h1,
    field_simp [zero_pow] at h1,
    exact ⟨ hx.symm, h1.symm ⟩,
  },
  exfalso,
  have h4 := calc Q'.x * (E'.a1 * Q'.y - 2 * E'.a2 * Q'.x)
  = 6 * (Q'.y ^ 2 + E'.a1 * Q'.x * Q'.y - Q'.x ^ 3 - E'.a2 * Q'.x ^ 2)
  - 2 * Q'.x * (E'.a1 * Q'.y - 3 * Q'.x ^ 2 - 2 * E'.a2 * Q'.x)
  - 3 * Q'.y * (2 * Q'.y + E'.a1 * Q'.x) : by ring
  ... = 0 : by { rw [h1, h2, h3], ring, },
  field_simp [hx] at h4,
  have hchar3 := calc 3 * Q'.x ^ 2 = (E'.a1 * Q'.y - 2 * E'.a2 * Q'.x)
  - (E'.a1 * Q'.y - 3 * Q'.x ^ 2 - 2 * E'.a2 * Q'.x) : by ring
  ... = 0 : by { rw [h2, h4], ring, },
  field_simp [hx] at hchar3,
  replace h3 := calc Q'.y = Q'.y + (2 * Q'.y + E'.a1 * Q'.x) : by { rw h3, ring, }
  ... = E'.a1 * Q'.x : by { ring, rw hchar3, ring, },
  rw h3 at h4, ring at h4,
  replace h4 := calc Q'.x * (E'.a1 ^ 2 + (1 - 3) * E'.a2) = Q'.x * E'.a1 ^ 2 - 2 * E'.a2 * Q'.x : by ring
  ... = 0 : h4,
  rw hchar3 at h4,
  field_simp [hx] at h4,
  replace h4 := calc E'.a2 = -E'.a1 ^ 2 + (E'.a1 ^ 2 + E'.a2) : by ring
  ... = -E'.a1 ^ 2 : by { rw h4, ring, },
  rw [h3, h4] at h1,
  replace h1 := calc (3 * E'.a1^2 - Q'.x) * Q'.x ^ 2
  = (E'.a1 * Q'.x) ^ 2 + E'.a1 * Q'.x * (E'.a1 * Q'.x) - Q'.x ^ 3 - -E'.a1 ^ 2 * Q'.x ^ 2 : by ring
  ... = 0 : h1,
  rw hchar3 at h1,
  field_simp [hx] at h1,
  exact h1,
end

lemma weierstrass_equation.singular_implies_has_node_or_cusp
{K : Type*} [field K] (E : weierstrass_equation K) :
¬ E.non_singular → (¬ E.has_node ↔ E.has_cusp) :=
begin
  rw E.singular_iff_has_affine_singular_point,
  rintros ⟨ P, hP ⟩,
  have hP' := E.singular_point_is_node_or_cusp P hP,
  split, {
    intro h,
    unfold weierstrass_equation.has_node at h,
    push_neg at h,
    replace hP' := hP'.1 (h P),
    exact ⟨ P, hP' ⟩,
  },
  rintros ⟨ P1, h1 ⟩ ⟨ P2, h2 ⟩,
  have := E.at_most_one_singular_point P1 P h1.1 hP,
  rw this at h1,
  have := E.at_most_one_singular_point P2 P h2.1 hP,
  rw this at h2,
  finish,
end
