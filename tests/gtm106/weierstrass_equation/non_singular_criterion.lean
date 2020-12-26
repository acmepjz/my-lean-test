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

lemma weierstrass_equation.disc_non_zero_implies_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :
E.non_singular' → E.non_singular :=
begin
  rw E.non_singular_iff_affine_non_singular,
  intro h1,
  by_cases h : ∃ P : affine_plane_point K, E.affine_point_on_curve P ∧ ¬ E.affine_point_regular P, {
    exfalso,
    rcases h with ⟨ P, h2, h3 ⟩,
    let C : linear_change_of_variable K := linear_change_of_variable.mk 1 P.x 0 P.y (calc (1 : K) ≠ 0 : one_ne_zero),
    let E' : weierstrass_equation K := C.change_curve E,
    set! P' := C.change_affine_point P with hP',
    unfold linear_change_of_variable.change_affine_point at hP',
    rw affine_plane_point.ext_iff at hP',
    unfold affine_plane_point.x
    affine_plane_point.y at hP',
    simp at hP',
    cases hP' with hP'x hP'y,
    rw E.change_curve_preserve_affine_point C P at h2,
    replace h2 : E'.affine_point_on_curve P' := h2,
    rw E.change_curve_preserve_affine_regular_point C P at h3,
    replace h3 : ¬ E'.affine_point_regular P' := h3,
    unfold weierstrass_equation.affine_point_regular at h3,
    push_neg at h3,
    replace h3 := h3 h2,
    unfold weierstrass_equation.affine_point_on_curve
    weierstrass_equation.eval_at_affine_point at h2,
    rw [hP'x, hP'y] at h2,
    field_simp [zero_pow] at h2,
    unfold weierstrass_equation.eval_dx_at_affine_point
    weierstrass_equation.eval_dy_at_affine_point at h3,
    rw [hP'x, hP'y] at h3,
    field_simp [zero_pow] at h3,
    rw C.preserve_non_singular' at h1,
    replace h1 : E'.non_singular' := h1,
    unfold weierstrass_equation.non_singular'
    weierstrass_equation.disc
    weierstrass_equation.b8
    weierstrass_equation.b6
    weierstrass_equation.b4
    weierstrass_equation.b2 at h1,
    rw [h2, h3.1, h3.2] at h1,
    field_simp [zero_pow] at h1,
    exact h1,
  },
  push_neg at h,
  exact h,
end

lemma weierstrass_equation.non_singular_implies_disc_non_zero
{K : Type*} [field K] (E : weierstrass_equation K) (hperfect : ring_char K = 2 → my_perfect_field K):
E.non_singular → E.non_singular' :=
begin
  by_cases hchar2 : ring_char K = 2, {
    replace hperfect : nth_power_surjective K 2 := by {
      have h := hperfect hchar2,
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
  set E' := C.change_curve E with hE,
  intros hsmooth hdisc,
  rw E'.disc_of_model_of_char_neq_2 ⟨ ha1, ha3 ⟩ at hdisc,
  -- TODO: construct a singular point for E'
  sorry,
end
