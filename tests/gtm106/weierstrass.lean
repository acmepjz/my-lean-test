import algebra.field
import algebra.char_zero
import algebra.char_p
import data.int.basic
import data.rat.basic
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.gtm106.weierstrass_equation.models_by_characteristic
import tests.testchar
import tactic

noncomputable theory

lemma weierstrass_equation.smooth_iff_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :
E.smooth ↔ E.non_singular :=
begin
  split, {
    by_cases hchar2 : ring_char K = 2, {
      rcases E.model_of_char_2 hchar2 with ⟨ hj, C, ha1, ha3, ha4 ⟩ | ⟨ hj, C, ha1, ha2 ⟩, {
        rw C.preserve_smooth E,
        rw C.preserve_non_singular E,
        rw weierstrass_equation.smooth_iff_affine_smooth,
        set E' := C.change_curve E with hE,
        intros hsmooth hdisc,
        have hdisc' : E'.disc = E'.a6 := by {
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
          rw [ha1, ha3, ha4],
          simp [zero_pow],
          have h := dvd_char_is_zero hchar2 4 (by norm_num), norm_cast at h, rw h, clear h,
          ring,
          calc -E'.a6 = E'.a6 - 2*E'.a6 : by ring
          ... = E'.a6 : by {
            have h := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h, rw h, clear h,
            ring,
          },
        },
        rw hdisc' at hdisc,
        let P : affine_plane_point K := affine_plane_point.mk 0 0,
        replace hsmooth := hsmooth P,
        unfold weierstrass_equation.affine_point_on_curve
        weierstrass_equation.affine_point_smooth
        weierstrass_equation.eval_at_affine_point
        weierstrass_equation.eval_dx_at_affine_point
        weierstrass_equation.eval_dy_at_affine_point
        affine_plane_point.x
        affine_plane_point.y at hsmooth,
        rw [ha1, ha3, ha4, hdisc] at hsmooth,
        simp [zero_pow] at hsmooth,
        exact hsmooth,
      }, {
        rw C.preserve_smooth E,
        rw C.preserve_non_singular E,
        rw weierstrass_equation.smooth_iff_affine_smooth,
        set E' := C.change_curve E with hE,
        intros hsmooth hdisc,
        have hdisc' : E'.disc = E'.a3^4 := by {
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
          rw [ha1, ha2],
          simp [zero_pow],
          ring,
          have h := dvd_char_is_zero hchar2 64 (by norm_num), norm_cast at h, rw h, clear h,
          have h := dvd_char_is_zero hchar2 432 (by norm_num), norm_cast at h, rw h, clear h,
          have h := dvd_char_is_zero hchar2 216 (by norm_num), norm_cast at h, rw h, clear h,
          have h := cong_char_is_eq hchar2 27 (-1) (by norm_num), norm_cast at h, rw h, clear h,
          ring, simp,
        },
        rw hdisc' at hdisc,
        field_simp at hdisc,
        -- ERROR: in this case the singular point is defined over an algebraic extension of K
        sorry,
      },
    },
    rcases E.model_of_char_neq_2 hchar2 with ⟨ C, ha1, ha3 ⟩,
    rw C.preserve_smooth E,
    rw C.preserve_non_singular E,
    set E' := C.change_curve E with hE,
    intros hsmooth hdisc,
    -- TODO: construct a singular point for E'
    sorry,
  },
  rw E.smooth_iff_affine_smooth,
  intro h1,
  by_cases h : ∃ P : affine_plane_point K, E.affine_point_on_curve P ∧ ¬ E.affine_point_smooth P, {
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
    rw E.change_curve_preserve_affine_smooth_point C P at h3,
    replace h3 : ¬ E'.affine_point_smooth P' := h3,
    unfold weierstrass_equation.affine_point_smooth at h3,
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
    rw C.preserve_non_singular at h1,
    replace h1 : E'.non_singular := h1,
    unfold weierstrass_equation.non_singular
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

lemma exists_j0 : ∃ E : weierstrass_equation ℚ, E.non_singular ∧ E.j = 0 :=
begin
  use [0, 0, 0, 0, -1],
  split, {
    unfold weierstrass_equation.non_singular
    weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    norm_num,
  }, {
    unfold weierstrass_equation.j
    weierstrass_equation.c4
    weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    norm_num,
  },
end

lemma exists_j1728 : ∃ E : weierstrass_equation ℚ, E.non_singular ∧ E.j = 1728 :=
begin
  use [0, 0, 0, -1, 0],
  split, {
    unfold weierstrass_equation.non_singular
    weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    norm_num,
  }, {
    unfold weierstrass_equation.j
    weierstrass_equation.c4
    weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    norm_num,
  },
end

lemma exists_j (j : ℚ) : ∃ E : weierstrass_equation ℚ, E.non_singular ∧ E.j = j :=
begin
  by_cases h0 : j = 0, {
    rw h0, exact exists_j0,
  },
  by_cases h1728 : j = 1728, {
    rw h1728, exact exists_j1728,
  },
  replace h1728 : j-1728 ≠ 0 := sub_ne_zero.mpr h1728,
  let E := weierstrass_equation.mk (j-1728) 0 0 (-36*(j-1728)^3) (-(j-1728)^5),
  have h_non_singular : E.disc ≠ 0 := by {
    calc E.disc = j^2 * (j-1728)^9 : by {
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
      ring,
    }
    ... ≠ 0 : by {
      field_simp [h0, h1728],
    },
  },
  use E,
  use h_non_singular,
  unfold weierstrass_equation.j,
  field_simp [h_non_singular],
  unfold weierstrass_equation.c4
  weierstrass_equation.disc
  weierstrass_equation.b2
  weierstrass_equation.b4
  weierstrass_equation.b6
  weierstrass_equation.b8
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6,
  ring,
end

/-
example (j : ℚ) (h0 : j ≠ 0) (h1728 : j-1728 ≠ 0) :
((-36) / (j - 1728)) ^ 2 - (-1) / (j - 1728) - 8 * (2 * ((-36) / (j - 1728))) ^ 3 - 27 * (4 * ((-1) / (j - 1728))) ^ 2 + 9 * (2 * ((-36) / (j - 1728))) * (4 * ((-1) / (j - 1728))) ≠ 0 :=
begin
  calc ((-36) / (j - 1728)) ^ 2 - (-1) / (j - 1728) - 8 * (2 * ((-36) / (j - 1728))) ^ 3 - 27 * (4 * ((-1) / (j - 1728))) ^ 2 + 9 * (2 * ((-36) / (j - 1728))) * (4 * ((-1) / (j - 1728)))
  = j^2 / (j-1728)^3 : by {
    field_simp [pow_succ, h1728],
    ring,
  }
  ... ≠ 0 : by {
    field_simp [h1728, h0],
  },
end
-/
