import algebra.field
import algebra.char_zero
import algebra.char_p
import gtm106.naive_plane
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.linear_change_of_variable
import gtm106.weierstrass_equation.models_by_characteristic
import myhelper.char
import myhelper.perfect
import tactic

namespace weierstrass_equation

/--
`Prop` that a Weierstrass equation is singular with singular point `(0,0)`.
-/
def is_singular_model
{K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.a3 = 0 ∧ E.a4 = 0 ∧ E.a6 = 0

@[simp]
lemma c4_of_singular_model {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_singular_model) :
E.c4 = E.b2^2 :=
begin
  simp [c4, b2, b4, h.1, h.2.1],
end

@[simp]
lemma disc_of_singular_model {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (h : E.is_singular_model) :
E.disc = 0 :=
begin
  simp [disc, b2, b4, b6, b8, h.1, h.2.1, h.2.2],
end

lemma has_singular_model
{K : Type*} [field K] (E : weierstrass_equation K)
(P : affine_plane_point K) (hP : E.affine_point_singular P) :
∃ C : linear_change_of_variable K, (C.change_curve E).is_singular_model
∧ (C.change_affine_point P) = ⟨ 0, 0 ⟩ :=
begin
  let C : linear_change_of_variable K := ⟨ 1, P.x, 0, P.y, by simp ⟩,
  use C,
  rw C.preserve_affine_singular_point E at hP,
  set E' := C.change_curve E with hE', clear_value E',
  set P' := C.change_affine_point P with hP', clear_value P',
  simp [linear_change_of_variable.change_affine_point] at hP',
  split, {
    simp [affine_plane_point.ext_iff] at hP',
    simp [affine_point_singular,
      affine_point_on_curve,
      eval_at_affine_point,
      eval_dx_at_affine_point,
      eval_dy_at_affine_point,
      hP'.1, hP'.2, zero_pow] at hP,
    exact ⟨ hP.2.2, hP.2.1, hP.1 ⟩,
  },
  exact hP',
end

/--
If a Weierstrass equation has non-zero discriminant,
then it does not have rational singular point.
-/
lemma disc_non_zero_implies_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :
E.non_singular' → E.non_singular :=
begin
  contrapose,
  rw E.singular_iff_has_affine_singular_point,
  rintros ⟨ P, hP ⟩,
  rcases E.has_singular_model P hP with ⟨ C, h2, h3 ⟩,
  rw C.preserve_non_singular',
  set E' : weierstrass_equation K := C.change_curve E, clear_value E',
  simp [non_singular', h2],
end

lemma non_singular_implies_disc_non_zero.char_2_case
{K : Type*} [field K] (E : weierstrass_equation K)
(hperfect : (ring_char K = 2 ∨ ring_char K = 3) ∧ E.c4 = 0 → my_perfect_field K)
(hchar2 : ring_char K = 2) :
E.non_singular → E.non_singular' :=
begin
  rcases E.have_model_of_char_2 hchar2 with ⟨ hj, C, ha1, ha3, ha4 ⟩ | ⟨ hj, C, ha1, ha2 ⟩, {
    rw [C.preserve_non_singular E, C.preserve_non_singular' E,
      non_singular_iff_affine_non_singular],
    set E' := C.change_curve E with hE, clear_value E',
    intros hsmooth hdisc,
    rw E'.disc_of_model_of_char_2_j_non_zero ⟨ ha1, ha3, ha4 ⟩ hchar2 at hdisc,
    let P : affine_plane_point K := ⟨ 0, 0 ⟩,
    have hP : E'.affine_point_on_curve P := by {
      simp [affine_point_on_curve,
        eval_at_affine_point,
        ha1, ha3, ha4, hdisc],
    },
    replace hsmooth := (hsmooth P hP).2,
    simp [eval_dx_at_affine_point,
      eval_dy_at_affine_point,
      ha1, ha3, ha4] at hsmooth,
    exact hsmooth,
  }, {
    replace hperfect : nth_power_surjective K 2 := by {
      have hc4 := (C.change_curve E).c4_of_model_of_char_2_j_zero ⟨ ha1, ha2 ⟩ hchar2,
      simp at hc4,
      simp [hchar2, hc4, my_perfect_field] at hperfect,
      exact hperfect,
    },
    rw [C.preserve_non_singular E, C.preserve_non_singular' E,
      non_singular_iff_affine_non_singular],
    set E' := C.change_curve E with hE, clear_value E',
    intros hsmooth hdisc,
    simp [E'.disc_of_model_of_char_2_j_zero ⟨ ha1, ha2 ⟩ hchar2] at hdisc,
    cases hperfect E'.a4 with x hx,
    cases hperfect (x^3+E'.a4*x+E'.a6) with y hy,
    have hP : E'.affine_point_on_curve ⟨ x, y ⟩ := by {
      simp [affine_point_on_curve,
        eval_at_affine_point,
        ha1, ha2, hdisc, hy],
      ring,
    },
    replace hsmooth := (hsmooth _ hP).2,
    simp [eval_dx_at_affine_point,
      eval_dy_at_affine_point,
      ha1, ha2, hdisc, hx] at hsmooth,
    ring_nf at hsmooth,
    ring_char2 at hsmooth,
    exact hsmooth,
  },
end

lemma non_singular_implies_disc_non_zero.char_neq_2_case
{K : Type*} [field K] (E : weierstrass_equation K)
(hperfect : (ring_char K = 2 ∨ ring_char K = 3) ∧ E.c4 = 0 → my_perfect_field K)
(hchar2 : ring_char K ≠ 2) :
E.non_singular → E.non_singular' :=
begin
  rcases E.have_model_of_char_neq_2 hchar2 with ⟨ C, ha1, ha3 ⟩,
  rw [C.preserve_non_singular E, C.preserve_non_singular' E,
    non_singular_iff_affine_non_singular],
  set E' := C.change_curve E with hE, clear_value E',
  intros hsmooth hdisc,
  let f : monic_cubic_poly K := ⟨ E'.a2, E'.a4, E'.a6 ⟩,
  have hdisc' : E'.disc = 16*f.disc := by {
    rw E'.disc_of_model_of_char_neq_2 ⟨ ha1, ha3 ⟩,
    unfold monic_cubic_poly.disc,
    ring,
  },
  have h16 := power_of_prime_neq_char_is_non_zero K 16 2 4 (by norm_num) (by norm_num) hchar2,
  norm_num at h16,
  simp [hdisc, h16] at hdisc',
  replace hperfect : ring_char K = 2 ∨ (ring_char K = 3 ∧ f.a = 0) → my_perfect_field K := by {
    by_cases hchar3 : ring_char K = 3, {
      intro h,
      simp [hchar2, hchar3] at h,
      replace h : E'.c4 = 0 := by {
        rw [E'.c4_of_model_of_char_neq_2 ⟨ ha1, ha3 ⟩, h],
        ring_char3,
      },
      simp [hE] at h,
      simp [hchar3, h] at hperfect,
      exact hperfect,
    },
    simp [hchar2, hchar3],
  },
  rcases f.disc_zero_implies_has_multiple_root hperfect hdisc' with ⟨ x, h1, h2 ⟩,
  replace h1 := calc x^3
  = -E'.a2*x^2 - E'.a4*x - E'.a6 + f.eval_at x : by { simp [monic_cubic_poly.eval_at], }
  ... = -E'.a2*x^2 - E'.a4*x - E'.a6 : by { simp [h1], },
  replace h2 := calc 3*x^2 = -2*E'.a2*x - E'.a4 + f.eval_dx_at x : by { simp [monic_cubic_poly.eval_dx_at], }
  ... = -2*E'.a2*x - E'.a4 : by { simp [h2], },
  let P := affine_plane_point.mk x 0,
  have hP : E'.affine_point_on_curve P := by {
    simp [affine_point_on_curve,
      eval_at_affine_point,
      h1, ha1, ha3], ring,
  },
  replace hsmooth := (hsmooth P hP).2,
  simp [eval_dx_at_affine_point,
    eval_dy_at_affine_point,
    h2, ha1, ha3] at hsmooth,
  exact hsmooth,
end

/--
If a Weierstrass equation has no rational singular point,
under the assumption that the field is not of characteristic 2 or 3, or is perfect,
the Weierstrass equation is of non-zero discriminant.

NOTE: When the field is of characteristic 2 or 3, the singular point
may be defined over a finite inseparable extension.
-/
lemma non_singular_implies_disc_non_zero
{K : Type*} [field K] (E : weierstrass_equation K)
(hperfect : (ring_char K = 2 ∨ ring_char K = 3) ∧ E.c4 = 0 → my_perfect_field K) :
E.non_singular → E.non_singular' :=
begin
  by_cases hchar2 : ring_char K = 2, {
    exact non_singular_implies_disc_non_zero.char_2_case E hperfect hchar2,
  },
  exact non_singular_implies_disc_non_zero.char_neq_2_case E hperfect hchar2,
end

/--
A Weierstrass equation has at most one singular point.
-/
lemma at_most_one_singular_point
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : affine_plane_point K)
(hP : E.affine_point_singular P) (hP' : E.affine_point_singular P') : P = P' :=
begin
  rcases E.has_singular_model P hP with ⟨ C, hsing, h0 ⟩,
  rw ← linear_change_of_variable.change_affine_point.id P,
  rw ← linear_change_of_variable.change_affine_point.id P',
  rw ← C.inv_comp,
  repeat { rw ← linear_change_of_variable.change_affine_point.comp },
  rw C.preserve_affine_singular_point E _ at hP hP',
  set Q := C.change_affine_point P, clear_value Q,
  set Q' := C.change_affine_point P', clear_value Q',
  set E' := C.change_curve E, clear_value E',
  congr,
  simp [h0, affine_plane_point.ext_iff],
  simp [affine_point_singular,
    affine_point_on_curve,
    eval_at_affine_point,
    eval_dx_at_affine_point,
    eval_dy_at_affine_point,
    hsing.1, hsing.2.1, hsing.2.2] at hP',
  rcases hP' with ⟨ h1, h2, h3 ⟩,
  by_cases hx : Q'.x = 0, {
    simp [hx, zero_pow] at h1,
    exact ⟨ hx.symm, h1.symm ⟩,
  },
  exfalso,
  have h4 := calc Q'.x * (E'.a1 * Q'.y - 2 * E'.a2 * Q'.x)
  = 6 * (Q'.y ^ 2 + E'.a1 * Q'.x * Q'.y - Q'.x ^ 3 - E'.a2 * Q'.x ^ 2)
  - 2 * Q'.x * (E'.a1 * Q'.y - 3 * Q'.x ^ 2 - 2 * E'.a2 * Q'.x)
  - 3 * Q'.y * (2 * Q'.y + E'.a1 * Q'.x) : by ring
  ... = 0 : by { rw [h1, h2, h3], ring, },
  simp [hx] at h4,
  have hchar3 := calc 3 * Q'.x ^ 2 = (E'.a1 * Q'.y - 2 * E'.a2 * Q'.x)
  - (E'.a1 * Q'.y - 3 * Q'.x ^ 2 - 2 * E'.a2 * Q'.x) : by ring
  ... = 0 : by { rw [h2, h4], ring, },
  simp [hx] at hchar3,
  replace h3 := calc Q'.y = Q'.y + (2 * Q'.y + E'.a1 * Q'.x) : by { simp [h3], }
  ... = E'.a1 * Q'.x : by { ring_nf, simp [hchar3], },
  replace h4 := calc Q'.x * (E'.a1 ^ 2 + (1 - 3) * E'.a2)
  = E'.a1 * Q'.y - 2 * E'.a2 * Q'.x : by { rw h3, ring, }
  ... = 0 : h4,
  simp [hchar3, hx] at h4,
  replace h4 := calc E'.a2 = -E'.a1 ^ 2 + (E'.a1 ^ 2 + E'.a2) : by ring
  ... = -E'.a1 ^ 2 : by { rw h4, ring, },
  rw [h3, h4] at h1,
  replace h1 := calc (3 * E'.a1^2 - Q'.x) * Q'.x ^ 2
  = (E'.a1 * Q'.x) ^ 2 + E'.a1 * Q'.x * (E'.a1 * Q'.x) - Q'.x ^ 3 - -E'.a1 ^ 2 * Q'.x ^ 2 : by ring
  ... = 0 : h1,
  simp [hchar3, hx] at h1,
  exact h1,
end

lemma singular_implies_has_node_or_cusp
{K : Type*} [field K] (E : weierstrass_equation K) :
¬ E.non_singular → (¬ E.has_node ↔ E.has_cusp) :=
begin
  rw E.singular_iff_has_affine_singular_point,
  rintros ⟨ P, hP ⟩,
  have hP' := E.singular_point_is_node_or_cusp P hP,
  split, {
    intro h,
    unfold has_node at h,
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

/--
If a Weierstrass equation has a rational node,
then its discriminant is zero and `c4` is not zero.
-/
lemma has_node_implies_disc_zero_c4_non_zero
{K : Type*} [field K] (E : weierstrass_equation K) :
E.has_node → E.has_node' :=
begin
  rintros ⟨ P, hP, hH ⟩,
  rcases E.has_singular_model P hP with ⟨ C, h2, h3 ⟩,
  replace hH : (E.eval_hessian_at_affine_point P)/C.u^2 ≠ 0 := by {
    field_simp [hH],
  },
  rw ← C.eval_hessian_at_affine_point E P at hH,
  rw C.preserve_has_node' E,
  rw C.preserve_affine_singular_point E P at hP,
  set E' := C.change_curve E, clear_value E',
  set P' := C.change_affine_point P, clear_value P',
  have h := mt E'.disc_non_zero_implies_non_singular,
  rw E'.singular_iff_has_affine_singular_point at h,
  replace h := h ⟨ P', hP ⟩,
  simp [non_singular'] at h,
  use h,
  simp [affine_plane_point.ext_iff] at h3,
  simp [eval_hessian_at_affine_point, h3.1] at hH,
  simp [c4, b4, h2.1, h2.2.1, hH],
end

/--
If a Weierstrass equation has a rational cusp,
then its discriminant is zero and `c4` is also zero.
-/
lemma has_cusp_implies_disc_zero_c4_zero
{K : Type*} [field K] (E : weierstrass_equation K) :
E.has_cusp → E.has_cusp' :=
begin
  rintros ⟨ P, hP, hH ⟩,
  rcases E.has_singular_model P hP with ⟨ C, h2, h3 ⟩,
  replace hH : (E.eval_hessian_at_affine_point P)/C.u^2 = 0 := by {
    field_simp [hH],
  },
  rw ← C.eval_hessian_at_affine_point E P at hH,
  rw C.preserve_has_cusp' E,
  rw C.preserve_affine_singular_point E P at hP,
  set E' := C.change_curve E, clear_value E',
  set P' := C.change_affine_point P, clear_value P',
  have h := mt E'.disc_non_zero_implies_non_singular,
  rw E'.singular_iff_has_affine_singular_point at h,
  replace h := h ⟨ P', hP ⟩,
  simp [non_singular'] at h,
  use h,
  simp [affine_plane_point.ext_iff] at h3,
  simp [eval_hessian_at_affine_point, h3.1] at hH,
  simp [c4, b4, h2.1, h2.2.1, hH],
end

/--
If a Weierstrass is of discriminant zero and `c4` non-zero,
then it has a rational node.
-/
lemma disc_zero_c4_non_zero_implies_has_node
{K : Type*} [field K] (E : weierstrass_equation K) :
E.has_node' → E.has_node :=
begin
  rintros ⟨ hdisc, hc4 ⟩,
  have hperfect : (ring_char K = 2 ∨ ring_char K = 3) ∧ E.c4 = 0 → my_perfect_field K := by {
    simp [hc4],
  },
  have hsing := mt (E.non_singular_implies_disc_non_zero hperfect),
  rw E.singular_iff_has_affine_singular_point at hsing,
  simp [non_singular', hdisc] at hsing,
  rcases hsing with ⟨ P, hP ⟩,
  rcases E.has_singular_model P hP with ⟨ C, h2, h3 ⟩,
  rw C.preserve_has_node E,
  rw C.preserve_affine_singular_point E P at hP,
  set E' := C.change_curve E with hE', clear_value E',
  set P' := C.change_affine_point P with hP', clear_value P',
  replace hc4 : E'.c4 ≠ 0 := by {
    simp [hE', hc4],
  },
  simp [h2] at hc4,
  simp [affine_plane_point.ext_iff] at h3,
  use [P', hP],
  simp [eval_hessian_at_affine_point, h3.1, hc4],
end

/--
If a Weierstrass is of discriminant zero and `c4` zero,
under the assumption that the field is not of characteristic 2 or 3, or is perfect,
it has a rational cusp.
-/
lemma disc_zero_c4_zero_implies_has_cusp
{K : Type*} [field K] (E : weierstrass_equation K)
(hperfect : ring_char K = 2 ∨ ring_char K = 3 → my_perfect_field K):
E.has_cusp' → E.has_cusp :=
begin
  rintros ⟨ hdisc, hc4 ⟩,
  replace hperfect : (ring_char K = 2 ∨ ring_char K = 3) ∧ E.c4 = 0 → my_perfect_field K := by {
    intro h,
    exact hperfect h.1,
  },
  have hsing := mt (E.non_singular_implies_disc_non_zero hperfect),
  rw E.singular_iff_has_affine_singular_point at hsing,
  simp [non_singular', hdisc] at hsing,
  rcases hsing with ⟨ P, hP ⟩,
  rcases E.has_singular_model P hP with ⟨ C, h2, h3 ⟩,
  rw C.preserve_has_cusp E,
  rw C.preserve_affine_singular_point E P at hP,
  set E' := C.change_curve E with hE', clear_value E',
  set P' := C.change_affine_point P with hP', clear_value P',
  replace hc4 : E'.c4 = 0 := by {
    simp [hE', hc4],
  },
  simp [h2] at hc4,
  simp [affine_plane_point.ext_iff] at h3,
  use [P', hP],
  simp [eval_hessian_at_affine_point, h3.1, hc4],
end

end weierstrass_equation
