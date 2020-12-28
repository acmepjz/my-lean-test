import algebra.field
import algebra.char_zero
import algebra.char_p
import field_theory.algebraic_closure
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.gtm106.weierstrass_equation.models_by_characteristic
import tests.testchar
import tactic

lemma weierstrass_equation.exists_j {K : Type*} [field K]
(j : K) : ∃ E : weierstrass_equation K,
E.non_singular' ∧ E.j = j :=
begin
  let E0 : weierstrass_equation K := weierstrass_equation.mk 0 0 1 0 0,
  have hc4_0 : E0.c4 = 0 := by {
    unfold weierstrass_equation.c4
    weierstrass_equation.b2
    weierstrass_equation.b4,
    ring, ring,
  },
  have hdisc_0 : E0.disc = -27 := by {
    unfold weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8,
    ring, ring,
  },
  have hj_0 : E0.j = 0 := by {
    unfold weierstrass_equation.j,
    rw [hc4_0, hdisc_0],
    ring,
  },
  let E1728 : weierstrass_equation K := weierstrass_equation.mk 0 0 0 1 0,
  have hc4_1728 : E1728.c4 = -48 := by {
    unfold weierstrass_equation.c4
    weierstrass_equation.b2
    weierstrass_equation.b4,
    ring, ring,
  },
  have hdisc_1728 : E1728.disc = -64 := by {
    unfold weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8,
    ring, ring,
  },
  have hj_1728 : E1728.j = 1728 := by {
    unfold weierstrass_equation.j,
    rw [hc4_1728, hdisc_1728],
    by_cases hchar2 : ring_char K = 2, {
      have h := dvd_char_is_zero hchar2 1728 (by norm_num), norm_cast at h, rw h, clear h,
      have h := dvd_char_is_zero hchar2 48 (by norm_num), norm_cast at h, rw h, clear h,
      ring,
    },
    have h64 := power_of_prime_neq_char_is_non_zero K 64 2 6 (by norm_num) (by norm_num) hchar2,
    norm_num at h64,
    field_simp [h64], ring,
  },
  by_cases h0 : j = 0, {
    rw h0,
    by_cases hchar3 : ring_char K = 3, {
      use E1728,
      split, {
        unfold weierstrass_equation.non_singular',
        rw hdisc_1728,
        have hchar2 : ring_char K ≠ 2 := by { rw hchar3, norm_num, },
        have h64 := power_of_prime_neq_char_is_non_zero K 64 2 6 (by norm_num) (by norm_num) hchar2,
        norm_num at h64,
        field_simp [h64],
      },
      rw hj_1728,
      have h := dvd_char_is_zero hchar3 1728 (by norm_num), norm_cast at h, exact h,
    },
    use E0,
    split, {
      unfold weierstrass_equation.non_singular',
      rw hdisc_0,
      have h27 := power_of_prime_neq_char_is_non_zero K 27 3 3 (by norm_num) (by norm_num) hchar3,
      norm_num at h27,
      field_simp [h27],
    },
    exact hj_0,
  },
  by_cases h1728 : j = 1728, {
    rw h1728,
    by_cases hchar2 : ring_char K = 2, {
      exfalso,
      have h := dvd_char_is_zero hchar2 1728 (by norm_num), norm_cast at h, rw h at h1728, clear h,
      exact h0 h1728,
    },
    use E1728,
    split, {
      unfold weierstrass_equation.non_singular',
      rw hdisc_1728,
      have h64 := power_of_prime_neq_char_is_non_zero K 64 2 6 (by norm_num) (by norm_num) hchar2,
      norm_num at h64,
      field_simp [h64],
    },
    exact hj_1728,
  },
  replace h1728 : j-1728 ≠ 0 := sub_ne_zero.mpr h1728,
  let E := weierstrass_equation.mk (j-1728) 0 0 (-36*(j-1728)^3) (-(j-1728)^5),
  have hc4 : E.c4 = j * (j-1728)^3 := by {
    unfold weierstrass_equation.c4
    weierstrass_equation.b2
    weierstrass_equation.b4,
    ring, ring,
  },
  have hdisc : E.disc = j^2 * (j-1728)^9 := by {
    unfold weierstrass_equation.disc
    weierstrass_equation.b2
    weierstrass_equation.b4
    weierstrass_equation.b6
    weierstrass_equation.b8,
    ring, ring,
  },
  have hns : E.disc ≠ 0 := by {
    rw hdisc,
    field_simp [h0, h1728],
  },
  have hj : E.j = j := by {
    unfold weierstrass_equation.j,
    field_simp [hns],
    rw [hc4, hdisc],
    ring,
  },
  exact ⟨ E, hns, hj ⟩,
end
