import algebra.field
import algebra.char_zero
import algebra.char_p
import field_theory.algebraic_closure
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.gtm106.weierstrass_equation.models_by_characteristic
import tests.testchar
import tests.testperfect
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

lemma alg_closed_implies_pow_surj (K : Type*) [field K] [is_alg_closed K] (n : ℕ) (hn : n ≠ 0)
: nth_power_surjective K n :=
begin
  intro x,
  let f : polynomial K := polynomial.X^n - (polynomial.C x),
  have hdeg := calc f.degree = n : polynomial.degree_X_pow_sub_C (nat.pos_of_ne_zero hn) x
  ... ≠ 0 : by { norm_cast, exact hn, },
  have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
  replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
  cases hsplit with y hy,
  use y,
  simp at hy,
  calc y ^ n = x + (y ^ n - x) : by ring
  ... = x : by { rw hy, ring, },
end

lemma weierstrass_equation.same_j_implies_isomorphic'_char_2 {K : Type*} [field K] [is_alg_closed K]
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
(hchar2 : ring_char K = 2)
: E.is_isomorphic' E' :=
begin
  rcases E.have_model_of_char_2 hchar2 with ⟨ hj, C, hmod ⟩ | ⟨ hj, C, hmod ⟩, {
    replace hj := hj hns,
    rcases E'.have_model_of_char_2 hchar2 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      replace hj' := hj' hns',
      rw C.preserve_non_singular' E at hns,
      rw C'.preserve_non_singular' E' at hns',
      unfold weierstrass_equation.non_singular' at hns hns',
      rw ← C.j E at h hj,
      rw ← C'.j E' at h hj',
      set E1 := C.change_curve E,
      set E1' := C'.change_curve E',
      rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
      rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
      clear_value E1 E1', clear C C' E E',
      rw E1.j_of_model_of_char_2_j_non_zero hmod hchar2 at h hj,
      rw E1'.j_of_model_of_char_2_j_non_zero hmod' hchar2 at h hj',
      field_simp at hj hj',
      field_simp [hj, hj'] at h,
      let f : polynomial K := polynomial.X^2 + polynomial.X + (polynomial.C (E1.a2 + E1'.a2)),
      have hdeg : f.degree ≠ 0 := by {
        let f1 : polynomial K := polynomial.X^2,
        let f2 : polynomial K := polynomial.X,
        let f3 : polynomial K := polynomial.C (E1.a2 + E1'.a2),
        have h1 : f1.degree = 2 := polynomial.degree_X_pow _,
        have h2 : f2.degree ≤ 1 := polynomial.degree_X_le,
        have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
        have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
        ... ≤ max 1 0 : max_le_max h2 h3
        ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
        calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw ← add_assoc, }
        ... ≠ 0 : by {
          rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
        },
      },
      have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
      replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
      cases hsplit with s hs,
      simp at hs,
      clear hdeg f,
      let C : linear_change_of_variable K := linear_change_of_variable.mk 1 0 s 0 (by simp),
      use C,
      rw weierstrass_equation.ext_iff,
      unfold linear_change_of_variable.change_curve
      linear_change_of_variable.u
      linear_change_of_variable.r
      linear_change_of_variable.s
      linear_change_of_variable.t
      weierstrass_equation.a1
      weierstrass_equation.a2
      weierstrass_equation.a3
      weierstrass_equation.a4
      weierstrass_equation.a6,
      rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, h],
      have h2eq0 := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h2eq0, rw h2eq0,
      simp [zero_pow],
      calc E1.a2 - s - s ^ 2 = E1.a2 - s - s ^ 2  + (s ^ 2 + s + (E1.a2 + E1'.a2)) : by { rw hs, ring, }
      ... = E1'.a2 : by { ring, rw h2eq0, ring, },
    }, {
      exfalso, finish,
    },
  }, {
    rcases E'.have_model_of_char_2 hchar2 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      exfalso, finish,
    }, {
      rw C.preserve_non_singular' E at hns,
      rw C'.preserve_non_singular' E' at hns',
      unfold weierstrass_equation.non_singular' at hns hns',
      rw ← C.j E at h hj,
      rw ← C'.j E' at h hj',
      set E1 := C.change_curve E,
      set E1' := C'.change_curve E',
      rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
      rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
      clear_value E1 E1', clear C C' E E',
      rw E1.disc_of_model_of_char_2_j_zero hmod hchar2 at hns,
      rw E1'.disc_of_model_of_char_2_j_zero hmod' hchar2 at hns',
      field_simp at hns hns',
      cases alg_closed_implies_pow_surj K 3 (by norm_num) (E1.a3 / E1'.a3) with u hu,
      let f : polynomial K := polynomial.X^4 + (polynomial.C E1.a3) * polynomial.X + (polynomial.C (E1.a4 - u^4*E1'.a4)),
      have hdeg : f.degree ≠ 0 := by {
        let f1 : polynomial K := polynomial.X^4,
        set! f2 : polynomial K := (polynomial.C E1.a3) * polynomial.X^1 with hf2, rw pow_one at hf2,
        let f3 : polynomial K := polynomial.C (E1.a4 - u^4*E1'.a4),
        have h1 : f1.degree = 4 := polynomial.degree_X_pow _,
        have h2 : f2.degree ≤ 1 := polynomial.degree_C_mul_X_pow_le _ _,
        have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
        have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
        ... ≤ max 1 0 : max_le_max h2 h3
        ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
        calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw [← add_assoc, hf2], }
        ... ≠ 0 : by {
          rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
        },
      },
      have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
      replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
      cases hsplit with s hs,
      repeat {rw polynomial.eval₂_add at hs},
      rw [polynomial.eval₂_mul,polynomial.eval₂_X_pow, polynomial.eval₂_X] at hs,
      repeat {rw polynomial.eval₂_C at hs},
      simp at hs,
      clear hdeg f,
      let f : polynomial K := polynomial.X^2 + (polynomial.C E1.a3) * polynomial.X + (polynomial.C (s^6 + E1.a4*s^2 + E1.a6 - u^6*E1'.a6)),
      have hdeg : f.degree ≠ 0 := by {
        let f1 : polynomial K := polynomial.X^2,
        set! f2 : polynomial K := (polynomial.C E1.a3) * polynomial.X^1 with hf2, rw pow_one at hf2,
        let f3 : polynomial K := polynomial.C (s^6 + E1.a4*s^2 + E1.a6 - u^6*E1'.a6),
        have h1 : f1.degree = 2 := polynomial.degree_X_pow _,
        have h2 : f2.degree ≤ 1 := polynomial.degree_C_mul_X_pow_le _ _,
        have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
        have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
        ... ≤ max 1 0 : max_le_max h2 h3
        ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
        calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw [← add_assoc, hf2], }
        ... ≠ 0 : by {
          rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
        },
      },
      have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
      replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
      cases hsplit with t ht,
      repeat {rw polynomial.eval₂_add at ht},
      rw [polynomial.eval₂_mul,polynomial.eval₂_X_pow, polynomial.eval₂_X] at ht,
      repeat {rw polynomial.eval₂_C at ht},
      simp at ht,
      clear hdeg f,
      let C := linear_change_of_variable.mk u (s^2) s t (by {
        intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact hns hu.symm,
      }),
      use C,
      rw weierstrass_equation.ext_iff,
      unfold linear_change_of_variable.change_curve
      linear_change_of_variable.u
      linear_change_of_variable.r
      linear_change_of_variable.s
      linear_change_of_variable.t
      weierstrass_equation.a1
      weierstrass_equation.a2
      weierstrass_equation.a3
      weierstrass_equation.a4
      weierstrass_equation.a6,
      rw [hmod.1, hmod.2, hmod'.1, hmod'.2, hu],
      have h2eq0 := dvd_char_is_zero hchar2 2 (by norm_num), norm_cast at h2eq0, rw h2eq0,
      have h3eq1 := cong_char_is_eq hchar2 3 1 (by norm_num), norm_cast at h3eq1, rw h3eq1,
      field_simp [hns, hns', C.hu],
      split, { ring, },
      split, {
        calc E1.a4 - s * E1.a3 + (s ^ 2) ^ 2
        = E1.a4 - s * E1.a3 + s ^ 4 - (s ^ 4 + E1.a3 * s + (E1.a4 - u ^ 4 * E1'.a4)) : by { rw hs, ring, }
        ... = E1'.a4 * u ^ 4 : by { ring, rw h2eq0, ring, },
      },
      calc E1.a6 + s ^ 2 * E1.a4 + (s ^ 2) ^ 3 - t * E1.a3 - t ^ 2
      = E1.a6 + s ^ 2 * E1.a4 + s ^ 6 - t * E1.a3 - t ^ 2 - (t ^ 2 + E1.a3 * t + (s ^ 6 + E1.a4 * s ^ 2 + E1.a6 - u ^ 6 * E1'.a6)) : by { rw ht, ring, }
      ... = E1'.a6 * u ^ 6 : by { ring, rw h2eq0, ring, },
    },
  },
end

lemma weierstrass_equation.same_j_implies_isomorphic'_char_3 {K : Type*} [field K] [is_alg_closed K]
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
(hchar3 : ring_char K = 3)
: E.is_isomorphic' E' :=
begin
  rcases E.have_model_of_char_3 hchar3 with ⟨ hj, C, hmod ⟩ | ⟨ hj, C, hmod ⟩, {
    replace hj := hj hns,
    rcases E'.have_model_of_char_3 hchar3 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      replace hj' := hj' hns',
      rw C.preserve_non_singular' E at hns,
      rw C'.preserve_non_singular' E' at hns',
      unfold weierstrass_equation.non_singular' at hns hns',
      rw ← C.j E at h hj,
      rw ← C'.j E' at h hj',
      set E1 := C.change_curve E,
      set E1' := C'.change_curve E',
      rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
      rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
      clear_value E1 E1', clear C C' E E',
      rw E1.j_of_model_of_char_3_j_non_zero hmod hchar3 at h hj,
      rw E1'.j_of_model_of_char_3_j_non_zero hmod' hchar3 at h hj',
      field_simp at hj hj',
      push_neg at hj hj',
      cases alg_closed_implies_pow_surj K 2 (by norm_num) (E1.a2 / E1'.a2) with u hu,
      let C := linear_change_of_variable.mk u 0 0 0 (by {
        intro h, rw h at hu, field_simp [zero_pow, hj'.1] at hu, exact hj.1 hu.symm,
      }),
      use C,
      rw weierstrass_equation.ext_iff,
      unfold linear_change_of_variable.change_curve
      linear_change_of_variable.u
      linear_change_of_variable.r
      linear_change_of_variable.s
      linear_change_of_variable.t
      weierstrass_equation.a1
      weierstrass_equation.a2
      weierstrass_equation.a3
      weierstrass_equation.a4
      weierstrass_equation.a6,
      rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu],
      field_simp [zero_pow, hj.1, hj.2, hj'.1, hj'.2], split, { ring, },
      field_simp [hj.2, hj'.2] at h,
      calc E1.a6 / u ^ 6 = E1.a6 / (u ^ 2) ^ 3 : by { congr' 1, ring, }
      ... = E1'.a6 : by {
        rw hu,
        field_simp [hj.1, hj.2, hj'.1, hj'.2],
        rw [mul_comm E1.a6 _, mul_comm E1'.a6 _],
        exact h.symm,
      },
    }, {
      exfalso, finish,
    },
  }, {
    rcases E'.have_model_of_char_3 hchar3 with ⟨ hj', C', hmod' ⟩ | ⟨ hj', C', hmod' ⟩, {
      exfalso, finish,
    }, {
      rw C.preserve_non_singular' E at hns,
      rw C'.preserve_non_singular' E' at hns',
      unfold weierstrass_equation.non_singular' at hns hns',
      rw ← C.j E at h hj,
      rw ← C'.j E' at h hj',
      set E1 := C.change_curve E,
      set E1' := C'.change_curve E',
      rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
      rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
      clear_value E1 E1', clear C C' E E',
      rw E1.disc_of_model_of_char_3_j_zero hmod hchar3 at hns,
      rw E1'.disc_of_model_of_char_3_j_zero hmod' hchar3 at hns',
      field_simp at hns hns',
      cases alg_closed_implies_pow_surj K 4 (by norm_num) (E1.a4 / E1'.a4) with u hu,
      let f : polynomial K := polynomial.X^3 + (polynomial.C E1.a4) * polynomial.X + (polynomial.C (E1.a6 - u^6*E1'.a6)),
      have hdeg : f.degree ≠ 0 := by {
        let f1 : polynomial K := polynomial.X^3,
        set! f2 : polynomial K := (polynomial.C E1.a4) * polynomial.X^1 with hf2, rw pow_one at hf2,
        let f3 : polynomial K := polynomial.C (E1.a6 - u^6*E1'.a6),
        have h1 : f1.degree = 3 := polynomial.degree_X_pow _,
        have h2 : f2.degree ≤ 1 := polynomial.degree_C_mul_X_pow_le _ _,
        have h3 : f3.degree ≤ 0 := polynomial.degree_C_le,
        have h4 := calc (f2 + f3).degree ≤ max f2.degree f3.degree : polynomial.degree_add_le f2 f3
        ... ≤ max 1 0 : max_le_max h2 h3
        ... < f1.degree : by { rw h1, simp, norm_cast, norm_num, },
        calc f.degree = (f1 + (f2 + f3)).degree : by { congr' 1, rw [← add_assoc, hf2], }
        ... ≠ 0 : by {
          rw [polynomial.degree_add_eq_left_of_degree_lt h4, h1], norm_cast, norm_num,
        },
      },
      have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
      replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
      cases hsplit with r hr,
      repeat {rw polynomial.eval₂_add at hr},
      rw [polynomial.eval₂_mul,polynomial.eval₂_X_pow, polynomial.eval₂_X] at hr,
      repeat {rw polynomial.eval₂_C at hr},
      simp at hr,
      clear hdeg f,
      let C := linear_change_of_variable.mk u r 0 0 (by {
        intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact hns hu.symm,
      }),
      use C,
      rw weierstrass_equation.ext_iff,
      unfold linear_change_of_variable.change_curve
      linear_change_of_variable.u
      linear_change_of_variable.r
      linear_change_of_variable.s
      linear_change_of_variable.t
      weierstrass_equation.a1
      weierstrass_equation.a2
      weierstrass_equation.a3
      weierstrass_equation.a4
      weierstrass_equation.a6,
      rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu],
      have h := dvd_char_is_zero hchar3 3 (by norm_num), norm_cast at h, rw h, clear h,
      field_simp [zero_pow, hns, hns', C.hu], split, { ring, },
      calc E1.a6 + r * E1.a4 + r ^ 3 = E1.a6 + r * E1.a4 + r ^ 3 - (r ^ 3 + E1.a4 * r + (E1.a6 - u ^ 6 * E1'.a6)) : by { rw hr, ring, }
      ... = E1'.a6 * u ^ 6 : by ring,
    },
  },
end

-- TODO: separable closed is enough (GTM106 Exercise A.4)
lemma weierstrass_equation.same_j_implies_isomorphic' {K : Type*} [field K] [is_alg_closed K]
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
: E.is_isomorphic' E' :=
begin
  by_cases hchar2 : ring_char K = 2, {
    exact weierstrass_equation.same_j_implies_isomorphic'_char_2 h hns hns' hchar2,
  },
  by_cases hchar3 : ring_char K = 3, {
    exact weierstrass_equation.same_j_implies_isomorphic'_char_3 h hns hns' hchar3,
  },
  rcases E.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C, hmod ⟩,
  rcases E'.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C', hmod' ⟩,
  rw C.preserve_non_singular' E at hns,
  rw C'.preserve_non_singular' E' at hns',
  unfold weierstrass_equation.non_singular' at hns hns',
  rw [← C.j E, ← C'.j E'] at h,
  set E1 := C.change_curve E,
  set E1' := C'.change_curve E',
  rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
  rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
  clear_value E1 E1', clear C C' E E',
  unfold weierstrass_equation.j at h,
  field_simp [hns, hns'] at h,
  rw [E1.c4_of_model_of_char_neq_2_and_3 hmod,
  E1.disc_of_model_of_char_neq_2_and_3 hmod,
  E1'.c4_of_model_of_char_neq_2_and_3 hmod',
  E1'.disc_of_model_of_char_neq_2_and_3 hmod'] at h,
  ring_exp at h,
  replace h := calc E1.a4 ^ 3 * E1'.a6 ^ 2 * 16^4 * 27^2
  = (E1.a4 ^ 3 * (E1'.a4 ^ 3 * 7077888) + E1.a4 ^ 3 * (E1'.a6 ^ 2 * 47775744)) - E1.a4 ^ 3 * (E1'.a4 ^ 3 * 7077888) : by ring
  ... = E1'.a4 ^ 3 * E1.a6 ^ 2 * 16^4 * 27^2 : by { rw h, ring, },
  have h4 := power_of_prime_neq_char_is_non_zero K 4 2 2 (by norm_num) (by norm_num) hchar2, norm_num at h4,
  have h16 := power_of_prime_neq_char_is_non_zero K 16 2 4 (by norm_num) (by norm_num) hchar2, norm_num at h16,
  have h27 := power_of_prime_neq_char_is_non_zero K 27 3 3 (by norm_num) (by norm_num) hchar3, norm_num at h27,
  field_simp [h16, h27] at h,
  rw E1.disc_of_model_of_char_neq_2_and_3 hmod at hns,
  rw E1'.disc_of_model_of_char_neq_2_and_3 hmod' at hns',
  by_cases ha4 : E1.a4 = 0, {
    rw ha4 at h hns,
    field_simp [zero_pow, h16, h27] at hns,
    field_simp [zero_pow, hns] at h,
    rw h at hns',
    field_simp [zero_pow, h16, h27] at hns',
    cases alg_closed_implies_pow_surj K 6 (by norm_num) (E1.a6/E1'.a6) with u hu,
    let C := linear_change_of_variable.mk u 0 0 0 (by {
      intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact hns hu.symm,
    }),
    use C,
    rw weierstrass_equation.ext_iff,
    unfold linear_change_of_variable.change_curve
    linear_change_of_variable.u
    linear_change_of_variable.r
    linear_change_of_variable.s
    linear_change_of_variable.t
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, ha4, h, hu],
    field_simp [zero_pow, hns], ring,
  },
  by_cases ha6 : E1.a6 = 0, {
    rw ha6 at h hns,
    field_simp [zero_pow, ha4] at h,
    rw h at hns',
    field_simp [zero_pow, h4, h16] at hns',
    cases alg_closed_implies_pow_surj K 4 (by norm_num) (E1.a4/E1'.a4) with u hu,
    let C := linear_change_of_variable.mk u 0 0 0 (by {
      intro h, rw h at hu, field_simp [zero_pow, hns'] at hu, exact ha4 hu.symm,
    }),
    use C,
    rw weierstrass_equation.ext_iff,
    unfold linear_change_of_variable.change_curve
    linear_change_of_variable.u
    linear_change_of_variable.r
    linear_change_of_variable.s
    linear_change_of_variable.t
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, ha6, h, hu],
    field_simp [zero_pow, ha4], ring,
  },
  by_cases ha4' : E1'.a4 = 0, {
    exfalso,
    rw ha4' at h,
    field_simp [zero_pow, ha4] at h,
    rw [ha4', h] at hns',
    field_simp [zero_pow] at hns',
    exact hns',
  },
  by_cases ha6' : E1'.a6 = 0, {
    exfalso,
    rw ha6' at h,
    field_simp [zero_pow, ha4', ha6] at h,
    exact h,
  },
  cases alg_closed_implies_pow_surj K 2 (by norm_num) ((E1.a6 / E1'.a6) / (E1.a4 / E1'.a4)) with u hu,
  have hu4 := calc u ^ 4 = (u ^ 2) ^ 2 : by ring
  ... = E1.a4 / E1'.a4 : by {
    rw hu,
    field_simp [zero_pow, ha4, ha6, ha4', ha6'],
    ring_exp,
    rw mul_comm (E1.a6 ^ 2) _,
    exact h.symm,
  },
  have hu6 := calc u ^ 6 = (u ^ 2) ^ 3 : by ring
  ... = E1.a6 / E1'.a6 : by {
    rw hu,
    field_simp [zero_pow, ha4, ha6, ha4', ha6'],
    calc (E1.a6 * E1'.a4) ^ 3 * E1'.a6
    = (E1'.a4 ^ 3 * E1.a6 ^ 2) * E1.a6 * E1'.a6 : by ring
    ... = (E1.a4 ^ 3 * E1'.a6 ^ 2) * E1.a6 * E1'.a6 : by rw h
    ... = E1.a6 * (E1'.a6 * E1.a4) ^ 3 : by ring,
  },
  let C := linear_change_of_variable.mk u 0 0 0 (by {
    intro h, rw h at hu, field_simp [zero_pow, ha4, ha6, ha4', ha6'] at hu, exact hu,
  }),
  use C,
  rw weierstrass_equation.ext_iff,
  unfold linear_change_of_variable.change_curve
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6,
  rw [hmod.1, hmod.2.1, hmod.2.2, hmod'.1, hmod'.2.1, hmod'.2.2, hu4, hu6],
  field_simp [zero_pow, ha4, ha6], split; ring,
end
