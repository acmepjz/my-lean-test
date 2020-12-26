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

lemma exists_j0 : ∃ E : weierstrass_equation ℚ, E.non_singular' ∧ E.j = 0 :=
begin
  use [0, 0, 0, 0, -1],
  split, {
    unfold weierstrass_equation.non_singular'
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

lemma exists_j1728 : ∃ E : weierstrass_equation ℚ, E.non_singular' ∧ E.j = 1728 :=
begin
  use [0, 0, 0, -1, 0],
  split, {
    unfold weierstrass_equation.non_singular'
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

lemma exists_j (j : ℚ) : ∃ E : weierstrass_equation ℚ, E.non_singular' ∧ E.j = j :=
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
