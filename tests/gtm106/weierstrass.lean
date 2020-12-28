import algebra.field
import algebra.char_zero
import algebra.char_p
import data.int.basic
import data.rat.basic
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tests.gtm106.weierstrass_equation.linear_change_of_variable
import tests.gtm106.weierstrass_equation.models_by_characteristic
import tests.gtm106.weierstrass_equation.j_invariant
import tests.testchar
import tactic

noncomputable theory

lemma weierstrass_equation.same_j_implies_isomorphic' {K : Type*} [field K] [is_alg_closed K]
{E E' : weierstrass_equation K} (h : E.j = E'.j) (hns : E.non_singular') (hns' : E'.non_singular')
: E.is_isomorphic' E' :=
begin
  unfold weierstrass_equation.non_singular' at hns hns',
  by_cases hchar2 : ring_char K = 2, {
    sorry,
  },
  by_cases hchar3 : ring_char K = 3, {
    sorry,
  },
  rcases E.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C, hmod ⟩,
  rcases E'.have_model_of_char_neq_2_and_3 hchar2 hchar3 with ⟨ C', hmod' ⟩,
  set E1 := C.change_curve E,
  set E1' := C'.change_curve E',
  rw ← weierstrass_equation.is_isomorphic'.transitive E E1 E' ⟨ C, rfl ⟩,
  rw weierstrass_equation.is_isomorphic'.transitive' E1 E' E1' ⟨ C', rfl ⟩,
  sorry,
end
