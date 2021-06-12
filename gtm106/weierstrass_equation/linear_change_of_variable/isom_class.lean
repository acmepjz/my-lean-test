import algebra.field
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import gtm106.weierstrass_equation.linear_change_of_variable.basic
import gtm106.weierstrass_equation.linear_change_of_variable.change_curve
import gtm106.weierstrass_equation.linear_change_of_variable.change_point
import tactic

-- ================
-- Isomorphism class of Weierstrass equations under linear change of variable
-- ================

namespace weierstrass_equation

def is_isom' {K : Type*} [field K]
(E E' : weierstrass_equation K) := ∃ C : linear_change_of_variable K,
(C.change_curve E) = E'

lemma is_isom'.refl {K : Type*} [field K]
(E : weierstrass_equation K) : E.is_isom' E :=
begin
  use linear_change_of_variable.identity K,
  exact linear_change_of_variable.change_curve.id E,
end

lemma is_isom'.symm {K : Type*} [field K]
(E E' : weierstrass_equation K) (h : E.is_isom' E') : E'.is_isom' E :=
begin
  rcases h with ⟨ C, h ⟩,
  use C.inverse,
  rw [← h, ← linear_change_of_variable.change_curve.comp],
  simp,
end

lemma is_isom'.trans {K : Type*} [field K]
(E E' E'' : weierstrass_equation K) (h : E.is_isom' E') (h' : E'.is_isom' E'')
: E.is_isom' E'' :=
begin
  rcases h with ⟨ C, h ⟩,
  rcases h' with ⟨ C', h' ⟩,
  use C'.composite C,
  rw [linear_change_of_variable.change_curve.comp, h, h'],
end

lemma is_isom'.is_equivalence (K : Type*) [h : field K]
: equivalence (@is_isom' K h) :=
mk_equivalence (@is_isom' K h)
(@is_isom'.refl K h)
(@is_isom'.symm K h)
(@is_isom'.trans K h)

instance isom_class'.setoid (K : Type*) [h : field K]
: setoid (weierstrass_equation K) :=
setoid.mk (@is_isom' K h)
(is_isom'.is_equivalence K)

/--
Isomorphism class of Weierstrass equations under linear change of variable
-/
def isom_class' (K : Type*) [field K] : Type* :=
quotient (isom_class'.setoid K)

def isom_class'.j {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@j K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.j],
}) E

def isom_class'.non_singular' {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@non_singular' K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_non_singular'],
}) E

def isom_class'.has_node' {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_node' K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_node'],
}) E

def isom_class'.has_cusp' {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_cusp' K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_cusp'],
}) E

def isom_class'.non_singular {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@non_singular K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_non_singular],
}) E

def isom_class'.has_node {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_node K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_node],
}) E

def isom_class'.has_cusp {K : Type*} [field K]
(E : isom_class' K) := quotient.lift (@has_cusp K _) (by {
  rintros E E' ⟨ C, h ⟩,
  rw [← h, C.preserve_has_cusp],
}) E

end weierstrass_equation
