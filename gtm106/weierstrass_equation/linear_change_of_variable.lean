import algebra.field
import tests.gtm106.naive_plane
import tests.gtm106.weierstrass_equation.basic
import tactic

noncomputable theory

/-
also viewed as a matrix
u^2   0   r
u^2*s u^3 t
0     0   1
-/

@[ext]
structure linear_change_of_variable (K : Type*) [field K] :=
mk :: (u r s t : K) (hu : u ≠ 0)

def linear_change_of_variable.identity (K : Type*) [field K] : linear_change_of_variable K :=
linear_change_of_variable.mk 1 0 0 0 (by simp)

def linear_change_of_variable.composite {K : Type*} [field K]
(C C' : linear_change_of_variable K) : linear_change_of_variable K :=
linear_change_of_variable.mk (C.u*C'.u) (C'.r*C.u^2 + C.r) (C.u*C'.s + C.s)
(C'.t*C.u^3 + C'.r*C.s*C.u^2 + C.t) (by field_simp [C.hu, C'.hu])

def linear_change_of_variable.inverse {K : Type*} [field K]
(C : linear_change_of_variable K) : linear_change_of_variable K :=
linear_change_of_variable.mk (1/C.u) (-C.r/C.u^2) (-C.s/C.u) ((C.r*C.s-C.t)/C.u^3) (by field_simp [C.hu])

lemma linear_change_of_variable.comp_assoc {K : Type*} [field K]
(C C' C'' : linear_change_of_variable K) : ((C.composite C').composite C'') = (C.composite (C'.composite C'')) :=
begin
  rw linear_change_of_variable.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { ring, }, split, { ring, }, split, { ring, }, ring,
end

lemma linear_change_of_variable.id_comp {K : Type*} [field K]
(C : linear_change_of_variable K) : (linear_change_of_variable.identity K).composite C = C :=
begin
  rw linear_change_of_variable.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.identity
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { ring, }, split, { ring, }, split, { ring, }, ring,
end

lemma linear_change_of_variable.comp_id {K : Type*} [field K]
(C : linear_change_of_variable K) : C.composite (linear_change_of_variable.identity K) = C :=
begin
  rw linear_change_of_variable.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.identity
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { ring, }, split, { ring, }, split, { ring, }, ring,
end

lemma linear_change_of_variable.inv_comp {K : Type*} [field K]
(C : linear_change_of_variable K) : C.inverse.composite C = linear_change_of_variable.identity K :=
begin
  rw linear_change_of_variable.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.inverse
  linear_change_of_variable.identity
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { field_simp [C.hu], }, split, { field_simp [pow_succ, C.hu], }, split, { field_simp [C.hu], },
  field_simp [pow_succ, C.hu], ring,
end

lemma linear_change_of_variable.comp_inv {K : Type*} [field K]
(C : linear_change_of_variable K) : C.composite C.inverse = linear_change_of_variable.identity K :=
begin
  rw linear_change_of_variable.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.inverse
  linear_change_of_variable.identity
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t,
  split, { field_simp [C.hu], }, split, { field_simp [pow_succ, C.hu], }, split, { field_simp [C.hu], ring, },
  field_simp [pow_succ, C.hu], ring,
end

def linear_change_of_variable.change_curve {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K) : weierstrass_equation K :=
weierstrass_equation.mk
((E.a1 + 2*C.s)/C.u)
((E.a2 - C.s*E.a1 + 3*C.r - C.s^2)/C.u^2)
((E.a3 + C.r*E.a1 + 2*C.t)/C.u^3)
((E.a4 - C.s*E.a3 + 2*C.r*E.a2 - (C.t+C.r*C.s)*E.a1 + 3*C.r^2 - 2*C.s*C.t)/C.u^4)
((E.a6 + C.r*E.a4 + C.r^2*E.a2 + C.r^3 - C.t*E.a3 - C.t^2 - C.r*C.t*E.a1)/C.u^6)

lemma linear_change_of_variable.change_curve.id {K : Type*} [field K]
(E : weierstrass_equation K) :
(linear_change_of_variable.identity K).change_curve E = E :=
begin
  rw weierstrass_equation.ext_iff,
  unfold linear_change_of_variable.identity
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6,
  split, { ring, }, split, { ring, }, split, { ring, }, ring, split, { ring, }, ring,
end

lemma linear_change_of_variable.change_curve.comp {K : Type*} [field K]
(C C' : linear_change_of_variable K) (E : weierstrass_equation K) :
C.change_curve (C'.change_curve E) = (C'.composite C).change_curve E :=
begin
  rw weierstrass_equation.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6,
  split, { field_simp [C.hu, C'.hu], ring, },
  split, { field_simp [C.hu, C'.hu], ring, },
  split, { field_simp [C.hu, C'.hu], ring, },
  split, { field_simp [C.hu, C'.hu], ring, },
  field_simp [C.hu, C'.hu], ring,
end

lemma linear_change_of_variable.a1 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a1 = (E.a1 + 2*C.s)/C.u :=
begin
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a1,
end

lemma linear_change_of_variable.a2 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a2 = (E.a2 - C.s*E.a1 + 3*C.r - C.s^2)/C.u^2 :=
begin
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a2,
end

lemma linear_change_of_variable.a3 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a3 = (E.a3 + C.r*E.a1 + 2*C.t)/C.u^3 :=
begin
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a3,
end

lemma linear_change_of_variable.a4 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a4 = (E.a4 - C.s*E.a3 + 2*C.r*E.a2 - (C.t+C.r*C.s)*E.a1 + 3*C.r^2 - 2*C.s*C.t)/C.u^4 :=
begin
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a4,
end

lemma linear_change_of_variable.a6 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).a6 = (E.a6 + C.r*E.a4 + C.r^2*E.a2 + C.r^3 - C.t*E.a3 - C.t^2 - C.r*C.t*E.a1)/C.u^6 :=
begin
  unfold linear_change_of_variable.change_curve
  weierstrass_equation.a6,
end

lemma linear_change_of_variable.b2 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b2 = (E.b2 + 12*C.r)/C.u^2 :=
begin
  unfold weierstrass_equation.b2,
  rw [C.a1, C.a2],
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.b4 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b4 = (E.b4 + C.r*E.b2 + 6*C.r^2)/C.u^4 :=
begin
  unfold weierstrass_equation.b4
  weierstrass_equation.b2,
  rw [C.a1, C.a3, C.a4],
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.b6 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b6 = (E.b6 + 2*C.r*E.b4 + C.r^2*E.b2 + 4*C.r^3)/C.u^6 :=
begin
  unfold weierstrass_equation.b6
  weierstrass_equation.b4
  weierstrass_equation.b2,
  rw [C.a3, C.a6],
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.b8 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).b8 = (E.b8 + 3*C.r*E.b6 + 3*C.r^2*E.b4 + C.r^3*E.b2 + 3*C.r^4)/C.u^8 :=
begin
  unfold weierstrass_equation.b8
  weierstrass_equation.b6
  weierstrass_equation.b4
  weierstrass_equation.b2,
  rw [C.a1, C.a2, C.a3, C.a4, C.a6],
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.c4 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).c4 = E.c4/C.u^4 :=
begin
  unfold weierstrass_equation.c4,
  rw [C.b2, C.b4],
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.c6 {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).c6 = E.c6/C.u^6 :=
begin
  unfold weierstrass_equation.c6,
  rw [C.b2, C.b4, C.b6],
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.disc {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).disc = E.disc/C.u^12 :=
begin
  unfold weierstrass_equation.disc,
  rw [C.b2, C.b4, C.b6, C.b8],
  unfold weierstrass_equation.b8
  weierstrass_equation.b6
  weierstrass_equation.b4
  weierstrass_equation.b2,
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.preserve_non_singular' {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.non_singular' ↔ (C.change_curve E).non_singular' :=
begin
  unfold weierstrass_equation.non_singular',
  rw [C.disc],
  field_simp [C.hu],
end

lemma linear_change_of_variable.preserve_has_node' {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_node' ↔ (C.change_curve E).has_node' :=
begin
  unfold weierstrass_equation.has_node',
  rw [C.c4, C.disc],
  field_simp [C.hu],
end

lemma linear_change_of_variable.preserve_has_cusp' {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_cusp' ↔ (C.change_curve E).has_cusp' :=
begin
  unfold weierstrass_equation.has_cusp',
  rw [C.c4, C.disc],
  field_simp [C.hu],
end

lemma linear_change_of_variable.j {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: (C.change_curve E).j = E.j :=
begin
  unfold weierstrass_equation.j,
  rw [C.c4, C.disc],
  by_cases h : E.disc = 0, {
    rw h,
    simp,
  },
  field_simp [pow_succ, C.hu, h],
  ring,
end

def weierstrass_equation.is_isomorphic' {K : Type*} [field K]
(E E' : weierstrass_equation K) := ∃ C : linear_change_of_variable K,
(C.change_curve E) = E'

lemma weierstrass_equation.is_isomorphic'.id {K : Type*} [field K]
(E : weierstrass_equation K) : E.is_isomorphic' E :=
begin
  use linear_change_of_variable.identity K,
  exact linear_change_of_variable.change_curve.id E,
end

def weierstrass_equation.is_isomorphic'.symm {K : Type*} [field K]
(E E' : weierstrass_equation K) : E.is_isomorphic' E' ↔ E'.is_isomorphic' E :=
begin
  have key : ∀ E E' : weierstrass_equation K, E.is_isomorphic' E' → E'.is_isomorphic' E := by {
    clear E E',
    rintros E E' ⟨ C, h ⟩,
    use C.inverse,
    rw ← h,
    rw linear_change_of_variable.change_curve.comp,
    rw linear_change_of_variable.comp_inv,
    rw linear_change_of_variable.change_curve.id,
  },
  split, { exact key E E', },
  exact key E' E,
end

def weierstrass_equation.is_isomorphic'.transitive {K : Type*} [field K]
(E E' E'' : weierstrass_equation K) :
E.is_isomorphic' E' → (E'.is_isomorphic' E'' ↔ E.is_isomorphic' E'') :=
begin
  rintros ⟨ C, h ⟩,
  split, {
    rintros ⟨ C', h' ⟩,
    use C.composite C',
    rw ← linear_change_of_variable.change_curve.comp,
    rw [h, h'],
  },
  rintros ⟨ C', h' ⟩,
  use C.inverse.composite C',
  rw ← linear_change_of_variable.change_curve.comp,
  rw ← h,
  rw linear_change_of_variable.change_curve.comp C.inverse C E,
  rw linear_change_of_variable.comp_inv,
  rw linear_change_of_variable.change_curve.id,
  exact h',
end

def weierstrass_equation.is_isomorphic'.transitive' {K : Type*} [field K]
(E E' E'' : weierstrass_equation K) :
E'.is_isomorphic' E'' → (E.is_isomorphic' E' ↔ E.is_isomorphic' E'') :=
begin
  rw weierstrass_equation.is_isomorphic'.symm E' E'',
  rw weierstrass_equation.is_isomorphic'.symm E E',
  rw weierstrass_equation.is_isomorphic'.symm E E'',
  exact weierstrass_equation.is_isomorphic'.transitive _ _ _,
end

lemma weierstrass_equation.isomorphic'_implies_same_j {K : Type*} [field K]
{E E' : weierstrass_equation K} (h : E.is_isomorphic' E') : E.j = E'.j :=
begin
  cases h with C h,
  rw [← h, C.j E],
end

def linear_change_of_variable.change_affine_point_back {K : Type*} [field K]
(C : linear_change_of_variable K) (P : affine_plane_point K) : affine_plane_point K :=
affine_plane_point.mk (C.u^2*P.x + C.r) (C.u^3*P.y + C.u^2*C.s*P.x + C.t)

def linear_change_of_variable.change_projective_point_back {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point K) : projective_plane_point K :=
projective_plane_point.mk (C.u^2*P.X + C.r*P.Z) (C.u^3*P.Y + C.u^2*C.s*P.X + C.t*P.Z) P.Z
(by {
  rintros ⟨ hX, hY, hZ ⟩,
  rw hZ at hX hY,
  field_simp [C.hu] at hX,
  rw hX at hY,
  field_simp [C.hu] at hY,
  exact P.h ⟨ hX, hY, hZ ⟩,
})

def linear_change_of_variable.change_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (P : affine_plane_point K) : affine_plane_point K :=
affine_plane_point.mk (P.x/C.u^2 - C.r/C.u^2) (P.y/C.u^3 - C.s*P.x/C.u^3 + (C.r*C.s-C.t)/C.u^3)

lemma linear_change_of_variable.change_affine_point.id {K : Type*} [field K]
(P : affine_plane_point K) :
(linear_change_of_variable.identity K).change_affine_point P = P :=
begin
  rw affine_plane_point.ext_iff,
  unfold linear_change_of_variable.identity
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t
  linear_change_of_variable.change_affine_point
  affine_plane_point.x
  affine_plane_point.y,
  split, { ring, }, ring,
end

lemma linear_change_of_variable.change_affine_point.comp {K : Type*} [field K]
(C C' : linear_change_of_variable K) (P : affine_plane_point K) :
C.change_affine_point (C'.change_affine_point P) = (C'.composite C).change_affine_point P :=
begin
  rw affine_plane_point.ext_iff,
  unfold linear_change_of_variable.composite
  linear_change_of_variable.u
  linear_change_of_variable.r
  linear_change_of_variable.s
  linear_change_of_variable.t
  linear_change_of_variable.change_affine_point
  affine_plane_point.x
  affine_plane_point.y,
  split, { field_simp [C.hu, C'.hu], ring, },
  field_simp [C.hu, C'.hu], ring,
end

def linear_change_of_variable.change_projective_point {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point K) : projective_plane_point K :=
projective_plane_point.mk (P.X/C.u^2 - P.Z*C.r/C.u^2) (P.Y/C.u^3 - C.s*P.X/C.u^3 + P.Z*(C.r*C.s-C.t)/C.u^3) P.Z
(by {
  rintros ⟨ hX, hY, hZ ⟩,
  rw hZ at hX hY,
  field_simp [C.hu] at hX,
  rw hX at hY,
  field_simp [C.hu] at hY,
  exact P.h ⟨ hX, hY, hZ ⟩,
})

-- no denominator version
def linear_change_of_variable.change_projective_point' {K : Type*} [field K]
(C : linear_change_of_variable K) (P : projective_plane_point K) : projective_plane_point K :=
projective_plane_point.mk (P.X*C.u - P.Z*C.r*C.u) (P.Y - C.s*P.X + P.Z*(C.r*C.s-C.t)) (P.Z*C.u^3)
(by {
  rintros ⟨ hX, hY, hZ ⟩,
  field_simp [C.hu] at hZ,
  rw hZ at hX hY,
  field_simp [C.hu] at hX,
  rw hX at hY,
  field_simp [C.hu] at hY,
  exact P.h ⟨ hX, hY, hZ ⟩,
})

lemma linear_change_of_variable.change_affine_point_id {K : Type*} [field K]
(C : linear_change_of_variable K) (P P' : affine_plane_point K) :
C.change_affine_point_back P = P' ↔ C.change_affine_point P' = P :=
begin
  split, {
    unfold linear_change_of_variable.change_affine_point_back
    linear_change_of_variable.change_affine_point,
    intro h1,
    rw affine_plane_point.ext_iff at h1 ⊢,
    cases h1 with h1 h2,
    rw [← h1, ← h2],
    field_simp [C.hu], ring,
    simp [mul_comm],
  }, {
    unfold linear_change_of_variable.change_affine_point_back
    linear_change_of_variable.change_affine_point,
    intro h1,
    rw affine_plane_point.ext_iff at h1 ⊢,
    cases h1 with h1 h2,
    rw [← h1, ← h2],
    field_simp [C.hu], ring,
    simp [mul_comm],
  },
end

lemma linear_change_of_variable.change_projective_point_id {K : Type*} [field K]
(C : linear_change_of_variable K) (P P' : projective_plane_point K) :
C.change_projective_point_back P = P' ↔ C.change_projective_point P' = P :=
begin
  split, {
    unfold linear_change_of_variable.change_projective_point_back
    linear_change_of_variable.change_projective_point,
    intro h1,
    rw projective_plane_point.ext_iff at h1 ⊢,
    unfold projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z at h1 ⊢,
    rcases h1 with ⟨ h1, h2, h3 ⟩,
    rw [← h1, ← h2, ← h3],
    field_simp [C.hu], ring,
    simp [mul_comm],
  }, {
    unfold linear_change_of_variable.change_projective_point_back
    linear_change_of_variable.change_projective_point,
    intro h1,
    rw projective_plane_point.ext_iff at h1 ⊢,
    unfold projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z at h1 ⊢,
    rcases h1 with ⟨ h1, h2, h3 ⟩,
    rw [← h1, ← h2, ← h3],
    field_simp [C.hu], ring,
    simp [mul_comm],
  },
end

lemma linear_change_of_variable.eval_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_at_affine_point (C.change_affine_point P) = (E.eval_at_affine_point P)/C.u^6 :=
begin
  unfold weierstrass_equation.eval_at_affine_point
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6
  linear_change_of_variable.change_affine_point
  affine_plane_point.x
  affine_plane_point.y,
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.eval_dx_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_dx_at_affine_point (C.change_affine_point P)
= (E.eval_dx_at_affine_point P + C.s * E.eval_dy_at_affine_point P)/C.u^4 :=
begin
  unfold weierstrass_equation.eval_dx_at_affine_point
  weierstrass_equation.eval_dy_at_affine_point
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6
  linear_change_of_variable.change_affine_point
  affine_plane_point.x
  affine_plane_point.y,
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.eval_dy_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_dy_at_affine_point (C.change_affine_point P) = (E.eval_dy_at_affine_point P)/C.u^3 :=
begin
  unfold weierstrass_equation.eval_dy_at_affine_point
  linear_change_of_variable.change_curve
  weierstrass_equation.a1
  weierstrass_equation.a2
  weierstrass_equation.a3
  weierstrass_equation.a4
  weierstrass_equation.a6
  linear_change_of_variable.change_affine_point
  affine_plane_point.x
  affine_plane_point.y,
  field_simp [pow_succ, C.hu],
  ring,
end

lemma linear_change_of_variable.eval_hessian_at_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
(P : affine_plane_point K) :
(C.change_curve E).eval_hessian_at_affine_point (C.change_affine_point P) = (E.eval_hessian_at_affine_point P)/C.u^2 :=
begin
  unfold weierstrass_equation.eval_hessian_at_affine_point,
  rw C.b2,
  unfold linear_change_of_variable.change_affine_point
  affine_plane_point.x
  affine_plane_point.y,
  field_simp [pow_succ, C.hu],
  ring,
end

lemma weierstrass_equation.change_curve_preserve_affine_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_on_curve P ↔ (C.change_curve E).affine_point_on_curve
(C.change_affine_point P) :=
begin
  unfold weierstrass_equation.affine_point_on_curve,
  rw C.eval_at_affine_point E P,
  field_simp [C.hu],
end

lemma weierstrass_equation.change_curve_preserve_affine_regular_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_regular P ↔ (C.change_curve E).affine_point_regular
(C.change_affine_point P) :=
begin
  unfold weierstrass_equation.affine_point_regular,
  split, {
    intro h,
    use (E.change_curve_preserve_affine_point C P).1 h.1,
    rintros ⟨ hh1, hh2 ⟩,
    rw C.eval_dx_at_affine_point E P at hh1,
    rw C.eval_dy_at_affine_point E P at hh2,
    field_simp [C.hu] at hh2,
    rw hh2 at hh1,
    field_simp [C.hu] at hh1,
    exact h.2 ⟨ hh1, hh2 ⟩,
  }, {
    intro h,
    use (E.change_curve_preserve_affine_point C P).2 h.1,
    rintros ⟨ hh1, hh2 ⟩,
    rw [C.eval_dx_at_affine_point E P, C.eval_dy_at_affine_point E P, hh1, hh2] at h,
    field_simp [C.hu] at h,
    exact h,
  },
end

lemma weierstrass_equation.change_curve_preserve_affine_singular_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_singular P ↔ (C.change_curve E).affine_point_singular
(C.change_affine_point P) :=
begin
  split, {
    intro h,
    have h1 := E.affine_point_is_regular_or_singular P h.1,
    have h2 := (C.change_curve E).affine_point_is_regular_or_singular (C.change_affine_point P)
    ((E.change_curve_preserve_affine_point C P).1 h.1),
    rw ← h1 at h,
    rw ← h2,
    intro h3,
    exact h ((E.change_curve_preserve_affine_regular_point C P).2 h3),
  }, {
    intro h,
    have h1 := E.affine_point_is_regular_or_singular P ((E.change_curve_preserve_affine_point C P).2 h.1),
    have h2 := (C.change_curve E).affine_point_is_regular_or_singular (C.change_affine_point P) h.1,
    rw ← h1,
    rw ← h2 at h,
    intro h3,
    exact h ((E.change_curve_preserve_affine_regular_point C P).1 h3),
  },
end

lemma weierstrass_equation.change_curve_preserve_node
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_is_node P ↔ (C.change_curve E).affine_point_is_node
(C.change_affine_point P) :=
begin
  unfold weierstrass_equation.affine_point_is_node,
  rw E.change_curve_preserve_affine_singular_point C P,
  rw C.eval_hessian_at_affine_point E P,
  field_simp [C.hu],
end

lemma weierstrass_equation.change_curve_preserve_cusp
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (P : affine_plane_point K) :
E.affine_point_is_cusp P ↔ (C.change_curve E).affine_point_is_cusp
(C.change_affine_point P) :=
begin
  unfold weierstrass_equation.affine_point_is_cusp,
  rw E.change_curve_preserve_affine_singular_point C P,
  rw C.eval_hessian_at_affine_point E P,
  field_simp [C.hu],
end

/-
lemma weierstrass_equation.change_curve_preserve_projective_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (X Y Z : K) :
let P' := C.change_projective_point X Y Z in
E.projective_point_on_curve X Y Z ↔ (C.change_curve E).projective_point_on_curve P'.1 P'.2.1 P'.2.2 :=
begin
  sorry,
end
-/

lemma linear_change_of_variable.preserve_non_singular {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.non_singular ↔ (C.change_curve E).non_singular :=
begin
  repeat { rw weierstrass_equation.non_singular_iff_affine_non_singular },
  unfold weierstrass_equation.affine_non_singular,
  split, {
    intros h P,
    replace h := h (C.inverse.change_affine_point P),
    rw E.change_curve_preserve_affine_point C _ at h,
    rw E.change_curve_preserve_affine_regular_point C _ at h,
    rw linear_change_of_variable.change_affine_point.comp _ _ P at h,
    rw linear_change_of_variable.inv_comp _ at h,
    rw linear_change_of_variable.change_affine_point.id at h,
    exact h,
  }, {
    intros h P,
    replace h := h (C.change_affine_point P),
    rw E.change_curve_preserve_affine_point C _,
    rw E.change_curve_preserve_affine_regular_point C _,
    exact h,
  },
end

lemma linear_change_of_variable.preserve_has_node {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_node ↔ (C.change_curve E).has_node :=
begin
  unfold weierstrass_equation.has_node,
  split, {
    rintros ⟨ P, hP ⟩,
    use C.change_affine_point P,
    exact (E.change_curve_preserve_node C P).1 hP,
  }, {
    rintros ⟨ P, hP ⟩,
    use C.inverse.change_affine_point P,
    rw (C.change_curve E).change_curve_preserve_node C.inverse at hP,
    rw linear_change_of_variable.change_curve.comp at hP,
    rw linear_change_of_variable.comp_inv at hP,
    rw linear_change_of_variable.change_curve.id at hP,
    exact hP,
  },
end

lemma linear_change_of_variable.preserve_has_cusp {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K)
: E.has_cusp ↔ (C.change_curve E).has_cusp :=
begin
  unfold weierstrass_equation.has_cusp,
  split, {
    rintros ⟨ P, hP ⟩,
    use C.change_affine_point P,
    exact (E.change_curve_preserve_cusp C P).1 hP,
  }, {
    rintros ⟨ P, hP ⟩,
    use C.inverse.change_affine_point P,
    rw (C.change_curve E).change_curve_preserve_cusp C.inverse at hP,
    rw linear_change_of_variable.change_curve.comp at hP,
    rw linear_change_of_variable.comp_inv at hP,
    rw linear_change_of_variable.change_curve.id at hP,
    exact hP,
  },
end
