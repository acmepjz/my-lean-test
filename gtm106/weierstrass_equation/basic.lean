import algebra.field
import gtm106.naive_plane
import tactic

noncomputable theory

@[ext]
structure weierstrass_equation (K : Type*) [field K] :=
mk :: (a1 a2 a3 a4 a6 : K)

def weierstrass_equation.eval_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
P.y^2 + E.a1*P.x*P.y + E.a3*P.y - P.x^3 - E.a2*P.x^2 - E.a4*P.x - E.a6

def weierstrass_equation.eval_dx_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
E.a1*P.y - 3*P.x^2 - 2*E.a2*P.x - E.a4

def weierstrass_equation.eval_dy_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
2*P.y + E.a1*P.x + E.a3

def weierstrass_equation.affine_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.eval_at_affine_point P = 0

def weierstrass_equation.affine_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_on_curve P ∧ ¬ (E.eval_dx_at_affine_point P = 0 ∧ E.eval_dy_at_affine_point P = 0)

def weierstrass_equation.affine_point_singular
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_on_curve P ∧ E.eval_dx_at_affine_point P = 0 ∧ E.eval_dy_at_affine_point P = 0

lemma weierstrass_equation.affine_point_is_regular_or_singular
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_on_curve P → (¬ E.affine_point_regular P ↔ E.affine_point_singular P) :=
begin
  intro h1,
  unfold weierstrass_equation.affine_point_regular
  weierstrass_equation.affine_point_singular,
  finish,
end

def weierstrass_equation.affine_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :=
∀ P : affine_plane_point K, E.affine_point_on_curve P → E.affine_point_regular P

def weierstrass_equation.eval_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) : K :=
P.Y^2*P.Z + E.a1*P.X*P.Y*P.Z + E.a3*P.Y*P.Z^2 - P.X^3 - E.a2*P.X^2*P.Z - E.a4*P.X*P.Z^2 - E.a6*P.Z^3

def weierstrass_equation.eval_dX_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) : K :=
E.a1*P.Y*P.Z - 3*P.X^2 - 2*E.a2*P.X*P.Z - E.a4*P.Z^2

def weierstrass_equation.eval_dY_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) : K :=
2*P.Y*P.Z + E.a1*P.X*P.Z + E.a3*P.Z^2

def weierstrass_equation.eval_dZ_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) : K :=
P.Y^2 + E.a1*P.X*P.Y + 2*E.a3*P.Y*P.Z - E.a2*P.X^2 - 2*E.a4*P.X*P.Z - 3*E.a6*P.Z^2

def weierstrass_equation.projective_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
E.eval_at_projective_point P = 0

def weierstrass_equation.projective_point_on_curve.equal
{K : Type*} [field K] (E : weierstrass_equation K) {P P' : projective_plane_point K}
(h : P.is_equal P') :
E.projective_point_on_curve P ↔ E.projective_point_on_curve P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key := calc E.eval_at_projective_point P'
  = (E.eval_at_projective_point P)*a^3 : by {
    unfold weierstrass_equation.eval_at_projective_point,
    rw [hX, hY, hZ],
    ring,
  },
  unfold weierstrass_equation.projective_point_on_curve,
  rw key,
  field_simp [ha],
end

def weierstrass_equation.projective_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
E.projective_point_on_curve P ∧ ¬ (E.eval_dX_at_projective_point P = 0
∧ E.eval_dY_at_projective_point P = 0 ∧ E.eval_dZ_at_projective_point P = 0)

lemma weierstrass_equation.projective_point_regular.equal
{K : Type*} [field K] (E : weierstrass_equation K) {P P' : projective_plane_point K}
(h : P.is_equal P') :
E.projective_point_regular P ↔ E.projective_point_regular P' :=
begin
  have hh := h,
  rcases hh with ⟨ a, ha, hX, hY, hZ ⟩,
  have keyX := calc E.eval_dX_at_projective_point P'
  = (E.eval_dX_at_projective_point P)*a^2 : by {
    unfold weierstrass_equation.eval_dX_at_projective_point,
    rw [hX, hY, hZ],
    ring,
  },
  have keyY := calc E.eval_dY_at_projective_point P'
  = (E.eval_dY_at_projective_point P)*a^2 : by {
    unfold weierstrass_equation.eval_dY_at_projective_point,
    rw [hX, hY, hZ],
    ring,
  },
  have keyZ := calc E.eval_dZ_at_projective_point P'
  = (E.eval_dZ_at_projective_point P)*a^2 : by {
    unfold weierstrass_equation.eval_dZ_at_projective_point,
    rw [hX, hY, hZ],
    ring,
  },
  split, {
    intro h1,
    use (weierstrass_equation.projective_point_on_curve.equal E h).1 h1.1,
    intro h2,
    rw [keyX, keyY, keyZ] at h2,
    field_simp [ha] at h2,
    exact h1.2 h2,
  }, {
    intro h1,
    use (weierstrass_equation.projective_point_on_curve.equal E h).2 h1.1,
    intro h2,
    rw h2.1 at keyX,
    rw h2.2.1 at keyY,
    rw h2.2.2 at keyZ,
    ring at keyX keyY keyZ,
    exact h1.2 ⟨ keyX, keyY, keyZ ⟩,
  },
end

def weierstrass_equation.non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :=
∀ P : projective_plane_point K, E.projective_point_on_curve P → E.projective_point_regular P

lemma weierstrass_equation.affine_point_is_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_on_curve P ↔ E.projective_point_on_curve P.to_projective_plane :=
begin
  have key := calc E.eval_at_projective_point P.to_projective_plane = E.eval_at_affine_point P : by {
    unfold affine_plane_point.to_projective_plane
    projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z
    weierstrass_equation.eval_at_projective_point
    weierstrass_equation.eval_at_affine_point,
    ring,
  },
  unfold weierstrass_equation.affine_point_on_curve
  weierstrass_equation.projective_point_on_curve,
  rw key,
end

lemma weierstrass_equation.affine_point_regular_iff_projective_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_regular P ↔ E.projective_point_regular P.to_projective_plane :=
begin
  have keyX := calc E.eval_dX_at_projective_point P.to_projective_plane = E.eval_dx_at_affine_point P : by {
    unfold affine_plane_point.to_projective_plane
    projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z
    weierstrass_equation.eval_dX_at_projective_point
    weierstrass_equation.eval_dx_at_affine_point,
    ring,
  },
  have keyY := calc E.eval_dY_at_projective_point P.to_projective_plane = E.eval_dy_at_affine_point P : by {
    unfold affine_plane_point.to_projective_plane
    projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z
    weierstrass_equation.eval_dY_at_projective_point
    weierstrass_equation.eval_dy_at_affine_point,
    ring,
  },
  have keyZ := calc E.eval_dZ_at_projective_point P.to_projective_plane =
  3 * E.eval_at_affine_point P - P.x * E.eval_dx_at_affine_point P - P.y * E.eval_dy_at_affine_point P : by {
    unfold affine_plane_point.to_projective_plane
    projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z
    weierstrass_equation.eval_dZ_at_projective_point
    weierstrass_equation.eval_at_affine_point
    weierstrass_equation.eval_dx_at_affine_point
    weierstrass_equation.eval_dy_at_affine_point,
    ring,
  },
  unfold weierstrass_equation.affine_point_regular
  weierstrass_equation.projective_point_regular,
  rw [← E.affine_point_is_projective_point P, keyX, keyY],
  unfold weierstrass_equation.affine_point_on_curve,
  split, {
    intro h,
    use h.1,
    intro hh,
    exact h.2 ⟨ hh.1, hh.2.1 ⟩,
  }, {
    intro h,
    use h.1,
    intro hh,
    rw [h.1, hh.1, hh.2] at keyZ,
    ring at keyZ,
    rw keyZ at h,
    simp at h,
    exact h.2 hh.1 hh.2,
  },
end

lemma weierstrass_equation.projective_point_is_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :
E.projective_point_on_curve P ↔ P.is_equal (projective_plane_point.infinite_point_Y K)
∨ (P.is_finite ∧ E.affine_point_on_curve P.to_affine_plane) :=
begin
  split, {
    have h1 := P.h,
    intro h2,
    unfold weierstrass_equation.projective_point_on_curve at h2,
    by_cases hZ : P.Z = 0, {
      left,
      unfold weierstrass_equation.eval_at_projective_point at h2,
      rw hZ at h2,
      ring at h2,
      field_simp at h2,
      replace h1 : P.Y ≠ 0 := by { intro h, exact h1 ⟨ h2, h, hZ ⟩, },
      use 1/P.Y,
      unfold projective_plane_point.infinite_point_Y
      projective_plane_point.X
      projective_plane_point.Y
      projective_plane_point.Z,
      rw [hZ, h2],
      field_simp [h1],
    },
    right,
    use hZ,
    calc E.eval_at_affine_point P.to_affine_plane
    = (E.eval_at_projective_point P)/P.Z^3 : by {
      unfold weierstrass_equation.eval_at_projective_point
      weierstrass_equation.eval_at_affine_point
      projective_plane_point.to_affine_plane
      affine_plane_point.x
      affine_plane_point.y,
      field_simp [pow_succ, hZ],
      ring,
    }
    ... = 0 : by {
      rw h2, ring,
    },
  },
  intro h,
  rcases h with h | ⟨ h1, h2 ⟩, {
    rw weierstrass_equation.projective_point_on_curve.equal E h,
    unfold weierstrass_equation.projective_point_on_curve
    weierstrass_equation.eval_at_projective_point
    projective_plane_point.infinite_point_Y
    projective_plane_point.X
    projective_plane_point.Y
    projective_plane_point.Z,
    simp, ring,
  },
  rw E.affine_point_is_projective_point at h2,
  rw ← weierstrass_equation.projective_point_on_curve.equal E (P.embed_invertible h1) at h2,
  exact h2,
end

lemma weierstrass_equation.infinite_point_is_regular
{K : Type*} [field K] (E : weierstrass_equation K) : E.projective_point_regular (projective_plane_point.infinite_point_Y K) :=
begin
  unfold weierstrass_equation.projective_point_regular
  weierstrass_equation.projective_point_on_curve
  projective_plane_point.infinite_point_Y
  projective_plane_point.X
  projective_plane_point.Y
  projective_plane_point.Z
  weierstrass_equation.eval_at_projective_point
  weierstrass_equation.eval_dX_at_projective_point
  weierstrass_equation.eval_dY_at_projective_point
  weierstrass_equation.eval_dZ_at_projective_point,
  ring,
  simp,
end

def weierstrass_equation.b2 {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.a1^2 + 4*E.a2

def weierstrass_equation.b4 {K : Type*} [field K] (E : weierstrass_equation K) : K :=
2*E.a4 + E.a1*E.a3

def weierstrass_equation.b6 {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.a3^2 + 4*E.a6

def weierstrass_equation.b8 {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.a1^2*E.a6 + 4*E.a2*E.a6 - E.a1*E.a3*E.a4 + E.a2*E.a3^2 - E.a4^2

def weierstrass_equation.c4 {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.b2^2 - 24*E.b4

def weierstrass_equation.c6 {K : Type*} [field K] (E : weierstrass_equation K) : K :=
-E.b2^3 + 36*E.b2*E.b4 - 216*E.b6

def weierstrass_equation.disc {K : Type*} [field K] (E : weierstrass_equation K) : K :=
-E.b2^2*E.b8 - 8*E.b4^3 - 27*E.b6^2 + 9*E.b2*E.b4*E.b6

lemma weierstrass_equation.b8_mul_4 {K : Type*} [field K] (E : weierstrass_equation K) :
4*E.b8 = E.b2*E.b6 - E.b4^2 :=
begin
  unfold weierstrass_equation.b8
  weierstrass_equation.b6
  weierstrass_equation.b4
  weierstrass_equation.b2,
  ring,
end

lemma weierstrass_equation.disc_mul_1728 {K : Type*} [field K] (E : weierstrass_equation K) :
1728*E.disc = E.c4^3 - E.c6^2 :=
begin
  unfold weierstrass_equation.disc
  weierstrass_equation.c4
  weierstrass_equation.c6
  weierstrass_equation.b8
  weierstrass_equation.b6
  weierstrass_equation.b4
  weierstrass_equation.b2,
  ring,
end

def weierstrass_equation.non_singular' {K : Type*} [field K] (E : weierstrass_equation K) :=
E.disc ≠ 0

def weierstrass_equation.has_node' {K : Type*} [field K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 ≠ 0

def weierstrass_equation.has_cusp' {K : Type*} [field K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 = 0

def weierstrass_equation.j {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.c4^3/E.disc

lemma weierstrass_equation.non_singular_iff_affine_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :
E.non_singular ↔ E.affine_non_singular :=
begin
  split, {
    intros h P,
    rw [E.affine_point_is_projective_point, E.affine_point_regular_iff_projective_point_regular],
    exact h P.to_projective_plane,
  },
  intros h P h1,
  rw E.projective_point_is_affine_point at h1,
  rcases h1 with h1 | ⟨ h1, h2 ⟩, {
    rw weierstrass_equation.projective_point_regular.equal E h1,
    exact E.infinite_point_is_regular,
  },
  replace h := h P.to_affine_plane,
  rw E.affine_point_regular_iff_projective_point_regular at h,
  rw ← weierstrass_equation.projective_point_regular.equal E (P.embed_invertible h1) at h,
  exact h h2,
end

/-
def weierstrass_equation.eval_dxdx_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
-6*P.x - 2*E.a2

def weierstrass_equation.eval_dxdy_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
E.a1

def weierstrass_equation.eval_dydy_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
2

def weierstrass_equation.eval_hessian_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
(E.eval_dxdx_at_affine_point P)*(E.eval_dydy_at_affine_point P) - (E.eval_dxdy_at_affine_point P)^2
-/

def weierstrass_equation.eval_hessian_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
-12*P.x - E.b2

def weierstrass_equation.affine_point_is_node
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_singular P ∧ E.eval_hessian_at_affine_point P ≠ 0

def weierstrass_equation.affine_point_is_cusp
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_singular P ∧ E.eval_hessian_at_affine_point P = 0

lemma weierstrass_equation.singular_point_is_node_or_cusp
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_singular P → (¬ E.affine_point_is_node P ↔ E.affine_point_is_cusp P) :=
begin
  intro h1,
  unfold weierstrass_equation.affine_point_is_node
  weierstrass_equation.affine_point_is_cusp,
  finish,
end

def weierstrass_equation.has_affine_singular_point
{K : Type*} [field K] (E : weierstrass_equation K) :=
∃ P : affine_plane_point K, E.affine_point_singular P

def weierstrass_equation.has_node
{K : Type*} [field K] (E : weierstrass_equation K) :=
∃ P : affine_plane_point K, E.affine_point_is_node P

def weierstrass_equation.has_cusp
{K : Type*} [field K] (E : weierstrass_equation K) :=
∃ P : affine_plane_point K, E.affine_point_is_cusp P

lemma weierstrass_equation.singular_iff_has_affine_singular_point
{K : Type*} [field K] (E : weierstrass_equation K) :
¬ E.non_singular ↔ E.has_affine_singular_point :=
begin
  rw E.non_singular_iff_affine_non_singular,
  split, {
    intro h,
    unfold weierstrass_equation.affine_non_singular at h,
    push_neg at h,
    rcases h with ⟨ P, h1, h2 ⟩,
    use [P, h1],
    unfold weierstrass_equation.affine_point_regular at h2,
    finish,
  },
  intros h1 h,
  rcases h1 with ⟨ P, h1, h2 ⟩,
  replace h := h P h1,
  unfold weierstrass_equation.affine_point_regular at h,
  finish,
end
