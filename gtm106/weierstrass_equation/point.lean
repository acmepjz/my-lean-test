import gtm106.weierstrass_equation.basic
import gtm106.naive_plane
import tactic

namespace weierstrass_equation

-- ================
-- Affine points
-- ================

def eval_at_affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
P.y^2 + E.a1*P.x*P.y + E.a3*P.y - P.x^3 - E.a2*P.x^2 - E.a4*P.x - E.a6

def eval_dx_at_affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
E.a1*P.y - 3*P.x^2 - 2*E.a2*P.x - E.a4

def eval_dy_at_affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
2*P.y + E.a1*P.x + E.a3

/--
`Prop` which asserts that an affine point is on curve
-/
def affine_point_on_curve
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.eval_at_affine_point P = 0

/--
`Prop` which asserts that an affine point is on curve, and which is regular
-/
def affine_point_regular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_on_curve P ∧ ¬ (E.eval_dx_at_affine_point P = 0 ∧ E.eval_dy_at_affine_point P = 0)

/--
`Prop` which asserts that an affine point is on curve, and which is singular
-/
def affine_point_singular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_on_curve P ∧ E.eval_dx_at_affine_point P = 0 ∧ E.eval_dy_at_affine_point P = 0

lemma affine_point_is_regular_or_singular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_on_curve P → (¬ E.affine_point_regular P ↔ E.affine_point_singular P) :=
begin
  intro h,
  simp [h, affine_point_regular, affine_point_singular],
end

/--
`Prop` which asserts that all affine points on curve are regular
-/
def affine_non_singular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
∀ P : affine_plane_point K, E.affine_point_on_curve P → E.affine_point_regular P

/--
Represents all affine points on curve, with the infinity point O
-/
inductive affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
| infinite : affine_point
| finite (P : affine_plane_point K) (h : E.affine_point_on_curve P) : affine_point

-- ================
-- Projective points
-- ================

def eval_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
P.Y^2*P.Z + E.a1*P.X*P.Y*P.Z + E.a3*P.Y*P.Z^2 - P.X^3 - E.a2*P.X^2*P.Z - E.a4*P.X*P.Z^2 - E.a6*P.Z^3

def eval_dX_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
E.a1*P.Y*P.Z - 3*P.X^2 - 2*E.a2*P.X*P.Z - E.a4*P.Z^2

def eval_dY_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
2*P.Y*P.Z + E.a1*P.X*P.Z + E.a3*P.Z^2

def eval_dZ_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
P.Y^2 + E.a1*P.X*P.Y + 2*E.a3*P.Y*P.Z - E.a2*P.X^2 - 2*E.a4*P.X*P.Z - 3*E.a6*P.Z^2

def projective_point_on_curve'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_at_projective_point' P = 0

def projective_point_dX_zero'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_dX_at_projective_point' P = 0

def projective_point_dY_zero'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_dY_at_projective_point' P = 0

def projective_point_dZ_zero'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_dZ_at_projective_point' P = 0

lemma projective_point_on_curve'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_on_curve' P = E.projective_point_on_curve' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_at_projective_point' P'
  = (E.eval_at_projective_point' P)*a^3 := by {
    unfold eval_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [projective_point_on_curve', key, ha],
end

lemma projective_point_dX_zero'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_dX_zero' P = E.projective_point_dX_zero' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_dX_at_projective_point' P'
  = (E.eval_dX_at_projective_point' P)*a^2 := by {
    unfold eval_dX_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [projective_point_dX_zero', key, ha],
end

lemma projective_point_dY_zero'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_dY_zero' P = E.projective_point_dY_zero' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_dY_at_projective_point' P'
  = (E.eval_dY_at_projective_point' P)*a^2 := by {
    unfold eval_dY_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [projective_point_dY_zero', key, ha],
end

lemma projective_point_dZ_zero'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_dZ_zero' P = E.projective_point_dZ_zero' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_dZ_at_projective_point' P'
  = (E.eval_dZ_at_projective_point' P)*a^2 := by {
    unfold eval_dZ_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [projective_point_dZ_zero', key, ha],
end

/--
`Prop` which asserts that a projective point is on curve
-/
def projective_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_on_curve')
(projective_point_on_curve'.sound E) P

def projective_point_dX_zero
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_dX_zero')
(projective_point_dX_zero'.sound E) P

def projective_point_dY_zero
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_dY_zero')
(projective_point_dY_zero'.sound E) P

def projective_point_dZ_zero
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_dZ_zero')
(projective_point_dZ_zero'.sound E) P

/--
`Prop` which asserts that a projective point is on curve, and which is regular
-/
def projective_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
E.projective_point_on_curve P ∧ ¬ (E.projective_point_dX_zero P
∧ E.projective_point_dY_zero P ∧ E.projective_point_dZ_zero P)

/--
`Prop` which asserts that all projective points on curve are regular
-/
def non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :=
∀ P : projective_plane_point K, E.projective_point_on_curve P → E.projective_point_regular P

/--
Represents all projective points on curve
-/
@[ext]
structure projective_point
{K : Type*} [field K] (E : weierstrass_equation K) :=
mk :: (P : projective_plane_point K) (h : E.projective_point_on_curve P)

-- ================
-- Relations of affine points and projective points
-- ================

/--
For any affine point, it is on curve if and only if
the corresponding projective point is on curve
-/
lemma affine_point_is_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_on_curve P ↔ E.projective_point_on_curve P.to_projective_plane :=
begin
  simp [projective_point_on_curve,
    affine_plane_point.to_projective_plane,
    projective_point_on_curve',
    affine_point_on_curve],
  have key : E.eval_at_projective_point' P.to_projective_plane' = E.eval_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      eval_at_projective_point',
      eval_at_affine_point],
  },
  rw key,
end

/--
For any affine point, it is a regular point on curve if and only if
the corresponding projective point is regular on curve
-/
lemma affine_point_regular_iff_projective_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_regular P ↔ E.projective_point_regular P.to_projective_plane :=
begin
  have keyX : E.eval_dX_at_projective_point' P.to_projective_plane' = E.eval_dx_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      eval_dX_at_projective_point',
      eval_dx_at_affine_point],
  },
  have keyY : E.eval_dY_at_projective_point' P.to_projective_plane' = E.eval_dy_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      eval_dY_at_projective_point',
      eval_dy_at_affine_point],
  },
  have keyZ : E.eval_dZ_at_projective_point' P.to_projective_plane'
  = 3 * E.eval_at_affine_point P - P.x * E.eval_dx_at_affine_point P - P.y * E.eval_dy_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      eval_dZ_at_projective_point',
      eval_at_affine_point,
      eval_dx_at_affine_point,
      eval_dy_at_affine_point],
    ring,
  },
  unfold affine_point_regular
    projective_point_regular
    projective_point_dX_zero
    projective_point_dY_zero
    projective_point_dZ_zero,
  rw [← E.affine_point_is_projective_point P],
  simp [affine_point_on_curve,
    affine_plane_point.to_projective_plane,
    projective_point_dX_zero',
    projective_point_dY_zero',
    projective_point_dZ_zero',
    keyX, keyY, keyZ],
  intro h,
  split, {
    intros h1 h2 h3,
    exfalso,
    exact h1 h2 h3,
  },
  intros h1 h2 h3,
  rw [h, h2, h3] at h1,
  simp at h1,
  exact h1,
end

/--
For any projective point, it is on curve if and only if it is `[0:1:0]`
or it is a finite point and the corresponding affine point is on curve
-/
lemma projective_point_is_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :
E.projective_point_on_curve P ↔ P = projective_plane_point.infinite_point_Y K
∨ (P.is_finite ∧ E.affine_point_on_curve P.to_affine_plane) :=
begin
  split, {
    revert P,
    refine quotient.ind _,
    simp [projective_point_on_curve,
      projective_plane_point.infinite_point_Y,
      projective_plane_point.is_finite,
      projective_plane_point.to_affine_plane],
    intro P,
    have h1 := P.h,
    intro h2,
    unfold projective_point_on_curve' at h2,
    by_cases hZ : P.Z = 0, {
      left,
      simp [eval_at_projective_point',
        hZ, zero_pow] at h2,
      simp [hZ, h2] at h1,
      use 1/P.Y,
      simp [projective_plane_point'.infinite_point_Y, h1, h2, hZ],
    },
    right,
    use hZ,
    calc E.eval_at_affine_point P.to_affine_plane
    = (E.eval_at_projective_point' P)/P.Z^3 : by {
      simp [eval_at_projective_point',
        eval_at_affine_point,
        projective_plane_point'.to_affine_plane],
      field_simp [pow_succ, hZ],
      ring,
    }
    ... = 0 : by {
      simp [h2],
    },
  },
  intro h,
  rcases h with h | ⟨ h1, h2 ⟩, {
    rw h,
    simp [projective_point_on_curve,
      projective_plane_point.infinite_point_Y,
      projective_point_on_curve',
      eval_at_projective_point',
      projective_plane_point'.infinite_point_Y, zero_pow],
  },
  rw [E.affine_point_is_projective_point, P.embed_invertible h1] at h2,
  exact h2,
end

/--
The point `[0:1:0]` is on curve and is regular
-/
@[simp]
lemma infinite_point_is_regular
{K : Type*} [field K] (E : weierstrass_equation K) : E.projective_point_regular (projective_plane_point.infinite_point_Y K) :=
begin
  simp [projective_plane_point.infinite_point_Y,
    projective_point_regular,
    projective_point_on_curve,
    projective_point_dX_zero,
    projective_point_dY_zero,
    projective_point_dZ_zero,
    projective_plane_point'.infinite_point_Y,
    projective_point_on_curve',
    projective_point_dX_zero',
    projective_point_dY_zero',
    projective_point_dZ_zero',
    eval_at_projective_point',
    eval_dX_at_projective_point',
    eval_dY_at_projective_point',
    eval_dZ_at_projective_point',
    zero_pow],
end

def affine_point.to_projective_point
{K : Type*} [field K] {E : weierstrass_equation K}
: affine_point E → projective_point E
| affine_point.infinite := ⟨ projective_plane_point.infinite_point_Y K, E.infinite_point_is_regular.1 ⟩
| (affine_point.finite P h) := ⟨ P.to_projective_plane, (E.affine_point_is_projective_point P).1 h ⟩

noncomputable def projective_point.to_affine_point
{K : Type*} [field K] {E : weierstrass_equation K}
(P : projective_point E) : affine_point E :=
begin
  by_cases h : P.P.is_finite, {
    exact affine_point.finite P.P.to_affine_plane (by {
      rcases (E.projective_point_is_affine_point P.P).1 P.h with h1 | ⟨ h2, h3 ⟩, {
        exfalso,
        simp [h1, projective_plane_point.infinite_point_Y,
          projective_plane_point'.infinite_point_Y,
          projective_plane_point.is_finite,
          projective_plane_point'.is_finite] at h,
        exact h,
      },
      exact h3,
    }),
  },
  exact affine_point.infinite,
end

@[simp]
lemma affine_point.embed_invertible
{K : Type*} [field K] {E : weierstrass_equation K}
(P : affine_point E) : P.to_projective_point.to_affine_point = P :=
match P with
| affine_point.infinite := by {
  simp [affine_point.to_projective_point,
    projective_plane_point.infinite_point_Y,
    projective_plane_point'.infinite_point_Y,
    projective_plane_point.is_finite,
    projective_plane_point'.is_finite,
    projective_point.to_affine_point],
}
| (affine_point.finite P h) := by {
  simp [affine_point.to_projective_point,
    affine_plane_point.to_projective_plane,
    affine_plane_point.to_projective_plane',
    projective_plane_point.is_finite,
    projective_plane_point'.is_finite,
    projective_point.to_affine_point,
    projective_plane_point.to_affine_plane,
    projective_plane_point'.to_affine_plane,
    affine_plane_point.ext_iff],
}
end

@[simp]
lemma projective_point.embed_invertible
{K : Type*} [field K] {E : weierstrass_equation K}
(P : projective_point E) : P.to_affine_point.to_projective_point = P :=
begin
  by_cases h : P.P.is_finite, {
    simp [projective_point.to_affine_point, h,
      affine_point.to_projective_point,
      projective_point.ext_iff,
      projective_plane_point.embed_invertible],
  },
  simp [projective_point.to_affine_point, h,
    affine_point.to_projective_point,
    projective_point.ext_iff],
  have h1 := (E.projective_point_is_affine_point P.P).1 P.h,
  simp [h] at h1,
  exact h1.symm,
end

noncomputable def affine_point_equiv_to_projective_point
{K : Type*} [field K] (E : weierstrass_equation K)
: equiv E.affine_point E.projective_point :=
⟨ affine_point.to_projective_point, projective_point.to_affine_point,
  affine_point.embed_invertible, projective_point.embed_invertible ⟩

/--
All projective points on curve are regular if and only if
all affine points on curve are regular
-/
lemma non_singular_iff_affine_non_singular
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
    rw h1,
    exact E.infinite_point_is_regular,
  },
  replace h := h P.to_affine_plane h2,
  rw [E.affine_point_regular_iff_projective_point_regular, P.embed_invertible h1] at h,
  exact h,
end

-- ================
-- Singular point: node and cusp
-- ================

def has_affine_singular_point
{K : Type*} [field K] (E : weierstrass_equation K) :=
∃ P : affine_plane_point K, E.affine_point_singular P

lemma singular_iff_has_affine_singular_point
{K : Type*} [field K] (E : weierstrass_equation K) :
¬ E.non_singular ↔ E.has_affine_singular_point :=
begin
  rw E.non_singular_iff_affine_non_singular,
  simp [affine_non_singular, has_affine_singular_point],
  split, {
    intro h,
    rcases h with ⟨ P, h1, h2 ⟩,
    use [P, h1],
    unfold affine_point_regular at h2,
    finish,
  },
  intro h,
  rcases h with ⟨ P, h1, h2 ⟩,
  use [P, h1],
  unfold affine_point_regular,
  finish,
end

/-
def eval_dxdx_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
-6*P.x - 2*E.a2

def eval_dxdy_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
E.a1

def eval_dydy_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
2

def eval_hessian_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
(E.eval_dxdx_at_affine_point P)*(E.eval_dydy_at_affine_point P) - (E.eval_dxdy_at_affine_point P)^2
-/

def eval_hessian_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
-12*P.x - E.b2

def affine_point_is_node
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_singular P ∧ E.eval_hessian_at_affine_point P ≠ 0

def affine_point_is_cusp
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_singular P ∧ E.eval_hessian_at_affine_point P = 0

lemma singular_point_is_node_or_cusp
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_singular P → (¬ E.affine_point_is_node P ↔ E.affine_point_is_cusp P) :=
begin
  intro h1,
  simp [h1, affine_point_is_node, affine_point_is_cusp],
end

def has_node
{K : Type*} [field K] (E : weierstrass_equation K) :=
∃ P : affine_plane_point K, E.affine_point_is_node P

def has_cusp
{K : Type*} [field K] (E : weierstrass_equation K) :=
∃ P : affine_plane_point K, E.affine_point_is_cusp P

end weierstrass_equation
