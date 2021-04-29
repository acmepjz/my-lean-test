import gtm106.weierstrass_equation.basic
import gtm106.naive_plane
import tactic

--
-- Affine points
--

def weierstrass_equation.eval_at_affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
P.y^2 + E.a1*P.x*P.y + E.a3*P.y - P.x^3 - E.a2*P.x^2 - E.a4*P.x - E.a6

def weierstrass_equation.eval_dx_at_affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
E.a1*P.y - 3*P.x^2 - 2*E.a2*P.x - E.a4

def weierstrass_equation.eval_dy_at_affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) : K :=
2*P.y + E.a1*P.x + E.a3

/--
`Prop` which asserts that an affine point is on curve
-/
def weierstrass_equation.affine_point_on_curve
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.eval_at_affine_point P = 0

/--
`Prop` which asserts that an affine point is on curve, and which is regular
-/
def weierstrass_equation.affine_point_regular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_on_curve P ∧ ¬ (E.eval_dx_at_affine_point P = 0 ∧ E.eval_dy_at_affine_point P = 0)

/--
`Prop` which asserts that an affine point is on curve, and which is singular
-/
def weierstrass_equation.affine_point_singular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :=
E.affine_point_on_curve P ∧ E.eval_dx_at_affine_point P = 0 ∧ E.eval_dy_at_affine_point P = 0

lemma weierstrass_equation.affine_point_is_regular_or_singular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_on_curve P → (¬ E.affine_point_regular P ↔ E.affine_point_singular P) :=
begin
  intro h,
  simp [h, weierstrass_equation.affine_point_regular, weierstrass_equation.affine_point_singular],
end

/--
`Prop` which asserts that all affine points on curve are regular
-/
def weierstrass_equation.affine_non_singular
{K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
∀ P : affine_plane_point K, E.affine_point_on_curve P → E.affine_point_regular P

/--
Represents all affine points on curve, with the infinity point O
-/
inductive weierstrass_equation.affine_point
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
| infinite : weierstrass_equation.affine_point
| finite (P : affine_plane_point K) (h : E.affine_point_on_curve P) : weierstrass_equation.affine_point

--
-- Projective points
--

def weierstrass_equation.eval_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
P.Y^2*P.Z + E.a1*P.X*P.Y*P.Z + E.a3*P.Y*P.Z^2 - P.X^3 - E.a2*P.X^2*P.Z - E.a4*P.X*P.Z^2 - E.a6*P.Z^3

def weierstrass_equation.eval_dX_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
E.a1*P.Y*P.Z - 3*P.X^2 - 2*E.a2*P.X*P.Z - E.a4*P.Z^2

def weierstrass_equation.eval_dY_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
2*P.Y*P.Z + E.a1*P.X*P.Z + E.a3*P.Z^2

def weierstrass_equation.eval_dZ_at_projective_point'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) : K :=
P.Y^2 + E.a1*P.X*P.Y + 2*E.a3*P.Y*P.Z - E.a2*P.X^2 - 2*E.a4*P.X*P.Z - 3*E.a6*P.Z^2

def weierstrass_equation.projective_point_on_curve'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_at_projective_point' P = 0

def weierstrass_equation.projective_point_dX_zero'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_dX_at_projective_point' P = 0

def weierstrass_equation.projective_point_dY_zero'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_dY_at_projective_point' P = 0

def weierstrass_equation.projective_point_dZ_zero'
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point' K) :=
E.eval_dZ_at_projective_point' P = 0

lemma weierstrass_equation.projective_point_on_curve'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_on_curve' P = E.projective_point_on_curve' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_at_projective_point' P'
  = (E.eval_at_projective_point' P)*a^3 := by {
    unfold weierstrass_equation.eval_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [weierstrass_equation.projective_point_on_curve', key, ha],
end

lemma weierstrass_equation.projective_point_dX_zero'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_dX_zero' P = E.projective_point_dX_zero' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_dX_at_projective_point' P'
  = (E.eval_dX_at_projective_point' P)*a^2 := by {
    unfold weierstrass_equation.eval_dX_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [weierstrass_equation.projective_point_dX_zero', key, ha],
end

lemma weierstrass_equation.projective_point_dY_zero'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_dY_zero' P = E.projective_point_dY_zero' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_dY_at_projective_point' P'
  = (E.eval_dY_at_projective_point' P)*a^2 := by {
    unfold weierstrass_equation.eval_dY_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [weierstrass_equation.projective_point_dY_zero', key, ha],
end

lemma weierstrass_equation.projective_point_dZ_zero'.sound
{K : Type*} [field K] (E : weierstrass_equation K) (P P' : projective_plane_point' K)
(h : P.is_equal P') :
E.projective_point_dZ_zero' P = E.projective_point_dZ_zero' P' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  have key : E.eval_dZ_at_projective_point' P'
  = (E.eval_dZ_at_projective_point' P)*a^2 := by {
    unfold weierstrass_equation.eval_dZ_at_projective_point',
    rw [hX, hY, hZ],
    ring,
  },
  simp [weierstrass_equation.projective_point_dZ_zero', key, ha],
end

/--
`Prop` which asserts that a projective point is on curve
-/
def weierstrass_equation.projective_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_on_curve')
(weierstrass_equation.projective_point_on_curve'.sound E) P

def weierstrass_equation.projective_point_dX_zero
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_dX_zero')
(weierstrass_equation.projective_point_dX_zero'.sound E) P

def weierstrass_equation.projective_point_dY_zero
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_dY_zero')
(weierstrass_equation.projective_point_dY_zero'.sound E) P

def weierstrass_equation.projective_point_dZ_zero
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
quotient.lift (E.projective_point_dZ_zero')
(weierstrass_equation.projective_point_dZ_zero'.sound E) P

/--
`Prop` which asserts that a projective point is on curve, and which is regular
-/
def weierstrass_equation.projective_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :=
E.projective_point_on_curve P ∧ ¬ (E.projective_point_dX_zero P
∧ E.projective_point_dY_zero P ∧ E.projective_point_dZ_zero P)

/--
`Prop` which asserts that all projective points on curve are regular
-/
def weierstrass_equation.non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :=
∀ P : projective_plane_point K, E.projective_point_on_curve P → E.projective_point_regular P

/--
Represents all projective points on curve
-/
@[ext]
structure weierstrass_equation.projective_point
{K : Type*} [field K] (E : weierstrass_equation K) :=
mk :: (P : projective_plane_point K) (h : E.projective_point_on_curve P)

--
-- Relations of affine points and projective points
--

/--
For any affine point, it is on curve if and only if
the corresponding projective point is on curve
-/
lemma weierstrass_equation.affine_point_is_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_on_curve P ↔ E.projective_point_on_curve P.to_projective_plane :=
begin
  simp [weierstrass_equation.projective_point_on_curve,
    affine_plane_point.to_projective_plane,
    weierstrass_equation.projective_point_on_curve',
    weierstrass_equation.affine_point_on_curve],
  have key : E.eval_at_projective_point' P.to_projective_plane' = E.eval_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      weierstrass_equation.eval_at_projective_point',
      weierstrass_equation.eval_at_affine_point],
  },
  rw key,
end

/--
For any affine point, it is a regular point on curve if and only if
the corresponding projective point is regular on curve
-/
lemma weierstrass_equation.affine_point_regular_iff_projective_point_regular
{K : Type*} [field K] (E : weierstrass_equation K) (P : affine_plane_point K) :
E.affine_point_regular P ↔ E.projective_point_regular P.to_projective_plane :=
begin
  have keyX : E.eval_dX_at_projective_point' P.to_projective_plane' = E.eval_dx_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      weierstrass_equation.eval_dX_at_projective_point',
      weierstrass_equation.eval_dx_at_affine_point],
  },
  have keyY : E.eval_dY_at_projective_point' P.to_projective_plane' = E.eval_dy_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      weierstrass_equation.eval_dY_at_projective_point',
      weierstrass_equation.eval_dy_at_affine_point],
  },
  have keyZ : E.eval_dZ_at_projective_point' P.to_projective_plane'
  = 3 * E.eval_at_affine_point P - P.x * E.eval_dx_at_affine_point P - P.y * E.eval_dy_at_affine_point P := by {
    simp [affine_plane_point.to_projective_plane',
      weierstrass_equation.eval_dZ_at_projective_point',
      weierstrass_equation.eval_at_affine_point,
      weierstrass_equation.eval_dx_at_affine_point,
      weierstrass_equation.eval_dy_at_affine_point],
    ring,
  },
  unfold weierstrass_equation.affine_point_regular
    weierstrass_equation.projective_point_regular
    weierstrass_equation.projective_point_dX_zero
    weierstrass_equation.projective_point_dY_zero
    weierstrass_equation.projective_point_dZ_zero,
  rw [← E.affine_point_is_projective_point P],
  simp [weierstrass_equation.affine_point_on_curve,
    affine_plane_point.to_projective_plane,
    weierstrass_equation.projective_point_dX_zero',
    weierstrass_equation.projective_point_dY_zero',
    weierstrass_equation.projective_point_dZ_zero',
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
lemma weierstrass_equation.projective_point_is_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (P : projective_plane_point K) :
E.projective_point_on_curve P ↔ P = projective_plane_point.infinite_point_Y K
∨ (P.is_finite ∧ E.affine_point_on_curve P.to_affine_plane) :=
begin
  split, {
    revert P,
    refine quotient.ind _,
    simp [weierstrass_equation.projective_point_on_curve,
      projective_plane_point.infinite_point_Y,
      projective_plane_point.is_finite,
      projective_plane_point.to_affine_plane],
    intro P,
    have h1 := P.h,
    intro h2,
    unfold weierstrass_equation.projective_point_on_curve' at h2,
    by_cases hZ : P.Z = 0, {
      left,
      simp [weierstrass_equation.eval_at_projective_point',
        hZ, zero_pow] at h2,
      simp [hZ, h2] at h1,
      use 1/P.Y,
      simp [projective_plane_point'.infinite_point_Y, h1, h2, hZ],
    },
    right,
    use hZ,
    calc E.eval_at_affine_point P.to_affine_plane
    = (E.eval_at_projective_point' P)/P.Z^3 : by {
      simp [weierstrass_equation.eval_at_projective_point',
        weierstrass_equation.eval_at_affine_point,
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
    simp [weierstrass_equation.projective_point_on_curve,
      projective_plane_point.infinite_point_Y,
      weierstrass_equation.projective_point_on_curve',
      weierstrass_equation.eval_at_projective_point',
      projective_plane_point'.infinite_point_Y, zero_pow],
  },
  rw [E.affine_point_is_projective_point, ← P.embed_invertible h1] at h2,
  exact h2,
end

/--
The point `[0:1:0]` is on curve and is regular
-/
lemma weierstrass_equation.infinite_point_is_regular
{K : Type*} [field K] (E : weierstrass_equation K) : E.projective_point_regular (projective_plane_point.infinite_point_Y K) :=
begin
  simp [projective_plane_point.infinite_point_Y,
    weierstrass_equation.projective_point_regular,
    weierstrass_equation.projective_point_on_curve,
    weierstrass_equation.projective_point_dX_zero,
    weierstrass_equation.projective_point_dY_zero,
    weierstrass_equation.projective_point_dZ_zero,
    projective_plane_point'.infinite_point_Y,
    weierstrass_equation.projective_point_on_curve',
    weierstrass_equation.projective_point_dX_zero',
    weierstrass_equation.projective_point_dY_zero',
    weierstrass_equation.projective_point_dZ_zero',
    weierstrass_equation.eval_at_projective_point',
    weierstrass_equation.eval_dX_at_projective_point',
    weierstrass_equation.eval_dY_at_projective_point',
    weierstrass_equation.eval_dZ_at_projective_point',
    zero_pow],
end

/--
All projective points on curve are regular if and only if
all affine points on curve are regular
-/
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
    rw h1,
    exact E.infinite_point_is_regular,
  },
  replace h := h P.to_affine_plane h2,
  rw [E.affine_point_regular_iff_projective_point_regular, ← P.embed_invertible h1] at h,
  exact h,
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
  simp [h1, weierstrass_equation.affine_point_is_node,
    weierstrass_equation.affine_point_is_cusp],
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
  simp [weierstrass_equation.affine_non_singular,
    weierstrass_equation.has_affine_singular_point],
  split, {
    intro h,
    rcases h with ⟨ P, h1, h2 ⟩,
    use [P, h1],
    unfold weierstrass_equation.affine_point_regular at h2,
    finish,
  },
  intro h,
  rcases h with ⟨ P, h1, h2 ⟩,
  use [P, h1],
  unfold weierstrass_equation.affine_point_regular,
  finish,
end
