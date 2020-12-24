import algebra.field
-- import algebra.algebra.basic
import data.int.basic
import data.rat.basic
-- import tests.gtm106.naive_algebraic_geometry
import tactic

noncomputable theory

structure weierstrass_equation (K : Type*) [field K] :=
mk :: (a1 a2 a3 a4 a6 : K)

/-
def weierstrass_equation.affine_curve {K : Type*} [field K] (E : weierstrass_equation K)
: naive_affine_hypersurface (naive_affine_space.mk1 K 2)
:= naive_affine_hypersurface.mk (by {
  let A := naive_affine_space.mk1 K 2,
  let x := A.x_i 0 (by norm_num),
  let y := A.x_i 1 (by norm_num),
  use x, -- y^2 + E.a1*x*y + E.a3*y - x^3 - E.a2*x^2 - E.a4*x - E.a6,
})
-/

def weierstrass_equation.eval_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) : K :=
y^2 + E.a1*x*y + E.a3*y - x^3 - E.a2*x^2 - E.a4*x - E.a6

def weierstrass_equation.eval_dx_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) : K :=
E.a1*y - 3*x^2 - 2*E.a2*x - E.a4

def weierstrass_equation.eval_dy_at_affine_point
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) : K :=
2*y + E.a1*x + E.a3

def weierstrass_equation.affine_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) :=
E.eval_at_affine_point x y = 0

def weierstrass_equation.affine_point_smooth
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) :=
E.affine_point_on_curve x y ∧ ¬ (E.eval_dx_at_affine_point x y = 0 ∧ E.eval_dy_at_affine_point x y = 0)

def weierstrass_equation.affine_smooth
{K : Type*} [field K] (E : weierstrass_equation K) :=
∀ x y : K, E.affine_point_on_curve x y → E.affine_point_smooth x y

def is_projective_point {K : Type*} [field K] (X Y Z : K) :=
¬ (X = 0 ∧ Y = 0 ∧ Z = 0)

def is_projective_point_equal {K : Type*} [field K] (X Y Z X' Y' Z' : K) :=
∃ a : K, a ≠ 0 ∧ X' = a * X ∧ Y' = a * Y ∧ Z' = a * Z

lemma is_projective_point.equal {K : Type*} [field K] {X Y Z X' Y' Z' : K}
(h : is_projective_point_equal X Y Z X' Y' Z') :
is_projective_point X Y Z ↔ is_projective_point X' Y' Z' :=
begin
  rcases h with ⟨ a, ha, hX, hY, hZ ⟩,
  split, {
    intros h h',
    rw [hX, hY, hZ] at h',
    field_simp [ha] at h',
    exact h h',
  }, {
    intros h h',
    have : X' = 0 ∧ Y' = 0 ∧ Z' = 0 := by {
      rw [hX, hY, hZ, h'.1, h'.2.1, h'.2.2],
      simp,
    },
    exact h this,
  },
end

def is_finite_projective_point {K : Type*} [field K] (X Y Z : K) :=
is_projective_point X Y Z ∧ Z ≠ 0

def is_infinite_projective_point {K : Type*} [field K] (X Y Z : K) :=
is_projective_point X Y Z ∧ Z = 0

def weierstrass_equation.eval_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) : K :=
Y^2*Z + E.a1*X*Y*Z + E.a3*Y*Z^2 - X^3 - E.a2*X^2*Z - E.a4*X*Z^2 - E.a6*Z^3

def weierstrass_equation.eval_dX_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) : K :=
E.a1*Y*Z - 3*X^2 - 2*E.a2*X*Z - E.a4*Z^2

def weierstrass_equation.eval_dY_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) : K :=
2*Y*Z + E.a1*X*Z + E.a3*Z^2

def weierstrass_equation.eval_dZ_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) : K :=
Y^2 + E.a1*X*Y + 2*E.a3*Y*Z - E.a2*X^2 - 2*E.a4*X*Z - 3*E.a6*Z^2

def weierstrass_equation.projective_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) :=
is_projective_point X Y Z ∧ E.eval_at_projective_point X Y Z = 0

def weierstrass_equation.projective_point_on_curve.equal
{K : Type*} [field K] (E : weierstrass_equation K) {X Y Z X' Y' Z' : K}
(h : is_projective_point_equal X Y Z X' Y' Z') :
E.projective_point_on_curve X Y Z ↔ E.projective_point_on_curve X' Y' Z' :=
begin
  have hh := h,
  rcases hh with ⟨ a, ha, hX, hY, hZ ⟩,
  have key := calc E.eval_at_projective_point X' Y' Z'
  = (E.eval_at_projective_point X Y Z)*a^3 : by {
    rw [hX, hY, hZ],
    unfold weierstrass_equation.eval_at_projective_point,
    ring,
  },
  unfold weierstrass_equation.projective_point_on_curve,
  rw [is_projective_point.equal h, key],
  field_simp [ha],
end

def weierstrass_equation.projective_point_smooth
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) :=
E.projective_point_on_curve X Y Z ∧ ¬ (E.eval_dX_at_projective_point X Y Z = 0
∧ E.eval_dY_at_projective_point X Y Z = 0 ∧ E.eval_dZ_at_projective_point X Y Z = 0)

lemma weierstrass_equation.projective_point_smooth.equal
{K : Type*} [field K] (E : weierstrass_equation K) {X Y Z X' Y' Z' : K}
(h : is_projective_point_equal X Y Z X' Y' Z') :
E.projective_point_smooth X Y Z ↔ E.projective_point_smooth X' Y' Z' :=
begin
  have hh := h,
  rcases hh with ⟨ a, ha, hX, hY, hZ ⟩,
  have keyX := calc E.eval_dX_at_projective_point X' Y' Z'
  = (E.eval_dX_at_projective_point X Y Z)*a^2 : by {
    rw [hX, hY, hZ],
    unfold weierstrass_equation.eval_dX_at_projective_point,
    ring,
  },
  have keyY := calc E.eval_dY_at_projective_point X' Y' Z'
  = (E.eval_dY_at_projective_point X Y Z)*a^2 : by {
    rw [hX, hY, hZ],
    unfold weierstrass_equation.eval_dY_at_projective_point,
    ring,
  },
  have keyZ := calc E.eval_dZ_at_projective_point X' Y' Z'
  = (E.eval_dZ_at_projective_point X Y Z)*a^2 : by {
    rw [hX, hY, hZ],
    unfold weierstrass_equation.eval_dZ_at_projective_point,
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

def weierstrass_equation.smooth
{K : Type*} [field K] (E : weierstrass_equation K) :=
∀ X Y Z : K, E.projective_point_on_curve X Y Z → E.projective_point_smooth X Y Z

lemma weierstrass_equation.affine_point_is_projective_point
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) :
E.affine_point_on_curve x y ↔ E.projective_point_on_curve x y 1 :=
begin
  have key := calc E.eval_at_projective_point x y 1 = E.eval_at_affine_point x y : by {
    unfold weierstrass_equation.eval_at_projective_point
    weierstrass_equation.eval_at_affine_point,
    ring,
  },
  unfold weierstrass_equation.affine_point_on_curve
  weierstrass_equation.projective_point_on_curve,
  rw key,
  have h : is_projective_point x y 1 := by {
    intro h, simp at h, exact h,
  },
  simp [h],
end

lemma weierstrass_equation.affine_point_smooth_iff_projective_point_smooth
{K : Type*} [field K] (E : weierstrass_equation K) (x y : K) :
E.affine_point_smooth x y ↔ E.projective_point_smooth x y 1 :=
begin
  have keyX := calc E.eval_dX_at_projective_point x y 1 = E.eval_dx_at_affine_point x y : by {
    unfold weierstrass_equation.eval_dX_at_projective_point
    weierstrass_equation.eval_dx_at_affine_point,
    ring,
  },
  have keyY := calc E.eval_dY_at_projective_point x y 1 = E.eval_dy_at_affine_point x y : by {
    unfold weierstrass_equation.eval_dY_at_projective_point
    weierstrass_equation.eval_dy_at_affine_point,
    ring,
  },
  have keyZ := calc E.eval_dZ_at_projective_point x y 1 =
  3 * E.eval_at_affine_point x y - x * E.eval_dx_at_affine_point x y - y * E.eval_dy_at_affine_point x y : by {
    unfold weierstrass_equation.eval_dZ_at_projective_point
    weierstrass_equation.eval_at_affine_point
    weierstrass_equation.eval_dx_at_affine_point
    weierstrass_equation.eval_dy_at_affine_point,
    ring,
  },
  unfold weierstrass_equation.affine_point_smooth
  weierstrass_equation.projective_point_smooth,
  rw [← E.affine_point_is_projective_point x y, keyX, keyY],
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
{K : Type*} [field K] (E : weierstrass_equation K) (X Y Z : K) :
E.projective_point_on_curve X Y Z ↔ is_projective_point_equal X Y Z 0 1 0
∨ (is_finite_projective_point X Y Z ∧ E.affine_point_on_curve (X/Z) (Y/Z)) :=
begin
  split, {
    rintros ⟨ h1, h2 ⟩,
    by_cases hZ : Z = 0, {
      left,
      unfold weierstrass_equation.eval_at_projective_point at h2,
      rw hZ at h2,
      ring at h2,
      field_simp at h2,
      replace h1 : Y ≠ 0 := by { intro h, exact h1 ⟨ h2, h, hZ ⟩, },
      use 1/Y,
      rw [hZ, h2],
      field_simp [h1],
    },
    right,
    use ⟨ h1, hZ ⟩,
    calc E.eval_at_affine_point (X/Z) (Y/Z)
    = (E.eval_at_projective_point X Y Z)/Z^3 : by {
      unfold weierstrass_equation.eval_at_projective_point
      weierstrass_equation.eval_at_affine_point,
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
    is_projective_point,
    simp, ring,
  },
  rw E.affine_point_is_projective_point at h2,
  have : is_projective_point_equal (X / Z) (Y / Z) 1 X Y Z := by {
    use Z,
    field_simp [h1.2, mul_comm],
  },
  rw weierstrass_equation.projective_point_on_curve.equal E this at h2,
  exact h2,
end

lemma weierstrass_equation.infinite_point_is_smooth
{K : Type*} [field K] (E : weierstrass_equation K) : E.projective_point_smooth 0 1 0 :=
begin
  unfold weierstrass_equation.projective_point_smooth
  weierstrass_equation.projective_point_on_curve
  is_projective_point
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

def weierstrass_equation.non_singular {K : Type*} [field K] (E : weierstrass_equation K) := E.disc ≠ 0

def weierstrass_equation.j {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.c4^3/E.disc

structure linear_change_of_variable (K : Type*) [field K] :=
mk :: (u r s t : K) (hu : u ≠ 0)

def linear_change_of_variable.change_curve {K : Type*} [field K]
(C : linear_change_of_variable K) (E : weierstrass_equation K) : weierstrass_equation K :=
weierstrass_equation.mk
((E.a1 + 2*C.s)/C.u)
((E.a2 - C.s*E.a1 + 3*C.r - C.s^2)/C.u^2)
((E.a3 + C.r*E.a1 + 2*C.t)/C.u^3)
((E.a4 - C.s*E.a3 + 2*C.r*E.a2 - (C.t+C.r*C.s)*E.a1 + 3*C.r^2 - 2*C.s*C.t)/C.u^4)
((E.a6 + C.r*E.a4 + C.r^2*E.a2 + C.r^3 - C.t*E.a3 - C.t^2 - C.r*C.t*E.a1)/C.u^6)

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

def linear_change_of_variable.change_affine_point_back {K : Type*} [field K]
(C : linear_change_of_variable K) (x y : K) : K × K :=
( C.u^2*x + C.r, C.u^3*y + C.u^2*C.s*x + C.t )

def linear_change_of_variable.change_projective_point_back {K : Type*} [field K]
(C : linear_change_of_variable K) (X Y Z : K) : K × K × K :=
( C.u^2*X + C.r*Z, C.u^3*Y + C.u^2*C.s*X + C.t*Z, Z )

def linear_change_of_variable.change_affine_point {K : Type*} [field K]
(C : linear_change_of_variable K) (x y : K) : K × K :=
( x/C.u^2 - C.r/C.u^2, y/C.u^3 - C.s*x/C.u^3 + (C.r*C.s-C.t)/C.u^3 )

lemma linear_change_of_variable.change_affine_point' {K : Type*} [field K]
(C : linear_change_of_variable K) (x y : K) :
(C.change_affine_point x y).1 = x/C.u^2 - C.r/C.u^2
∧ (C.change_affine_point x y).2 = y/C.u^3 - C.s*x/C.u^3 + (C.r*C.s-C.t)/C.u^3 :=
begin
  unfold linear_change_of_variable.change_affine_point,
  simp,
end

def linear_change_of_variable.change_projective_point {K : Type*} [field K]
(C : linear_change_of_variable K) (X Y Z : K) : K × K × K :=
( X/C.u^2 - Z*C.r/C.u^2, Y/C.u^3 - C.s*X/C.u^3 + Z*(C.r*C.s-C.t)/C.u^3, Z )

-- no denominator version
def linear_change_of_variable.change_projective_point' {K : Type*} [field K]
(C : linear_change_of_variable K) (X Y Z : K) : K × K × K :=
( X*C.u - Z*C.r*C.u, Y - C.s*X + Z*(C.r*C.s-C.t), Z*C.u^3 )

lemma linear_change_of_variable.change_affine_point_id {K : Type*} [field K]
(C : linear_change_of_variable K) (x y x' y' : K) :
C.change_affine_point_back x y = ( x', y' ) ↔ C.change_affine_point x' y' = ( x, y ) :=
begin
  split, {
    unfold linear_change_of_variable.change_affine_point_back
    linear_change_of_variable.change_affine_point,
    intro h1,
    rw prod.mk.inj_iff at h1 ⊢,
    cases h1 with h1 h2,
    rw [← h1, ← h2],
    field_simp [C.hu], ring,
    simp [mul_comm],
  }, {
    unfold linear_change_of_variable.change_affine_point_back
    linear_change_of_variable.change_affine_point,
    intro h1,
    rw prod.mk.inj_iff at h1 ⊢,
    cases h1 with h1 h2,
    rw [← h1, ← h2],
    field_simp [C.hu], ring,
    simp [mul_comm],
  },
end

lemma linear_change_of_variable.change_projective_point_id {K : Type*} [field K]
(C : linear_change_of_variable K) (X Y Z X' Y' Z' : K) :
C.change_projective_point_back X Y Z = ( X', Y', Z' ) ↔ C.change_projective_point X' Y' Z' = ( X, Y, Z ) :=
begin
  split, {
    unfold linear_change_of_variable.change_projective_point_back
    linear_change_of_variable.change_projective_point,
    intro h1,
    repeat {rw prod.mk.inj_iff at h1 ⊢},
    rcases h1 with ⟨ h1, h2, h3 ⟩,
    rw [← h1, ← h2, ← h3],
    field_simp [C.hu], ring,
    simp [mul_comm],
  }, {
    unfold linear_change_of_variable.change_projective_point_back
    linear_change_of_variable.change_projective_point,
    intro h1,
    repeat {rw prod.mk.inj_iff at h1 ⊢},
    rcases h1 with ⟨ h1, h2, h3 ⟩,
    rw [← h1, ← h2, ← h3],
    field_simp [C.hu], ring,
    simp [mul_comm],
  },
end

lemma weierstrass_equation.change_curve_preserve_affine_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (x y : K) :
E.affine_point_on_curve x y ↔ (C.change_curve E).affine_point_on_curve
(C.change_affine_point x y).1 (C.change_affine_point x y).2 :=
begin
  cases C.change_affine_point' x y with h1 h2,
  have key := calc (C.change_curve E).eval_at_affine_point (C.change_affine_point x y).1 (C.change_affine_point x y).2
  = (E.eval_at_affine_point x y)/C.u^6 : by {
    unfold weierstrass_equation.eval_at_affine_point
    linear_change_of_variable.change_curve
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [h1, h2],
    field_simp [pow_succ, C.hu],
    ring,
  },
  unfold weierstrass_equation.affine_point_on_curve,
  rw key,
  field_simp [C.hu],
end

lemma weierstrass_equation.change_curve_preserve_affine_smooth_point
{K : Type*} [field K] (E : weierstrass_equation K)
(C : linear_change_of_variable K) (x y : K) :
E.affine_point_smooth x y ↔ (C.change_curve E).affine_point_smooth
(C.change_affine_point x y).1 (C.change_affine_point x y).2 :=
begin
  cases C.change_affine_point' x y with h1 h2,
  have keyX := calc (C.change_curve E).eval_dx_at_affine_point (C.change_affine_point x y).1 (C.change_affine_point x y).2
  = (E.eval_dx_at_affine_point x y + C.s * E.eval_dy_at_affine_point x y)/C.u^4 : by {
    unfold weierstrass_equation.eval_dx_at_affine_point
    weierstrass_equation.eval_dy_at_affine_point
    linear_change_of_variable.change_curve
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [h1, h2],
    field_simp [pow_succ, C.hu],
    ring,
  },
  have keyY := calc (C.change_curve E).eval_dy_at_affine_point (C.change_affine_point x y).1 (C.change_affine_point x y).2
  = (E.eval_dy_at_affine_point x y)/C.u^3 : by {
    unfold weierstrass_equation.eval_dy_at_affine_point
    linear_change_of_variable.change_curve
    weierstrass_equation.a1
    weierstrass_equation.a2
    weierstrass_equation.a3
    weierstrass_equation.a4
    weierstrass_equation.a6,
    rw [h1, h2],
    field_simp [pow_succ, C.hu],
    ring,
  },
  unfold weierstrass_equation.affine_point_smooth,
  split, {
    intro h,
    use (E.change_curve_preserve_affine_point C x y).1 h.1,
    rintros ⟨ hh1, hh2 ⟩,
    rw keyX at hh1,
    rw keyY at hh2,
    field_simp [C.hu] at hh2,
    rw hh2 at hh1,
    field_simp [C.hu] at hh1,
    exact h.2 ⟨ hh1, hh2 ⟩,
  }, {
    intro h,
    use (E.change_curve_preserve_affine_point C x y).2 h.1,
    rintros ⟨ hh1, hh2 ⟩,
    rw [keyX, keyY, hh1, hh2] at h,
    field_simp [C.hu] at h,
    exact h,
  },
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

lemma weierstrass_equation.smooth_iff_affine_smooth
{K : Type*} [field K] (E : weierstrass_equation K) :
E.smooth ↔ E.affine_smooth :=
begin
  split, {
    intros h x y,
    rw [E.affine_point_is_projective_point, E.affine_point_smooth_iff_projective_point_smooth],
    exact h x y 1,
  },
  intros h X Y Z h1,
  rw E.projective_point_is_affine_point at h1,
  rcases h1 with h1 | ⟨ h1, h2 ⟩, {
    rw weierstrass_equation.projective_point_smooth.equal E h1,
    exact E.infinite_point_is_smooth,
  },
  replace h := h (X/Z) (Y/Z) h2,
  rw E.affine_point_smooth_iff_projective_point_smooth at h,
  have : is_projective_point_equal (X / Z) (Y / Z) 1 X Y Z := by {
    use Z,
    field_simp [h1.2, mul_comm],
  },
  rw weierstrass_equation.projective_point_smooth.equal E this at h,
  exact h,
end

lemma weierstrass_equation.smooth_iff_non_singular
{K : Type*} [field K] (E : weierstrass_equation K) :
E.smooth ↔ E.non_singular :=
begin
  rw E.smooth_iff_affine_smooth,
  split, {
    sorry,
  },
  intro h1,
  by_cases h : ∃ x y : K, E.affine_point_on_curve x y ∧ ¬ E.affine_point_smooth x y, {
    exfalso,
    rcases h with ⟨ x0, y0, h2, h3 ⟩,
    let C : linear_change_of_variable K := linear_change_of_variable.mk 1 x0 0 y0 (calc (1 : K) ≠ 0 : one_ne_zero),
    let E' : weierstrass_equation K := C.change_curve E,
    let P' := C.change_affine_point x0 y0,
    have hP' : P' = C.change_affine_point x0 y0 := rfl,
    unfold linear_change_of_variable.change_affine_point at hP',
    replace hP' := calc (P'.1, P'.2) = P' : rfl
    ... = (0, 0) : by { simp at hP', exact hP', },
    rw prod.mk.inj_iff at hP',
    have := E.change_curve_preserve_affine_point C x0 y0,
    sorry,
  },
  push_neg at h,
  exact h,
end

lemma exists_j0 : ∃ E : weierstrass_equation ℚ, E.non_singular ∧ E.j = 0 :=
begin
  use [0, 0, 0, 0, -1],
  split, {
    unfold weierstrass_equation.non_singular
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

lemma exists_j1728 : ∃ E : weierstrass_equation ℚ, E.non_singular ∧ E.j = 1728 :=
begin
  use [0, 0, 0, -1, 0],
  split, {
    unfold weierstrass_equation.non_singular
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

lemma exists_j (j : ℚ) : ∃ E : weierstrass_equation ℚ, E.non_singular ∧ E.j = j :=
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
