import algebra.field
import algebra.algebra.basic
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
{K : Type*} [field K] (E : weierstrass_equation K)
{R : Type*} [comm_ring R] [algebra K R] (x y : R) : R :=
let ι := algebra_map K R in
y^2 + ι(E.a1)*x*y + ι(E.a3)*y - x^3 - ι(E.a2)*x^2 - ι(E.a4)*x - ι(E.a6)

def weierstrass_equation.affine_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K)
{R : Type*} [comm_ring R] [algebra K R] (x y : R) :=
E.eval_at_affine_point x y = 0

def is_projective_point {R : Type*} [comm_ring R] (X Y Z : R) :=
¬ (X = 0 ∧ Y = 0 ∧ Z = 0)

def is_projective_point_finite {R : Type*} [comm_ring R] (X Y Z : R) :=
¬ (X = 0 ∧ Y = 0 ∧ Z = 0) ∧ Z ≠ 0

def is_projective_point_infinite {R : Type*} [comm_ring R] (X Y Z : R) :=
¬ (X = 0 ∧ Y = 0 ∧ Z = 0) ∧ Z = 0

def weierstrass_equation.eval_at_projective_point
{K : Type*} [field K] (E : weierstrass_equation K)
{R : Type*} [comm_ring R] [algebra K R] (X Y Z : R) : R :=
let ι := algebra_map K R in
Y^2*Z + ι(E.a1)*X*Y*Z + ι(E.a3)*Y*Z^2 - X^3 - ι(E.a2)*X^2*Y - ι(E.a4)*X*Y^2 - ι(E.a6)*Z^3

def weierstrass_equation.projective_point_on_curve
{K : Type*} [field K] (E : weierstrass_equation K)
{R : Type*} [comm_ring R] [algebra K R] (X Y Z : R) :=
¬ (X = 0 ∧ Y = 0 ∧ Z = 0) ∧ E.eval_at_projective_point X Y Z = 0

lemma weierstrass_equation.affine_point_is_projective_point
{K : Type*} [field K] (E : weierstrass_equation K)
{R : Type*} [comm_ring R] [algebra K R] (x y : R)
(h : E.affine_point_on_curve x y) : E.projective_point_on_curve x y 1 :=
begin
  split,
  sorry,
  sorry,
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
