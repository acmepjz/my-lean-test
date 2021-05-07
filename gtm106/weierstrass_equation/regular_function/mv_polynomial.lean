import algebra.field
import data.polynomial
import data.mv_polynomial
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import tactic

noncomputable theory

namespace weierstrass_equation

namespace regular_function_ring

/--
The `x` in `K[x,y]`
-/
def x0 {K : Type*} [comm_ring K]
: mv_polynomial (fin 2) K
:= @mv_polynomial.X K (fin 2) _ ⟨ 0, by norm_num ⟩

/--
The `y` in `K[x,y]`
-/
def y0 {K : Type*} [comm_ring K]
: mv_polynomial (fin 2) K
:= @mv_polynomial.X K (fin 2) _ ⟨ 1, by norm_num ⟩

/--
The `y^2 + a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6` in `K[x,y]`
-/
def f0 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) : mv_polynomial (fin 2) K
:= y0^2 + (mv_polynomial.C E.a1)*x0*y0 + (mv_polynomial.C E.a3)*y0 - x0^3
  - (mv_polynomial.C E.a2)*x0^2 - (mv_polynomial.C E.a4)*x0 - (mv_polynomial.C E.a6)

def I0.gen {K : Type*} [comm_ring K]
(E : weierstrass_equation K) : set (mv_polynomial (fin 2) K)
:= {f0 E}

/--
The principal idean `(y^2 + a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6)` in `K[x,y]`
-/
def I0 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) : ideal (mv_polynomial (fin 2) K)
:= ideal.span (I0.gen E)

end regular_function_ring

/--
The regular function ring of affine part,
which is `K[x,y]/(y^2 + a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6)`
-/
@[reducible]
def regular_function_ring {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
(regular_function_ring.I0 E).quotient

namespace regular_function_ring

def quotient_map {K : Type*} [comm_ring K]
(E : weierstrass_equation K) : ring_hom (mv_polynomial (fin 2) K) (regular_function_ring E)
:= ideal.quotient.mk (I0 E)

def C {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : ring_hom K (regular_function_ring E)
:= (quotient_map E).comp (@mv_polynomial.C K (fin 2) _)

/--
The `x` in regular function ring
-/
def x {K : Type*} [comm_ring K]
{E : weierstrass_equation K}
: E.regular_function_ring
:= (quotient_map E) x0

/--
The `y` in regular function ring
-/
def y {K : Type*} [comm_ring K]
{E : weierstrass_equation K}
: E.regular_function_ring
:= (quotient_map E) y0

lemma ker {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
: (y : E.regular_function_ring) ^ 2 + C E.a1 * x * y + C E.a3 * y - x ^ 3 - C E.a2 * x ^ 2 - C E.a4 * x - C E.a6 = 0 :=
begin
  simp [x, y, x0, y0, C, quotient_map],
  repeat { rw ← ring_hom.map_mul <|>
    rw ← ring_hom.map_pow <|>
    rw ← ring_hom.map_add <|>
    rw ← ring_hom.map_sub },
  rw ideal.quotient.eq_zero_iff_mem,
  have : f0 E = mv_polynomial.X 1 ^ 2 
    + mv_polynomial.C E.a1 * mv_polynomial.X 0 * mv_polynomial.X 1
    + mv_polynomial.C E.a3 * mv_polynomial.X 1
    - mv_polynomial.X 0 ^ 3
    - mv_polynomial.C E.a2 * mv_polynomial.X 0 ^ 2
    - mv_polynomial.C E.a4 * mv_polynomial.X 0
    - mv_polynomial.C E.a6 := rfl,
  rw ← this,
  simp [I0, I0.gen, ideal.mem_span_singleton],
end

def eval_at_affine_point_0 {K : Type*} [comm_ring K]
(P : affine_plane_point K) : ring_hom (mv_polynomial (fin 2) K) K
:= @mv_polynomial.eval K (fin 2) _ (λ i, if i = 0 then P.x else P.y)

@[simp]
lemma eval_at_affine_point_0.C {K : Type*} [comm_ring K]
(P : affine_plane_point K) (a : K) : (eval_at_affine_point_0 P) (mv_polynomial.C a) = a :=
begin
  simp [eval_at_affine_point_0],
end

@[simp]
lemma eval_at_affine_point_0.x0 {K : Type*} [comm_ring K]
(P : affine_plane_point K) : (eval_at_affine_point_0 P) x0 = P.x :=
begin
  simp [eval_at_affine_point_0, x0],
end

@[simp]
lemma eval_at_affine_point_0.y0 {K : Type*} [comm_ring K]
(P : affine_plane_point K) : (eval_at_affine_point_0 P) y0 = P.y :=
begin
  simp [eval_at_affine_point_0, y0],
end

lemma eval_at_affine_point_0.lift {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
(P : affine_plane_point K) (h1 : E.affine_point_on_curve P)
(f : mv_polynomial (fin 2) K) (h2 : f ∈ I0 E)
: eval_at_affine_point_0 P f = 0 :=
begin
  simp [affine_point_on_curve, eval_at_affine_point] at h1,
  simp [I0, ideal.span] at h2,
  refine submodule.span_induction h2 _ _ _ _,
  {
    intros f h,
    simp [I0.gen, f0] at h,
    simp [h, h1],
  },
  {
    simp [eval_at_affine_point_0],
  },
  {
    simp [eval_at_affine_point_0],
    intros f g h1 h2,
    rw [h1, h2, add_zero],
  },
  simp [eval_at_affine_point_0],
  intros f g h,
  rw [h, mul_zero],
end

def eval_at_affine_point {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
: ring_hom E.regular_function_ring K
:= ideal.quotient.lift (I0 E) (eval_at_affine_point_0 P)
(eval_at_affine_point_0.lift E P h)

@[simp]
lemma eval_at_affine_point.C {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
(a : K) : (eval_at_affine_point E P h) (C a) = a :=
begin
  simp [eval_at_affine_point, C, quotient_map],
end

@[simp]
lemma eval_at_affine_point.x {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
: (eval_at_affine_point E P h) x = P.x :=
begin
  simp [eval_at_affine_point, x, quotient_map],
end

@[simp]
lemma eval_at_affine_point.y {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
(P : affine_plane_point K) (h : E.affine_point_on_curve P)
: (eval_at_affine_point E P h) y = P.y :=
begin
  simp [eval_at_affine_point, y, quotient_map],
end

end regular_function_ring

end weierstrass_equation
