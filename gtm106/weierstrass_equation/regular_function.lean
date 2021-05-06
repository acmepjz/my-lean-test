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

/--
The regular function ring of affine part,
we define it as the free `K[x]`-module of rank 2 `K[x]⬝{1,y}`.
-/
@[ext]
structure regular_function_ring' {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
mk :: (C1 Cy : polynomial K)

namespace regular_function_ring'

def zero {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : regular_function_ring' E
:= ⟨ 0, 0 ⟩

def one {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : regular_function_ring' E
:= ⟨ 1, 0 ⟩

def x {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : regular_function_ring' E
:= ⟨ polynomial.X, 0 ⟩

def y {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : regular_function_ring' E
:= ⟨ 0, 1 ⟩

def add {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E) : regular_function_ring' E
:= ⟨ f.1 + g.1, f.2 + g.2 ⟩

def neg {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E) : regular_function_ring' E
:= ⟨ -(f.1), -(f.2) ⟩

def sub {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E) : regular_function_ring' E
:= ⟨ f.1 - g.1, f.2 - g.2 ⟩

-- since y^2 = -a1*x*y - a3*y + x^3 + a2*x^2 + a4*x + a6
-- therefore (f1 + f2*y)*(g1 + g2*y)
-- = f1*g1 + (f1*g2 + f2*g1)*y + f2*g2*y^2
-- = (f1*g1 + f2*g2*(x^3 + a2*x^2 + a4*x + a6)) + (f1*g2 + f2*g1 - f2*g2*(a1*x + a3))*y
def mul {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E) : regular_function_ring' E
:= ⟨ f.1*g.1 + f.2*g.2*(polynomial.monomial 3 1 + polynomial.monomial 2 E.a2 + polynomial.monomial 1 E.a4 + polynomial.C E.a6),
  f.1*g.2 + f.2*g.1 - f.2*g.2*(polynomial.monomial 1 E.a1 + polynomial.C E.a3) ⟩

lemma add.add_assoc {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g h : regular_function_ring' E)
: add (add f g) h = add f (add g h) :=
begin
  simp [add, add_assoc],
end

lemma add.zero_add {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E)
: add zero f = f :=
begin
  simp [add, zero, ext_iff],
end

lemma add.add_zero {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E)
: add f zero = f :=
begin
  simp [add, zero, ext_iff],
end

lemma add.add_left_neg {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E)
: add (neg f) f = zero :=
begin
  simp [add, neg, zero, ext_iff],
end

lemma add.add_right_neg {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E)
: add f (neg f) = zero :=
begin
  simp [add, neg, zero, ext_iff],
end

lemma add.add_comm {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E)
: add f g = add g f :=
begin
  simp [add, add_comm],
end

lemma mul.mul_assoc {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g h : regular_function_ring' E)
: mul (mul f g) h = mul f (mul g h) :=
begin
  simp [mul],
  split, { ring, },
  ring,
end

lemma mul.one_mul {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E)
: mul one f = f :=
begin
  simp [mul, one, ext_iff],
end

lemma mul.mul_one {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E)
: mul f one = f :=
begin
  simp [mul, one, ext_iff],
end

lemma mul.left_distrib {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g h : regular_function_ring' E)
: mul f (add g h) = add (mul f g) (mul f h) :=
begin
  simp [mul, add],
  split, { ring, },
  ring,
end

lemma mul.right_distrib {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g h : regular_function_ring' E)
: mul (add f g) h = add (mul f h) (mul g h) :=
begin
  simp [mul, add],
  split, { ring, },
  ring,
end

lemma mul.mul_comm {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E)
: mul f g = mul g f :=
begin
  simp [mul],
  split, { ring, },
  ring,
end

instance to_comm_ring {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : comm_ring (regular_function_ring' E)
:= ⟨ @add K _ E, add.add_assoc, zero, add.zero_add, add.add_zero, neg,
  sub, (λ f g, by {
    simp only [has_add.add, add_zero_class.add],
    simp [add, sub, neg, sub_eq_add_neg],
  }), add.add_left_neg, add.add_comm, mul, mul.mul_assoc, one,
  mul.one_mul, mul.mul_one, mul.left_distrib, mul.right_distrib, mul.mul_comm ⟩

def C.to_fun {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a : K) : regular_function_ring' E
:= ⟨ polynomial.C a, 0 ⟩

def C.map_one' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @C.to_fun K _ E 1 = one :=
begin
  simp [C.to_fun, one],
end

def C.map_mul' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a b : K)
: (@C.to_fun K _ E (a*b)) = mul (@C.to_fun K _ E a) (@C.to_fun K _ E b) :=
begin
  simp [C.to_fun, mul],
end

def C.map_zero' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @C.to_fun K _ E 0 = zero :=
begin
  simp [C.to_fun, zero],
end

def C.map_add' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a b : K)
: (@C.to_fun K _ E (a+b)) = add (@C.to_fun K _ E a) (@C.to_fun K _ E b) :=
begin
  simp [C.to_fun, add],
end

def C {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : ring_hom K (regular_function_ring' E)
:= ⟨ C.to_fun, C.map_one', C.map_mul', C.map_zero', C.map_add' ⟩

def to_regular_function_ring.to_fun {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E) : regular_function_ring E
:= (polynomial.eval₂ (@regular_function_ring.C K _ E) regular_function_ring.x f.1)
+ (polynomial.eval₂ (@regular_function_ring.C K _ E) regular_function_ring.x f.2) * regular_function_ring.y

def to_regular_function_ring.map_one' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @to_regular_function_ring.to_fun K _ E one = 1 :=
begin
  simp [to_regular_function_ring.to_fun, one],
end

def to_regular_function_ring.map_mul' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E)
: (@to_regular_function_ring.to_fun K _ E (mul f g)) = (@to_regular_function_ring.to_fun K _ E f) * (@to_regular_function_ring.to_fun K _ E g) :=
begin
  unfold mul to_regular_function_ring.to_fun,
  dsimp only,
  sorry,
end

def to_regular_function_ring.map_zero' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @to_regular_function_ring.to_fun K _ E zero = 0 :=
begin
  simp [to_regular_function_ring.to_fun, zero],
end

def to_regular_function_ring.map_add' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E)
: (@to_regular_function_ring.to_fun K _ E (add f g)) = (@to_regular_function_ring.to_fun K _ E f) + (@to_regular_function_ring.to_fun K _ E g) :=
begin
  unfold add to_regular_function_ring.to_fun,
  dsimp only,
  repeat { rw polynomial.eval₂_add },
  ring,
end

def to_regular_function_ring {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : ring_hom (regular_function_ring' E) (regular_function_ring E)
:= ⟨ to_regular_function_ring.to_fun, to_regular_function_ring.map_one', to_regular_function_ring.map_mul', to_regular_function_ring.map_zero', to_regular_function_ring.map_add' ⟩

end regular_function_ring'

end weierstrass_equation
