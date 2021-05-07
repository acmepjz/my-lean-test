import algebra.field
import data.polynomial
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import tactic

noncomputable theory

namespace weierstrass_equation

/--
The regular function ring of affine part,
which is `K[x,y]/(y^2 + a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6)`,
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

def smul {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a : K) (f : regular_function_ring' E) : regular_function_ring' E
:= ⟨ polynomial.C a * f.1, polynomial.C a * f.2 ⟩

def smul_poly {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a : polynomial K) (f : regular_function_ring' E) : regular_function_ring' E
:= ⟨ a * f.1, a * f.2 ⟩

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

lemma C.map_one' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @C.to_fun K _ E 1 = one :=
begin
  simp [C.to_fun, one],
end

lemma C.map_mul' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a b : K)
: (@C.to_fun K _ E (a*b)) = mul (@C.to_fun K _ E a) (@C.to_fun K _ E b) :=
begin
  simp [C.to_fun, mul],
end

lemma C.map_zero' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @C.to_fun K _ E 0 = zero :=
begin
  simp [C.to_fun, zero],
end

lemma C.map_add' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a b : K)
: (@C.to_fun K _ E (a+b)) = add (@C.to_fun K _ E a) (@C.to_fun K _ E b) :=
begin
  simp [C.to_fun, add],
end

def C {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : ring_hom K (regular_function_ring' E)
:= ⟨ C.to_fun, C.map_one', C.map_mul', C.map_zero', C.map_add' ⟩

lemma ker {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
: (y : E.regular_function_ring') ^ 2 + C E.a1 * x * y + C E.a3 * y - x ^ 3 - C E.a2 * x ^ 2 - C E.a4 * x - C E.a6 = 0 :=
begin
  simp only [has_add.add, distrib.add, ring.add, comm_ring.add,
    has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, comm_ring.sub,
    has_mul.mul, distrib.mul, ring.mul, comm_ring.mul,
    pow, monoid.pow, mul_one_class.mul, monoid.mul,
    has_zero.zero, mul_zero_class.zero, monoid_with_zero.zero, semiring.zero, ring.zero, comm_ring.zero,
    has_one.one, mul_one_class.one, monoid.one, ring.one, comm_ring.one,
    mul.mul_one],
  simp [C, C.to_fun, x, y, add, sub, mul, zero, polynomial.X, polynomial.monomial_mul_monomial],
  ring,
end

def eval_at_affine_point.to_fun {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K) (f : regular_function_ring' E) : K
:= (polynomial.eval P.x f.1) + (polynomial.eval P.x f.2) * P.y

lemma eval_at_affine_point.map_one' {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K)
: eval_at_affine_point.to_fun E P one = 1 :=
begin
  simp [eval_at_affine_point.to_fun, one],
end

lemma eval_at_affine_point.map_mul' {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K) (h : E.affine_point_on_curve P)
(f g : regular_function_ring' E)
: eval_at_affine_point.to_fun E P (mul f g) = eval_at_affine_point.to_fun E P f * eval_at_affine_point.to_fun E P g :=
begin
  simp [eval_at_affine_point.to_fun, mul],
  simp [affine_point_on_curve, eval_at_affine_point] at h,
  transitivity polynomial.eval P.x f.C1 * polynomial.eval P.x g.C1
    + polynomial.eval P.x f.Cy * polynomial.eval P.x g.Cy *
      (P.y ^ 2 - (P.y ^ 2 + E.a1 * P.x * P.y + E.a3 * P.y - P.x ^ 3 - E.a2 * P.x ^ 2 - E.a4 * P.x - E.a6))
    + (polynomial.eval P.x f.C1 * polynomial.eval P.x g.Cy + polynomial.eval P.x f.Cy * polynomial.eval P.x g.C1) * P.y,
  { rw ← sub_eq_zero, ring, },
  rw [h, ← sub_eq_zero], ring,
end

lemma eval_at_affine_point.map_zero' {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K)
: eval_at_affine_point.to_fun E P zero = 0 :=
begin
  simp [eval_at_affine_point.to_fun, zero],
end

lemma eval_at_affine_point.map_add' {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K)
(f g : regular_function_ring' E)
: eval_at_affine_point.to_fun E P (add f g) = eval_at_affine_point.to_fun E P f + eval_at_affine_point.to_fun E P g :=
begin
  simp [eval_at_affine_point.to_fun, add],
  ring,
end

def eval_at_affine_point {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K) (h : E.affine_point_on_curve P)
: ring_hom (regular_function_ring' E) K
:= ⟨ eval_at_affine_point.to_fun E P,
  eval_at_affine_point.map_one' E P,
  eval_at_affine_point.map_mul' E P h,
  eval_at_affine_point.map_zero' E P,
  eval_at_affine_point.map_add' E P ⟩

@[simp]
lemma eval_at_affine_point.C {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K) (h : E.affine_point_on_curve P)
(a : K) : (eval_at_affine_point E P h) (C a) = a :=
begin
  simp [eval_at_affine_point, eval_at_affine_point.to_fun, C, C.to_fun],
end

@[simp]
lemma eval_at_affine_point.x {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K) (h : E.affine_point_on_curve P)
: (eval_at_affine_point E P h) x = P.x :=
begin
  simp [eval_at_affine_point, eval_at_affine_point.to_fun, x],
end

@[simp]
lemma eval_at_affine_point.y {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (P : affine_plane_point K) (h : E.affine_point_on_curve P)
: (eval_at_affine_point E P h) y = P.y :=
begin
  simp [eval_at_affine_point, eval_at_affine_point.to_fun, y],
end

def C_poly.to_fun {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a : polynomial K) : regular_function_ring' E
:= ⟨ a, 0 ⟩

lemma C_poly.map_one' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @C_poly.to_fun K _ E 1 = one :=
begin
  simp [C_poly.to_fun, one],
end

lemma C_poly.map_mul' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a b : polynomial K)
: (@C_poly.to_fun K _ E (a*b)) = mul (@C_poly.to_fun K _ E a) (@C_poly.to_fun K _ E b) :=
begin
  simp [C_poly.to_fun, mul],
end

lemma C_poly.map_zero' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @C_poly.to_fun K _ E 0 = zero :=
begin
  simp [C_poly.to_fun, zero],
end

lemma C_poly.map_add' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (a b : polynomial K)
: (@C_poly.to_fun K _ E (a+b)) = add (@C_poly.to_fun K _ E a) (@C_poly.to_fun K _ E b) :=
begin
  simp [C_poly.to_fun, add],
end

def C_poly {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : ring_hom (polynomial K) (regular_function_ring' E)
:= ⟨ C_poly.to_fun, C_poly.map_one', C_poly.map_mul', C_poly.map_zero', C_poly.map_add' ⟩

instance to_poly_algebra {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : algebra (polynomial K) (regular_function_ring' E)
:= { to_has_scalar := ⟨ smul_poly ⟩,
  to_ring_hom := C_poly,
  commutes' := (λ f g, by {
    rw mul_comm,
  }),
  smul_def' := (λ f g, by {
    simp only [has_mul.mul, distrib.mul, semiring.mul, ring.mul, comm_ring.mul],
    simp only [smul_poly, C_poly, C_poly.to_fun],
    simp [mul],
  }),
}

instance to_algebra {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : algebra K (regular_function_ring' E)
:= { to_has_scalar := ⟨ smul ⟩,
  to_ring_hom := C,
  commutes' := (λ f g, by {
    rw mul_comm,
  }),
  smul_def' := (λ f g, by {
    simp only [has_mul.mul, distrib.mul, semiring.mul, ring.mul, comm_ring.mul],
    simp only [smul, C, C.to_fun],
    simp [mul],
  }),
}

lemma no_zero_divisor {K : Type*} [field K]
{E : weierstrass_equation K} (hns : E.non_singular') (f g : regular_function_ring' E)
: f * g = 0 → f = 0 ∨ g = 0 :=
begin
  simp only [has_mul.mul, distrib.mul, ring.mul, comm_ring.mul,
    has_zero.zero, mul_zero_class.zero, monoid_with_zero.zero, semiring.zero, ring.zero, comm_ring.zero],
  simp [mul, zero, ext_iff],
  intros h1 h2,
  sorry,
end

/-
instance to_integral_domain {K : Type*} [field K]
{E : weierstrass_equation K} (h : E.non_singular') : integral_domain (regular_function_ring' E)
:= {
  exists_pair_ne := by {
    use [zero, one],
    simp [zero, one],
  },
  eq_zero_or_eq_zero_of_mul_eq_zero := no_zero_divisor h,
  .. (infer_instance : comm_ring (regular_function_ring' E))
}
-/

end regular_function_ring'

end weierstrass_equation
