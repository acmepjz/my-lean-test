import algebra.field
import data.polynomial
import data.mv_polynomial
import gtm106.weierstrass_equation.basic
import gtm106.weierstrass_equation.point
import tactic

namespace weierstrass_equation

namespace regular_function_ring

noncomputable def x0 {K : Type*} [comm_ring K]
: mv_polynomial (fin 2) K
:= @mv_polynomial.X K (fin 2) _ ⟨ 0, by norm_num ⟩

noncomputable def y0 {K : Type*} [comm_ring K]
: mv_polynomial (fin 2) K
:= @mv_polynomial.X K (fin 2) _ ⟨ 1, by norm_num ⟩

noncomputable def f0 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) : mv_polynomial (fin 2) K
:= y0^2 + (mv_polynomial.C E.a1)*x0*y0 + (mv_polynomial.C E.a3)*y0 - x0^3
  - (mv_polynomial.C E.a2)*x0^2 - (mv_polynomial.C E.a4)*x0 - (mv_polynomial.C E.a6)

noncomputable def I0 {K : Type*} [comm_ring K]
(E : weierstrass_equation K) : ideal (mv_polynomial (fin 2) K)
:= ideal.span {f0 E}

end regular_function_ring

/--
The regular function ring of affine part,
which is `K[x,y]/(y^2 + a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6)`
-/
@[reducible]
def regular_function_ring {K : Type*} [comm_ring K]
(E : weierstrass_equation K) :=
(regular_function_ring.I0 E).quotient

example {K : Type*} [comm_ring K]
(E : weierstrass_equation K) (x y : regular_function_ring E)
: regular_function_ring E :=
begin
  exact x + y,
end

/--
The regular function ring of affine part,
viewed as `K[x]⬝{1,y}` which is a free `K[x]`-module of rank 2
-/
@[reducible]
def regular_function_ring' {K : Type*} [comm_ring K]
(E : weierstrass_equation K)
:= (fin 2) → polynomial K

end weierstrass_equation
