import algebra.field
import data.polynomial
import data.mv_polynomial
import gtm106.weierstrass_equation.regular_function.basic
import gtm106.weierstrass_equation.regular_function.mv_polynomial
import tactic

noncomputable theory

namespace weierstrass_equation

namespace regular_function_ring'

def to_regular_function_ring.to_fun {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f : regular_function_ring' E) : regular_function_ring E
:= (polynomial.eval₂ (@regular_function_ring.C K _ E) regular_function_ring.x f.1)
+ (polynomial.eval₂ (@regular_function_ring.C K _ E) regular_function_ring.x f.2) * regular_function_ring.y

lemma to_regular_function_ring.map_one' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @to_regular_function_ring.to_fun K _ E one = 1 :=
begin
  simp [to_regular_function_ring.to_fun, one],
end

lemma to_regular_function_ring.map_mul' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} (f g : regular_function_ring' E)
: (@to_regular_function_ring.to_fun K _ E (mul f g)) = (@to_regular_function_ring.to_fun K _ E f) * (@to_regular_function_ring.to_fun K _ E g) :=
begin
  have h : (@regular_function_ring.x K _ E) ^ 3 + regular_function_ring.C E.a2 * regular_function_ring.x ^ 2 + regular_function_ring.C E.a4 * regular_function_ring.x + regular_function_ring.C E.a6 = 0 := by {
    sorry,
  },
  -- simp [to_regular_function_ring.to_fun, mul],
  sorry,
end

lemma to_regular_function_ring.map_zero' {K : Type*} [comm_ring K]
{E : weierstrass_equation K} : @to_regular_function_ring.to_fun K _ E zero = 0 :=
begin
  simp [to_regular_function_ring.to_fun, zero],
end

lemma to_regular_function_ring.map_add' {K : Type*} [comm_ring K]
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
