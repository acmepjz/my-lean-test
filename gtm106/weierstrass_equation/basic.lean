import algebra.field
import tactic

/--
Weierstrass equation `y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6`
-/
@[ext]
structure weierstrass_equation (K : Type*) [comm_ring K] :=
mk :: (a1 a2 a3 a4 a6 : K)

namespace weierstrass_equation

def base_change {K : Type*} [comm_ring K]
(E : weierstrass_equation K) {L : Type*} [comm_ring L] (f : ring_hom K L)
: weierstrass_equation L := ⟨ f E.a1, f E.a2, f E.a3, f E.a4, f E.a6 ⟩

def b2 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a1^2 + 4*E.a2

def b4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
2*E.a4 + E.a1*E.a3

def b6 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a3^2 + 4*E.a6

def b8 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a1^2*E.a6 + 4*E.a2*E.a6 - E.a1*E.a3*E.a4 + E.a2*E.a3^2 - E.a4^2

def c4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.b2^2 - 24*E.b4

def c6 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
-E.b2^3 + 36*E.b2*E.b4 - 216*E.b6

def disc {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
-E.b2^2*E.b8 - 8*E.b4^3 - 27*E.b6^2 + 9*E.b2*E.b4*E.b6

lemma b8_mul_4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) :
4*E.b8 = E.b2*E.b6 - E.b4^2 :=
begin
  simp [b8, b6, b4, b2],
  ring,
end

lemma disc_mul_1728 {K : Type*} [comm_ring K] (E : weierstrass_equation K) :
1728*E.disc = E.c4^3 - E.c6^2 :=
begin
  simp [disc, c4, c6, b8, b6, b4, b2],
  ring,
end

def non_singular' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc ≠ 0

def has_node' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 ≠ 0

def has_cusp' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 = 0

def j {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.c4^3/E.disc

end weierstrass_equation
