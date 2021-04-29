import algebra.field
import tactic

/--
Weierstrass equation `y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6`
-/
@[ext]
structure weierstrass_equation (K : Type*) [comm_ring K] :=
mk :: (a1 a2 a3 a4 a6 : K)

def weierstrass_equation.base_change {K : Type*} [comm_ring K]
(E : weierstrass_equation K) {L : Type*} [comm_ring L] (f : ring_hom K L)
: weierstrass_equation L := ⟨ f E.a1, f E.a2, f E.a3, f E.a4, f E.a6 ⟩

def weierstrass_equation.b2 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a1^2 + 4*E.a2

def weierstrass_equation.b4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
2*E.a4 + E.a1*E.a3

def weierstrass_equation.b6 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a3^2 + 4*E.a6

def weierstrass_equation.b8 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a1^2*E.a6 + 4*E.a2*E.a6 - E.a1*E.a3*E.a4 + E.a2*E.a3^2 - E.a4^2

def weierstrass_equation.c4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.b2^2 - 24*E.b4

def weierstrass_equation.c6 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
-E.b2^3 + 36*E.b2*E.b4 - 216*E.b6

def weierstrass_equation.disc {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
-E.b2^2*E.b8 - 8*E.b4^3 - 27*E.b6^2 + 9*E.b2*E.b4*E.b6

lemma weierstrass_equation.b8_mul_4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) :
4*E.b8 = E.b2*E.b6 - E.b4^2 :=
begin
  simp [weierstrass_equation.b8, weierstrass_equation.b6,
    weierstrass_equation.b4, weierstrass_equation.b2],
  ring,
end

lemma weierstrass_equation.disc_mul_1728 {K : Type*} [comm_ring K] (E : weierstrass_equation K) :
1728*E.disc = E.c4^3 - E.c6^2 :=
begin
  simp [weierstrass_equation.disc,
    weierstrass_equation.c4, weierstrass_equation.c6,
    weierstrass_equation.b8, weierstrass_equation.b6,
    weierstrass_equation.b4, weierstrass_equation.b2],
  ring,
end

def weierstrass_equation.non_singular' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc ≠ 0

def weierstrass_equation.has_node' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 ≠ 0

def weierstrass_equation.has_cusp' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 = 0

def weierstrass_equation.j {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.c4^3/E.disc
