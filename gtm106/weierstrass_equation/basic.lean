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

@[simp]
lemma b2.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).b2 = f E.b2 :=
begin
  simp [base_change, b2],
end

def b4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
2*E.a4 + E.a1*E.a3

@[simp]
lemma b4.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).b4 = f E.b4 :=
begin
  simp [base_change, b4],
end

def b6 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a3^2 + 4*E.a6

@[simp]
lemma b6.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).b6 = f E.b6 :=
begin
  simp [base_change, b6],
end

def b8 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.a1^2*E.a6 + 4*E.a2*E.a6 - E.a1*E.a3*E.a4 + E.a2*E.a3^2 - E.a4^2

@[simp]
lemma b8.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).b8 = f E.b8 :=
begin
  simp [base_change, b8],
end

def c4 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
E.b2^2 - 24*E.b4

@[simp]
lemma c4.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).c4 = f E.c4 :=
begin
  simp [c4],
end

def c6 {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
-E.b2^3 + 36*E.b2*E.b4 - 216*E.b6

@[simp]
lemma c6.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).c6 = f E.c6 :=
begin
  simp [c6],
end

def disc {K : Type*} [comm_ring K] (E : weierstrass_equation K) : K :=
-E.b2^2*E.b8 - 8*E.b4^3 - 27*E.b6^2 + 9*E.b2*E.b4*E.b6

@[simp]
lemma disc.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
: (E.base_change f).disc = f E.disc :=
begin
  simp [disc],
end

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

lemma non_singular'.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
(h : (E.base_change f).non_singular') : E.non_singular' :=
begin
  intro h0,
  simp [non_singular', h0] at h,
  exact h,
end

@[simp]
lemma non_singular'.base_change_field
{K : Type*} [field K] (E : weierstrass_equation K)
{L : Type*} [field L] (f : ring_hom K L)
: (E.base_change f).non_singular' ↔ E.non_singular' :=
begin
  simp [non_singular'],
end

def has_node' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 ≠ 0

@[simp]
lemma has_node'.base_change_field
{K : Type*} [field K] (E : weierstrass_equation K)
{L : Type*} [field L] (f : ring_hom K L)
: (E.base_change f).has_node' ↔ E.has_node' :=
begin
  simp [has_node'],
end

def has_cusp' {K : Type*} [comm_ring K] (E : weierstrass_equation K) :=
E.disc = 0 ∧ E.c4 = 0

lemma has_cusp'.base_change
{K : Type*} [comm_ring K] (E : weierstrass_equation K)
{L : Type*} [comm_ring L] (f : ring_hom K L)
(h : E.has_cusp') : (E.base_change f).has_cusp' :=
begin
  simp [has_cusp'] at h,
  simp [has_cusp', h.1, h.2],
end

@[simp]
lemma has_cusp'.base_change_field
{K : Type*} [field K] (E : weierstrass_equation K)
{L : Type*} [field L] (f : ring_hom K L)
: (E.base_change f).has_cusp' ↔ E.has_cusp' :=
begin
  simp [has_cusp'],
end

def j {K : Type*} [field K] (E : weierstrass_equation K) : K :=
E.c4^3/E.disc

@[simp]
lemma j.base_change
{K : Type*} [field K] (E : weierstrass_equation K)
{L : Type*} [field L] (f : ring_hom K L)
: (E.base_change f).j = f E.j :=
begin
  simp [j],
  by_cases h : E.disc = 0, {
    simp [h],
  },
  have h1 : f E.disc ≠ 0 := by simp [h],
  field_simp [h1],
  have h2 : (f.to_fun E.c4)^3 = (f.to_fun E.c4)*(f.to_fun E.c4)*(f.to_fun E.c4) := by ring,
  unfold coe_fn has_coe_to_fun.coe,
  rw h2,
  repeat { rw ← f.map_mul' },
  congr' 1,
  simp [h, pow_succ, mul_assoc],
end

end weierstrass_equation
