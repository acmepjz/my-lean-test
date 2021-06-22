import algebra.field
import gtm106.weierstrass_equation.linear_change_of_variable.basic
import gtm106.weierstrass_equation.linear_change_of_variable.change_curve
import gtm106.weierstrass_equation.linear_change_of_variable.change_point
import tactic

namespace linear_change_of_variable

def is_translation {K : Type*} [field K] (C : linear_change_of_variable K)
:= C.u = 1 ∧ C.s = 0

def is_scale {K : Type*} [field K] (C : linear_change_of_variable K)
:= C.r = 0 ∧ C.s = 0 ∧ C.t = 0

def is_shear {K : Type*} [field K] (C : linear_change_of_variable K)
:= C.u = 1 ∧ C.r = 0 ∧ C.t = 0

def mk_translation {K : Type*} [field K] (r t : K) : linear_change_of_variable K
:= ⟨ 1, r, 0, t, by simp ⟩

def mk_scale {K : Type*} [field K] (u : K) (hu : u ≠ 0) : linear_change_of_variable K
:= ⟨ u, 0, 0, 0, hu ⟩

def mk_shear {K : Type*} [field K] (s : K) : linear_change_of_variable K
:= ⟨ 1, 0, s, 0, by simp ⟩

@[simp]
lemma mk_translation.sound {K : Type*} [field K] (r t : K)
: is_translation (mk_translation r t) :=
begin
  simp [mk_translation, is_translation],
end

@[simp]
lemma mk_scale.sound {K : Type*} [field K] (u : K) (hu : u ≠ 0)
: is_scale (mk_scale u hu) :=
begin
  simp [mk_scale, is_scale],
end

@[simp]
lemma mk_shear.sound {K : Type*} [field K] (s : K)
: is_shear (mk_shear s) :=
begin
  simp [mk_shear, is_shear],
end

lemma decomposition' {K : Type*} [field K] (C : linear_change_of_variable K)
: C = ((mk_scale C.u C.hu).composite (mk_shear C.s)).composite (mk_translation C.r C.t) :=
begin
  simp [mk_scale, mk_shear, mk_translation, composite, ext_iff],
end

lemma decomposition {K : Type*} [field K] (C : linear_change_of_variable K)
: ∃ (C1 C2 C3 : linear_change_of_variable K),
is_scale C1 ∧ is_shear C2 ∧ is_translation C3 ∧ C = (C1.composite C2).composite C3 :=
begin
  use [mk_scale C.u C.hu, mk_shear C.s, mk_translation C.r C.t],
  rw ← decomposition' C,
  simp,
end

end linear_change_of_variable
