import algebra.field
import tactic

/--
Linear change of variable defined in GTM106,
also viewed as a matrix
```
u^2   0   r
u^2*s u^3 t
0     0   1
```
-/
@[ext]
structure linear_change_of_variable (K : Type*) [field K] :=
mk :: (u r s t : K) (hu : u ≠ 0)

namespace linear_change_of_variable

@[simp]
lemma u_non_zero {K : Type*} [field K]
(C : linear_change_of_variable K) : C.u ≠ 0 := C.hu

-- ================
-- Linear change of variables form a group
-- ================

def identity (K : Type*) [field K] : linear_change_of_variable K :=
⟨ 1, 0, 0, 0, by simp ⟩

def composite {K : Type*} [field K]
(C C' : linear_change_of_variable K) : linear_change_of_variable K :=
⟨ C.u*C'.u, C.r*C'.u^2 + C'.r, C'.u*C.s + C'.s,
  C.t*C'.u^3 + C.r*C'.s*C'.u^2 + C'.t, by simp ⟩

lemma comp_assoc {K : Type*} [field K]
(C C' C'' : linear_change_of_variable K) : ((C.composite C').composite C'') = (C.composite (C'.composite C'')) :=
begin
  simp [composite, ext_iff],
  split, { ring, }, split, { ring, }, split, { ring, }, ring,
end

@[simp]
lemma id_comp {K : Type*} [field K]
(C : linear_change_of_variable K) : (identity K).composite C = C :=
begin
  simp [composite, identity, ext_iff],
end

@[simp]
lemma comp_id {K : Type*} [field K]
(C : linear_change_of_variable K) : C.composite (identity K) = C :=
begin
  simp [composite, identity, ext_iff],
end

def inverse {K : Type*} [field K]
(C : linear_change_of_variable K) : linear_change_of_variable K :=
⟨ 1/C.u, -C.r/C.u^2, -C.s/C.u, (C.r*C.s-C.t)/C.u^3, by simp ⟩

@[simp]
lemma inv_comp {K : Type*} [field K]
(C : linear_change_of_variable K) : C.inverse.composite C = identity K :=
begin
  simp [composite, inverse, identity, ext_iff],
  split, { field_simp, ring, },
  field_simp [pow_succ], ring,
end

@[simp]
lemma comp_inv {K : Type*} [field K]
(C : linear_change_of_variable K) : C.composite C.inverse = identity K :=
begin
  simp [composite, inverse, identity, ext_iff],
  split, { field_simp [pow_succ], }, split, { field_simp [mul_comm], },
  field_simp [pow_succ], ring,
end

instance to_group (K : Type*) [field K] : group (linear_change_of_variable K)
:= ⟨ composite, comp_assoc, identity K, id_comp, comp_id, inverse,
  (λ C C', C.composite (C'.inverse)), by {
    intros _ _, simp only [has_mul.mul, mul_one_class.mul],
  }, inv_comp ⟩

end linear_change_of_variable
