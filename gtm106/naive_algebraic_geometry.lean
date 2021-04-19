import algebra.field
import data.list.basic
import data.list.func
import data.nat.basic
import data.int.basic
import data.rat.basic
import data.fin
import data.mv_polynomial.basic
import tactic

noncomputable theory

structure naive_affine_space (K : Type*) [field K] (d : ℕ) :=
mk ::

def naive_affine_space.mk1 (K : Type*) [field K] (d : ℕ) : naive_affine_space K d :=
naive_affine_space.mk

def naive_affine_space.regular_function_ring {K : Type*} [field K] {d : ℕ}
(A : naive_affine_space K d) :=
mv_polynomial (fin d) K

def naive_affine_space.x_i {K : Type*} [field K] {d : ℕ}
(A : naive_affine_space K d) (i : ℕ) (hi : i < d) : A.regular_function_ring :=
mv_polynomial.X (fin.mk i hi)

structure naive_affine_space.point {K : Type*} [field K] {d : ℕ}
(A : naive_affine_space K d) :=
mk :: (coord : list K) (h_length : coord.length = d)

def naive_affine_space.eval_at_point {K : Type*} [field K] {d : ℕ}
(A : naive_affine_space K d) (f : A.regular_function_ring) (p : A.point) : K :=
mv_polynomial.eval (λ i : (fin d), p.coord.nth_le i
(calc (i : ℕ) < p.coord.length : by { rw p.h_length, refine fin.is_lt i, })) f

structure naive_affine_hypersurface {K : Type*} [field K] {d : ℕ}
(A : naive_affine_space K d) :=
mk :: (f : A.regular_function_ring)

def naive_affine_space.point.is_on {K : Type*} [field K] {d : ℕ} {A : naive_affine_space K d}
(p : A.point) (S : naive_affine_hypersurface A) :=
A.eval_at_point S.f p = 0

structure naive_affine_hypersurface.point {K : Type*} [field K] {d : ℕ} {A : naive_affine_space K d}
(S : naive_affine_hypersurface A) extends naive_affine_space.point A :=
mk :: (h_on : naive_affine_space.point.is_on to_point S)

/-
structure naive_affine_plane (K : Type*) [field K] extends naive_affine_space K 2 :=
mk ::

def naive_affine_plane.x {K : Type*} [field K] (A : naive_affine_plane K) : A.to_naive_affine_space.regular_function_ring :=
A.to_naive_affine_space.x_i 0 (by norm_num)

def naive_affine_plane.y {K : Type*} [field K] (A : naive_affine_plane K) : A.to_naive_affine_space.regular_function_ring :=
A.to_naive_affine_space.x_i 1 (by norm_num)
-/
