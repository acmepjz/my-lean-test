import algebra.field
import data.nat.basic
import data.int.basic
import data.rat.basic
import tactic

noncomputable theory

@[ext]
structure affine_plane_point (K : Type*) [field K] :=
mk :: (x y : K)

@[ext]
structure projective_plane_point (K : Type*) [field K] :=
mk :: (X Y Z : K) (h : ¬ (X = 0 ∧ Y = 0 ∧ Z = 0))

def projective_plane_point.is_equal {K : Type*} [field K]
(P P' : projective_plane_point K) :=
∃ a : K, a ≠ 0 ∧ P'.X = a * P.X ∧ P'.Y = a * P.Y ∧ P'.Z = a * P.Z

def projective_plane_point.is_finite {K : Type*} [field K]
(P : projective_plane_point K) := P.Z ≠ 0

def projective_plane_point.is_infinite {K : Type*} [field K]
(P : projective_plane_point K) := P.Z = 0

def projective_plane_point.infinite_point_X (K : Type*) [field K]
: projective_plane_point K :=
projective_plane_point.mk 1 0 0 (by simp)

def projective_plane_point.infinite_point_Y (K : Type*) [field K]
: projective_plane_point K :=
projective_plane_point.mk 0 1 0 (by simp)

def projective_plane_point.infinite_point_slope (K : Type*) [field K]
(k : K) : projective_plane_point K :=
projective_plane_point.mk 1 k 0 (by simp)

def affine_plane_point.to_projective_plane {K : Type*} [field K]
(P : affine_plane_point K) : projective_plane_point K :=
projective_plane_point.mk P.x P.y 1 (by simp)

def projective_plane_point.to_affine_plane {K : Type*} [field K]
(P : projective_plane_point K) : affine_plane_point K :=
affine_plane_point.mk (P.X/P.Z) (P.Y/P.Z)

lemma affine_plane_point.embed_invertible {K : Type*} [field K]
(P : affine_plane_point K) : P = P.to_projective_plane.to_affine_plane :=
begin
  unfold projective_plane_point.to_affine_plane
  affine_plane_point.to_projective_plane
  projective_plane_point.X
  projective_plane_point.Y
  projective_plane_point.Z,
  ring,
  ext; refl,
end

lemma projective_plane_point.embed_invertible {K : Type*} [field K]
(P : projective_plane_point K) (h : P.is_finite) : P.is_equal P.to_affine_plane.to_projective_plane :=
begin
  unfold affine_plane_point.to_projective_plane
  projective_plane_point.to_affine_plane
  affine_plane_point.x
  affine_plane_point.y,
  use 1/P.Z,
  unfold projective_plane_point.is_finite at h,
  unfold projective_plane_point.X
  projective_plane_point.Y
  projective_plane_point.Z,
  field_simp [h],
end
