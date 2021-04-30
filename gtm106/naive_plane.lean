import algebra.field
import tactic

noncomputable theory

/--
The set of R-points of affine plane is `Hom(Spec(R),A_Z^2)`,
which is just `R^2`
-/
@[ext]
structure affine_plane_point (K : Type*) [comm_ring K] :=
mk :: (x y : K)

def affine_plane_point.base_change {K : Type*} [comm_ring K]
(P : affine_plane_point K) {L : Type*} [comm_ring L] (f : ring_hom K L)
: affine_plane_point L := ⟨ f P.x, f P.y ⟩

/--
A point in `A^3` whose coordinates are not all-zero
-/
@[ext]
structure projective_plane_point' (K : Type*) [comm_ring K] :=
mk :: (X Y Z : K) (h : ¬ (X = 0 ∧ Y = 0 ∧ Z = 0))

def projective_plane_point'.base_change' {K : Type*} [field K]
(P : projective_plane_point' K) {L : Type*} [field L] (f : ring_hom K L)
: projective_plane_point' L := ⟨ f P.X, f P.Y, f P.Z, (by simp [ring_hom.map_eq_zero, P.h]) ⟩

def projective_plane_point'.is_equal {K : Type*} [field K]
(P P' : projective_plane_point' K) :=
∃ a : K, a ≠ 0 ∧ P'.X = a * P.X ∧ P'.Y = a * P.Y ∧ P'.Z = a * P.Z

lemma projective_plane_point'.is_equal.refl {K : Type*} [field K]
(P : projective_plane_point' K) : P.is_equal P :=
begin
  use 1,
  simp,
end

lemma projective_plane_point'.is_equal.symm {K : Type*} [field K]
(P P' : projective_plane_point' K) (h : P.is_equal P') : P'.is_equal P :=
begin
  rcases h with ⟨ a, h1, h2, h3, h4 ⟩,
  use 1/a,
  simp [h2, h3, h4, h1],
end

lemma projective_plane_point'.is_equal.trans {K : Type*} [field K]
(P P' P'' : projective_plane_point' K) (h : P.is_equal P') (h' : P'.is_equal P'') : P.is_equal P'' :=
begin
  rcases h with ⟨ a, h1, h2, h3, h4 ⟩,
  rcases h' with ⟨ a', h'1, h'2, h'3, h'4 ⟩,
  use a*a',
  rw [h'2, h'3, h'4, h2, h3, h4],
  split, { simp [h1, h'1], },
  split, { ring, },
  split, { ring, },
  ring,
end

lemma projective_plane_point'.is_equal.is_equivalence (K : Type*) [h : field K]
: equivalence (@projective_plane_point'.is_equal K h) :=
mk_equivalence (@projective_plane_point'.is_equal K h)
(@projective_plane_point'.is_equal.refl K h)
(@projective_plane_point'.is_equal.symm K h)
(@projective_plane_point'.is_equal.trans K h)

instance projective_plane_point.setoid (K : Type*) [h : field K]
: setoid (projective_plane_point' K) :=
setoid.mk (@projective_plane_point'.is_equal K h)
(projective_plane_point'.is_equal.is_equivalence K)

/--
The set of R-points of projective plane is `Hom(Spec(R),P_Z^2)`,
for simplicity we restrict ourself to field case, namely
the equivalent class of points in `A^3`
-/
def projective_plane_point (K : Type*) [field K] : Type* :=
quotient (projective_plane_point.setoid K)

def projective_plane_point'.base_change {K : Type*} [field K]
(P : projective_plane_point' K) {L : Type*} [field L] (f : ring_hom K L)
: projective_plane_point L := quotient.mk (P.base_change' f)

lemma projective_plane_point'.base_change.sound {K : Type*} [field K]
{L : Type*} [field L] (f : ring_hom K L)
(P P' : projective_plane_point' K) (h : P.is_equal P')
: P.base_change f = P'.base_change f :=
begin
  simp [projective_plane_point'.base_change, quotient.sound],
  rcases h with ⟨ a, h1, h2, h3, h4 ⟩,
  use (f a),
  simp [projective_plane_point'.base_change', h1, h2, h3, h4],
end

def projective_plane_point.base_change {K : Type*} [field K]
(P : projective_plane_point K) {L : Type*} [field L] (f : ring_hom K L)
: projective_plane_point L := quotient.lift (λ (P : projective_plane_point' K),
  projective_plane_point'.base_change P f)
(projective_plane_point'.base_change.sound f) P

def projective_plane_point'.is_finite {K : Type*} [field K]
(P : projective_plane_point' K) := P.Z ≠ 0

lemma projective_plane_point'.is_finite.sound {K : Type*} [field K]
(P P' : projective_plane_point' K) (h : P.is_equal P') : P.is_finite = P'.is_finite :=
begin
  rcases h with ⟨ a, h1, h2, h3, h4 ⟩,
  simp [projective_plane_point'.is_finite, h4, h1],
end

def projective_plane_point.is_finite {K : Type*} [h : field K]
(P : projective_plane_point K) := quotient.lift (@projective_plane_point'.is_finite K h)
(@projective_plane_point'.is_finite.sound K h) P

def projective_plane_point'.is_infinite {K : Type*} [field K]
(P : projective_plane_point' K) := P.Z = 0

lemma projective_plane_point'.is_infinite.sound {K : Type*} [field K]
(P P' : projective_plane_point' K) (h : P.is_equal P') : P.is_infinite = P'.is_infinite :=
begin
  rcases h with ⟨ a, h1, h2, h3, h4 ⟩,
  simp [projective_plane_point'.is_infinite, h4, h1],
end

def projective_plane_point.is_infinite {K : Type*} [h : field K]
(P : projective_plane_point K) := quotient.lift (@projective_plane_point'.is_infinite K h)
(@projective_plane_point'.is_infinite.sound K h) P

def projective_plane_point'.infinite_point_X (K : Type*) [field K]
: projective_plane_point' K := ⟨ 1, 0, 0, (by simp) ⟩

def projective_plane_point'.infinite_point_Y (K : Type*) [field K]
: projective_plane_point' K := ⟨ 0, 1, 0, (by simp) ⟩

def projective_plane_point'.infinite_point_slope (K : Type*) [field K]
(k : K) : projective_plane_point' K := ⟨ 1, k, 0, (by simp) ⟩

def projective_plane_point.infinite_point_X (K : Type*) [field K]
: projective_plane_point K := quotient.mk (projective_plane_point'.infinite_point_X K)

def projective_plane_point.infinite_point_Y (K : Type*) [field K]
: projective_plane_point K := quotient.mk (projective_plane_point'.infinite_point_Y K)

def projective_plane_point.infinite_point_slope (K : Type*) [field K]
(k : K) : projective_plane_point K := quotient.mk (projective_plane_point'.infinite_point_slope K k)

def affine_plane_point.to_projective_plane' {K : Type*} [field K]
(P : affine_plane_point K) : projective_plane_point' K := ⟨ P.x, P.y, 1, (by simp) ⟩

def affine_plane_point.to_projective_plane {K : Type*} [field K]
(P : affine_plane_point K) : projective_plane_point K := quotient.mk P.to_projective_plane'

def projective_plane_point'.to_affine_plane {K : Type*} [field K]
(P : projective_plane_point' K) : affine_plane_point K :=
affine_plane_point.mk (P.X/P.Z) (P.Y/P.Z)

def projective_plane_point'.to_affine_plane.sound {K : Type*} [field K]
(P P' : projective_plane_point' K) (h : P.is_equal P')
: P.to_affine_plane = P'.to_affine_plane :=
begin
  rcases h with ⟨ a, h1, h2, h3, h4 ⟩,
  by_cases hZ : P.Z ≠ 0, {
    simp [projective_plane_point'.to_affine_plane, h2, h3, h4],
    split, {
      symmetry,
      field_simp [h1, hZ],
      ring,
    },
    symmetry,
    field_simp [h1, hZ],
    ring,
  },
  simp at hZ,
  simp [projective_plane_point'.to_affine_plane, hZ, h4],
end

def projective_plane_point.to_affine_plane {K : Type*} [h : field K]
(P : projective_plane_point K) : affine_plane_point K :=
quotient.lift (@projective_plane_point'.to_affine_plane K h)
(@projective_plane_point'.to_affine_plane.sound K h) P

lemma affine_plane_point.embed_invertible {K : Type*} [field K]
(P : affine_plane_point K) : P.to_projective_plane.to_affine_plane = P :=
begin
  unfold projective_plane_point.to_affine_plane
  affine_plane_point.to_projective_plane
  affine_plane_point.to_projective_plane',
  simp [projective_plane_point'.to_affine_plane, affine_plane_point.ext_iff],
end

lemma projective_plane_point.embed_invertible {K : Type*} [field K]
(P : projective_plane_point K) (h : P.is_finite) : P.to_affine_plane.to_projective_plane = P :=
begin
  revert h P,
  refine quotient.ind _,
  intros P h,
  simp [projective_plane_point.is_finite, projective_plane_point'.is_finite] at h,
  refine quotient.sound _,
  simp [affine_plane_point.to_projective_plane',
    projective_plane_point.to_affine_plane, projective_plane_point'.to_affine_plane],
  use [P.Z, h],
  split, { field_simp [mul_comm], },
  split, { field_simp [mul_comm], },
  simp,
end
