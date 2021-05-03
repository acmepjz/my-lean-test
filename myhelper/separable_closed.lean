import data.nat.basic
import data.nat.prime
import data.rat.basic
import algebra.field
import algebra.char_zero
import algebra.char_p
import field_theory.separable
import field_theory.algebraic_closure
import field_theory.perfect_closure
import myhelper.char
import myhelper.perfect
import tactic

def my_sep_closed (K : Type*) [field K] :=
∀ f : polynomial K, f.separable → f.degree ≠ 0 → ∃ x : K, polynomial.eval₂ (ring_hom.id K) x f = 0

lemma alg_closed_implies_sep_closed (K : Type*) [field K] :
is_alg_closed K → my_sep_closed K :=
begin
  intros hac f hsep hdeg,
  have hsplit := @polynomial.splits' K K _ hac _ (ring_hom.id K) f,
  exact polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
end

lemma alg_closed_implies_pow_surj (K : Type*) [field K] [is_alg_closed K] (n : ℕ) (hn : n ≠ 0)
: nth_power_surjective K n :=
begin
  intro x,
  let f : polynomial K := polynomial.X^n - (polynomial.C x),
  have hdeg := calc f.degree = n : polynomial.degree_X_pow_sub_C (nat.pos_of_ne_zero hn) x
  ... ≠ 0 : by { norm_cast, exact hn, },
  have hsplit := @polynomial.splits' K K _ _ _ (ring_hom.id K) f,
  replace hsplit := polynomial.exists_root_of_splits (ring_hom.id K) hsplit hdeg,
  cases hsplit with y hy,
  use y,
  simp at hy,
  calc y ^ n = x + (y ^ n - x) : by ring
  ... = x : by { rw hy, ring, },
end

lemma sep_closed_implies_pow_surj (K : Type*) [field K] (hsc : my_sep_closed K) (n : ℕ) (hn : ¬ (ring_char K) ∣ n)
: nth_power_surjective K n :=
begin
  intro x,
  have hn' : n ≠ 0 := by { intro h, rw h at hn, simp at hn, exact hn, },
  by_cases hx : x = 0, {
    use 0,
    simp only [hx, hn', ne.def, not_false_iff, zero_pow'],
  },
  let f : polynomial K := polynomial.X^n - (polynomial.C x),
  have hdeg := calc f.degree = n : polynomial.degree_X_pow_sub_C (nat.pos_of_ne_zero hn') x
  ... ≠ 0 : by { norm_cast, exact hn', },
  let f' : polynomial K := (polynomial.C (n : K)) * polynomial.X^(n-1),
  have hf' : f' = f.derivative := by {
    have : f = (polynomial.C (1 : K)) * polynomial.X^n - (polynomial.C x) := by simp,
    rw [this, polynomial.derivative_sub, polynomial.derivative_C_mul_X_pow, polynomial.derivative_C],
    simp,
  },
  have hcop : is_coprime f f.derivative := by {
    rw ← hf',
    let a : polynomial K := polynomial.C (-(1 : K) / x),
    let b : polynomial K := polynomial.C ((1 : K) / x / n) * polynomial.X,
    use [a, b],
    have hnK : (n : K) ≠ 0 := by {
      refine ndvd_char_is_non_zero (calc ring_char K = ring_char K : rfl) n _,
      norm_cast, exact hn,
    },
    calc a * f + b * f'
    = (polynomial.C (-(1 : K) / x)) * polynomial.X^n - (polynomial.C (-(1 : K) / x)) * (polynomial.C x)
    + polynomial.C ((1 : K) / x / n) * (polynomial.C (n : K)) * (polynomial.X * polynomial.X^(n-1)) : by {
      rw mul_sub,
      rw mul_assoc _ polynomial.X,
      rw ← mul_assoc polynomial.X _,
      rw mul_comm polynomial.X (polynomial.C (n : K)),
      repeat { rw ← mul_assoc },
    }
    ... = 1 : by {
      repeat { rw ← polynomial.C_mul },
      rw ← pow_succ _ (n-1),
      have := nat.pos_of_ne_zero hn',
      have : 1 ≤ n := by linarith,
      have : n-1+1=n := by { rw nat.sub_add_eq_add_sub this, simp, },
      rw this,
      rw sub_add_eq_add_sub,
      rw ← add_mul,
      rw ← polynomial.C_add,
      have : (-1) / x + 1 / x / ↑n * ↑n = 0 := by {
        field_simp [hx, hnK], ring,
      },
      rw this,
      have : (-1) / x * x = -1 := by { field_simp [hx], },
      rw this,
      rw polynomial.C_0,
      rw zero_mul,
      simp,
    },
  },
  cases hsc f hcop hdeg with y hy,
  use y,
  simp at hy,
  calc y ^ n = x + (y ^ n - x) : by ring
  ... = x : by { rw hy, ring, },
end
