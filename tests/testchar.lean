import data.nat.basic
import data.nat.prime
import data.rat.basic
import algebra.field
import algebra.char_zero
import algebra.char_p
import tactic

example (K : Type*) [field K] : nat.prime (ring_char K) ∨ ring_char K = 0 :=
begin
  let p := ring_char K,
  have h : ring_char K = p := rfl,
  rw h,
  rw ring_char.eq_iff at h,
  exact char_p.char_is_prime_or_zero K p,
end

example : char_zero ℚ :=
begin
  exact char_p.char_p_to_char_zero ℚ,
end

example : ring_char ℚ = 0 :=
begin
  have : char_p ℚ 0 := char_p.of_char_zero ℚ,
  have := ring_char.eq ℚ this,
  exact this.symm,
end

lemma prime_neq_char_is_non_zero
(K : Type*) [field K] (q : ℕ) (hq : nat.prime q) (hneq : ring_char K ≠ q) : (q : K) ≠ 0 :=
begin
  intro h0,
  replace h0 := ring_char.dvd h0,
  set p := ring_char K with ← hp,
  rw ring_char.eq_iff at hp,
  cases char_p.char_is_prime_or_zero K p with hp' hp', {
    rw nat.prime_dvd_prime_iff_eq hp' hq at h0,
    exact hneq h0,
  },
  rw hp' at h0,
  simp at h0,
  simp [h0, hp'] at hneq,
  exact hneq,
end

example (K : Type*) [field K] (h : (2 : K) ≠ 0) (x : K) : (x * 2) / 2 = x :=
begin
  field_simp [h],
end
