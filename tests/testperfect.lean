import data.nat.basic
import data.nat.prime
import data.rat.basic
import algebra.field
import algebra.char_zero
import algebra.char_p
import field_theory.perfect_closure
import tactic

noncomputable theory

def nth_power_surjective (K : Type*) [field K] (n : ℕ) :=
∀ x : K, ∃ y : K, y ^ n = x

def my_perfect_field (K : Type*) [field K] :=
ring_char K = 0 ∨ nth_power_surjective K (ring_char K)

