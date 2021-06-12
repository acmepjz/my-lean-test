import field_theory.perfect_closure
import tactic

noncomputable theory

def nth_power_surjective (K : Type*) [comm_ring K] (n : ℕ) :=
∀ x : K, ∃ y : K, y ^ n = x

def my_perfect_field (K : Type*) [comm_ring K] :=
ring_char K = 0 ∨ nth_power_surjective K (ring_char K)
