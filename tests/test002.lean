import data.nat.basic
import tactic

noncomputable theory

open nat

theorem prob (f : ℕ → ℕ) (hinc : ∀ m n : ℕ, m < n → f m < f n) (hff : ∀ n : ℕ, f (f n) = 3 * n)
: f 0 = 0
∧ (∀ k n : ℕ, n ≤ 3 ^ k → f (3 ^ k + n) = 2 * 3 ^ k + n)
∧ (∀ k n : ℕ, n ≤ 3 ^ k → f (2 * 3 ^ k + n) = 3 * (3 ^ k + n)) :=
begin
  have h1 : f 0 = 0 := by {
    by_contradiction,
    have := hinc 0 (f 0) (nat.pos_of_ne_zero h),
    rw hff 0 at this,
    simp at this,
    exact not_lt_zero (f 0) this,
  },
  split, { exact h1, },
  have h2 : ∀ n k : ℕ, f(n) + k ≤ f(n+k) := by {
    intros n k,
    induction k with k hk,
    { simp, },
    rw succ_eq_add_one,
    repeat {rw ← add_assoc},
    calc f n + k + 1 ≤ f (n + k) + 1 : add_le_add_right hk 1
    ... ≤ f (n + k + 1) : by {
      have : n + k < n + k + 1 := lt_add_one (n + k),
      have : f (n + k) < f (n + k + 1) := hinc (n + k) (n + k + 1) this,
      exact succ_le_iff.mpr this,
    },
  },
  have h3 : f 1 = 2 := by {
    have t1 := h2 0 1,
    rw h1 at t1,
    simp at t1,
    by_cases t2 : f 1 < 2, {
      exfalso,
      have t3 : f 1 = 1 := le_antisymm (lt_succ_iff.mp t2) t1,
      have t4 : f 1 = 3 := by { have := hff 1, rw t3 at this, simp at this, exact this, },
      linarith only [t3, t4],
    },
    by_cases t3 : 2 < f 1, {
      exfalso,
      have t4 : 3 ≤ f 1 := succ_le_iff.mpr t3,
      have t5 : f 1 < f 2 := hinc 1 2 one_lt_two,
      have t6 : f 2 < f (f 1) := hinc 2 (f 1) t3,
      rw hff 1 at t6,
      simp at t6,
      linarith only [t4, t5, t6],
    },
    linarith only [t2, t3],
  },
  have h4 : ∀ k : ℕ, f (3 ^ k) = 2 * 3 ^ k ∧ f (2 * 3 ^ k) = 3 * 3 ^ k := by {
    intro k,
    induction k with k hk, {
      simp,
      split, { exact h3, },
      have := hff 1,
      rw h3 at this,
      simpa,
    }, {
      rw pow_succ,
      have t1 : f (3 * 3 ^ k) = 2 * (3 * 3 ^ k) := by {
        have := hff (2 * 3 ^ k),
        rw hk.2 at this,
        rw this,
        ring,
      },
      have := hff (3 * 3 ^ k),
      rw t1 at this,
      exact ⟨ t1, this ⟩,
    },
  },
  have h5 : ∀ k n : ℕ, n ≤ 3 ^ k → f (3 ^ k + n) = 2 * 3 ^ k + n := by {
    intros k n hnk,
    cases h4 k with t1 t2,
    have t3 : 2 * 3 ^ k + n ≤ f (3 ^ k + n) := by { have := h2 (3 ^ k) n, rw t1 at this, exact this, },
    cases le.dest hnk with m hm,
    have t4 := calc f (3 ^ k + n) + m ≤ f (3 ^ k + n + m) : h2 (3 ^ k + n) m
    ... = f (2 * 3 ^ k) : by { congr, rw ← hm, ring, }
    ... = 3 * 3 ^ k : t2
    ... = 2 * 3 ^ k + 3 ^ k : by ring
    ... = 2 * 3 ^ k + n + m : by { rw ← hm, ring, },
    rw add_le_add_iff_right m at t4,
    linarith only [t3, t4],
  },
  split, { exact h5, },
  intros k n hnk,
  have := hff (3 ^ k + n),
  rw h5 k n hnk at this,
  exact this,
end
