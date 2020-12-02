import data.int.basic
import data.int.parity
import data.int.gcd
import data.nat.basic
import data.nat.prime
import data.rat.basic
import ring_theory.multiplicity
import number_theory.pythagorean_triples
import tactic

noncomputable theory

lemma rat.stupid (q : ℚ) : ∃ n d : ℤ, 0 < d ∧ q = (n : ℚ) / d :=
begin
  use [q.num, q.denom],
  split, { norm_cast, exact q.pos, },
  rw [← rat.mk_eq_div, rat.num_denom],
end

lemma gcd_neg (a b : ℤ) : a.gcd b = a.gcd (-b) :=
begin
  have t1 := int.dvd_gcd (int.gcd_dvd_left a b) (dvd_neg_of_dvd (int.gcd_dvd_right a b)),
  have t2 := int.dvd_gcd (int.gcd_dvd_left a (-b)) (dvd_neg_of_dvd (int.gcd_dvd_right a (-b))),
  rw neg_neg at t2,
  norm_cast at t1 t2,
  exact nat.dvd_antisymm t1 t2,
end

lemma abs.stupid_gcd (x y : ℤ) : x.gcd y = x.gcd (abs y) :=
begin
  by_cases h : y ≥ 0, { rw abs_of_nonneg h, },
  push_neg at h,
  rw abs_of_neg h,
  exact gcd_neg x y,
end

lemma abs.stupid_sqr (x : ℤ) : abs x^2 = x^2 :=
begin
  have := abs_mul_abs_self x,
  ring at this,
  exact this,
end

lemma abs.stupid_mod_two (x : ℤ) : (abs x) % 2 = x % 2 :=
begin
  by_cases h : x ≥ 0, { rw abs_of_nonneg h, },
  push_neg at h,
  rw abs_of_neg h,
  exact int.neg_mod_two x,
end

lemma gcd_add (a b k : ℤ) : a.gcd b = a.gcd (b+k*a) :=
begin
  have key : ∀ a b k : ℤ, a.gcd b ∣ a.gcd (b+k*a) := by {
    intros a b k,
    have t1 := int.gcd_dvd_left a b,
    have t2 := dvd_add (int.gcd_dvd_right a b) (dvd_mul_of_dvd_right t1 k),
    have := int.dvd_gcd t1 t2,
    norm_cast at this,
    exact this,
  },
  have t1 := key a b k,
  have t2 := key a (b+k*a) (-k),
  simp at t2,
  exact nat.dvd_antisymm t1 t2,
end

example (a b : ℤ) : b ∣ a ↔ b.nat_abs ∣ a.nat_abs :=
begin
  exact int.nat_abs_dvd_abs_iff.symm,
end

example (a b : ℕ) : (a:ℤ).gcd b = a.gcd b :=
begin
  refl,
end

example (a b : ℕ) : a ∣ b → b%a=0 :=
begin
  exact nat.mod_eq_zero_of_dvd,
end

example (a b p : ℕ) (hp : nat.prime p) :
multiplicity p (a*b) = (multiplicity p a) + (multiplicity p b) :=
begin
  have hp' : prime p := nat.prime_iff.mp hp,
  exact multiplicity.mul hp',
end

-- oops
lemma nat_not_dvd_of_pos_of_lt {a b : ℕ} (h1 : 0 < b) (h2 : b < a) : ¬ a ∣ b :=
begin
  rintros ⟨c, rfl⟩,
  rcases nat.eq_zero_or_pos c with (rfl | hc),
  { exact lt_irrefl 0 h1 },
  { exact not_lt.2 (nat.le_mul_of_pos_right hc) h2 },
end

lemma nat_n_lt_pow_2_n (n p : ℕ) (hp' : 2 ≤ p) : n < p ^ n :=
begin
  induction n with n hn, { simp, },
  calc n.succ < p^n + 1 : by { rw nat.succ_eq_add_one, linarith only [hn], }
  ... ≤ 2 * p ^ n : by { have := nat.one_le_pow n p (by linarith only [hp']), linarith only [this], }
  ... ≤ p * p ^ n : (mul_le_mul_right (pow_pos (calc 0 < p : by linarith only [hp']) n)).mpr hp'
  ... = p ^ n.succ : by { rw pow_succ, },
end

lemma nat_mult_fin_iff (a p : ℕ) (hp : nat.prime p) :
multiplicity p a ≠ ⊤ ↔ a ≠ 0 :=
begin
  split, {
    intro hmult,
    cases enat.ne_top_iff.1 hmult with v hv,
    rw multiplicity.eq_some_iff at hv,
    replace hv := hv.2,
    intro ha,
    rw ha at hv,
    simp at hv,
    exact hv,
  },
  induction a with a ha, { simp, },
  clear ha,
  intro ha, clear ha,
  have hp' : 2 ≤ p := nat.prime.two_le hp,
  have key := nat_n_lt_pow_2_n a.succ p (nat.prime.two_le hp),
  have := multiplicity.finite_def.2 ⟨ a, nat_not_dvd_of_pos_of_lt (nat.succ_pos a) key ⟩,
  intro h,
  exact multiplicity.eq_top_iff_not_finite.1 h this,
end

lemma nat_mult_gcd_eq_min_mult (a b p : ℕ) (hp : nat.prime p) :
multiplicity p (a.gcd b) = min (multiplicity p a) (multiplicity p b) :=
begin
  by_cases H : 0 < a.gcd b, {
    have hp' : prime p := nat.prime_iff.mp hp,
    let a' := a / a.gcd b,
    let b' := b / a.gcd b,
    have ha' : a' * a.gcd b = a := nat.div_mul_cancel (nat.gcd_dvd_left a b),
    have hb' : b' * a.gcd b = b := nat.div_mul_cancel (nat.gcd_dvd_right a b),
    apply_fun multiplicity p at ha',
    apply_fun multiplicity p at hb',
    rw multiplicity.mul hp' at ha',
    rw multiplicity.mul hp' at hb',
    have hcop : a'.coprime b' := nat.coprime_div_gcd_div_gcd H,
    by_cases hle' : multiplicity p a' ≤ multiplicity p b', {
      have ha'0 := multiplicity_eq_zero_of_coprime (nat.prime.ne_one hp) hle' hcop,
      have hle : multiplicity p a ≤ multiplicity p b := by { rw [← ha', ← hb'], exact add_le_add_right hle' _, },
      rw [ha'0, zero_add] at ha',
      rw ha',
      exact (min_eq_left hle).symm,
    },
    replace hle' : multiplicity p b' ≤ multiplicity p a' := le_of_lt (not_le.mp hle'),
    have hb'0 := multiplicity_eq_zero_of_coprime (nat.prime.ne_one hp) hle' (nat.coprime.symm hcop),
    have hle : multiplicity p b ≤ multiplicity p a := by { rw [← ha', ← hb'], exact add_le_add_right hle' _, },
    rw [hb'0, zero_add] at hb',
    rw hb',
    exact (min_eq_right hle).symm,
  },
  replace H : a.gcd b = 0 := by linarith only [H],
  have ha : a = 0 := nat.eq_zero_of_gcd_eq_zero_left H,
  have hb : b = 0 := nat.eq_zero_of_gcd_eq_zero_right H,
  rw [H, ha, hb],
  simp,
end

lemma nat_mult_lcm_eq_max_mult (a b p : ℕ) (hp : nat.prime p) :
multiplicity p (a.lcm b) = max (multiplicity p a) (multiplicity p b) :=
begin
  by_cases H : 0 < a.gcd b, {
    have hp' : prime p := nat.prime_iff.mp hp,
    have h := nat.gcd_mul_lcm a b,
    apply_fun multiplicity p at h,
    repeat {rw multiplicity.mul hp' at h},
    rw [← min_add_max (multiplicity p a) (multiplicity p b), ← nat_mult_gcd_eq_min_mult a b p hp] at h,
    have h1 := (nat_mult_fin_iff (a.gcd b) p hp).2 (by linarith only [H]),
    exact (enat.add_left_cancel_iff h1).1 h,
  },
  replace H : a.gcd b = 0 := by linarith only [H],
  have ha : a = 0 := nat.eq_zero_of_gcd_eq_zero_left H,
  have hb : b = 0 := nat.eq_zero_of_gcd_eq_zero_right H,
  rw [ha, hb, nat.lcm_zero_left],
  simp,
end

lemma nat_dvd_iff_mult_le.tfae1 (a b : ℕ) :
a ∣ b → (∀ p : ℕ, multiplicity p a ≤ multiplicity p b) :=
begin
  intros hdvd p,
  set! v := multiplicity p a with hv, clear_value v,
  rw ← hv,
  by_cases vinf : v = ⊤, {
    rw vinf at hv,
    replace hv := hv.symm,
    rw multiplicity.eq_top_iff at hv,
    replace hv : ∀ (n : ℕ), p ^ n ∣ b := by { intro n, exact dvd_trans (hv n) hdvd, },
    rw ← multiplicity.eq_top_iff at hv,
    rw [vinf, hv],
  },
  cases enat.ne_top_iff.1 vinf with v' hv',
  rw hv' at hv ⊢,
  replace hv := dvd_trans (multiplicity.eq_some_iff.1 hv.symm).1 hdvd,
  exact multiplicity.pow_dvd_iff_le_multiplicity.1 hv,
end

lemma nat_dvd_iff_mult_le.tfae2 (a b : ℕ) : (∀ p : ℕ, multiplicity p a ≤ multiplicity p b)
→ (∀ p : ℕ, nat.prime p → multiplicity p a ≤ multiplicity p b) :=
begin
  intros hdvd p hp,
  exact hdvd p,
end

lemma nat_dvd_iff_mult_le.tfae3 (a b : ℕ) : (∀ p : ℕ, nat.prime p → multiplicity p a ≤ multiplicity p b)
→ a ∣ b :=
begin
  intros hmult,
  by_cases ha : a = 0, {
    rw [ha, zero_dvd_iff],
    by_contradiction hb,
    have hbpos : 0 < b := nat.pos_of_ne_zero hb,
    rcases nat.exists_infinite_primes (b+1) with ⟨ p, hpbig, hp ⟩,
    replace hmult := hmult p hp,
    have t1 : p^0 ∣ b ∧ ¬ p^(0+1) ∣ b := by {
      simp,
      have : b < p := by linarith only [hbpos, hpbig],
      exact nat_not_dvd_of_pos_of_lt hbpos this,
    },
    rw ← multiplicity.eq_some_iff at t1,
    rw [ha, t1] at hmult,
    simp at hmult,
    have := enat.coe_ne_top 0,
    rw hmult at this,
    norm_cast at this,
  },
  replace ha := nat.pos_of_ne_zero ha,
  rw nat.gcd_eq_left_iff_dvd,
  by_contradiction,
  replace h : a.gcd b < a := (ne.le_iff_lt h).mp (nat.gcd_le_left b ha),
  have h2 := nat.gcd_pos_of_pos_left b ha,
  let a' := a / a.gcd b,
  have ha' : a' * a.gcd b = a := nat.div_mul_cancel (nat.gcd_dvd_left a b),
  have ha'1 : a' ≠ 1 := by {
    intro ha'1,
    rw [ha'1, one_mul] at ha',
    linarith only [h, ha'],
  },
  let p := nat.min_fac a',
  have hp : nat.prime p := nat.min_fac_prime ha'1,
  have hpdvd : p^1 ∣ a' := by { ring, exact nat.min_fac_dvd a', },
  replace hpdvd := multiplicity.le_multiplicity_of_pow_dvd hpdvd,
  replace hmult := hmult p hp,
  have hp' : prime p := nat.prime_iff.mp hp,
  apply_fun multiplicity p at ha',
  rw [multiplicity.mul hp', nat_mult_gcd_eq_min_mult a b p hp, min_eq_left hmult] at ha',
  replace ha' : multiplicity p a' + multiplicity p a = 0 + multiplicity p a := by { simp, exact ha', },
  have : multiplicity p a ≠ ⊤ := (nat_mult_fin_iff a p hp).2 (by linarith only [ha]),
  rw enat.add_right_cancel_iff this at ha',
  rw ha' at hpdvd,
  norm_cast at hpdvd,
  linarith only [hpdvd],
end

lemma nat_dvd_iff_mult_le (a b : ℕ) : a ∣ b ↔ (∀ p : ℕ, nat.prime p → multiplicity p a ≤ multiplicity p b) :=
begin
  split, {
    intro hdvd,
    exact nat_dvd_iff_mult_le.tfae2 a b (nat_dvd_iff_mult_le.tfae1 a b hdvd),
  },
  exact nat_dvd_iff_mult_le.tfae3 a b,
end

lemma nat_eq_iff_mult_eq (a b : ℕ) : a = b ↔ (∀ p : ℕ, nat.prime p → multiplicity p a = multiplicity p b) :=
begin
  split, {
    intros heq p hp,
    rw heq,
  },
  intro hmult,
  have hmult1 : (∀ p : ℕ, nat.prime p → multiplicity p a ≤ multiplicity p b) := by {
    intros p hp,
    exact (hmult p hp).le,
  },
  have hmult2 : (∀ p : ℕ, nat.prime p → multiplicity p b ≤ multiplicity p a) := by {
    intros p hp,
    exact (hmult p hp).ge,
  },
  have t1 := nat_dvd_iff_mult_le.tfae3 a b hmult1,
  have t2 := nat_dvd_iff_mult_le.tfae3 b a hmult2,
  exact nat.dvd_antisymm t1 t2,
end

lemma gcd_lcm (a b c : ℤ) : a.gcd (b.lcm c) = (a.gcd b).lcm (a.gcd c) :=
begin
  change a.nat_abs.gcd (b.nat_abs.lcm c.nat_abs) = (a.nat_abs.gcd b.nat_abs).lcm (a.nat_abs.gcd c.nat_abs),
  set a' := a.nat_abs,
  set b' := b.nat_abs,
  set c' := c.nat_abs,
  clear_value a' b' c',
  clear a b c,
  rw nat_eq_iff_mult_eq,
  intros p hp,
  rw nat_mult_lcm_eq_max_mult _ _ p hp,
  repeat {rw nat_mult_gcd_eq_min_mult _ _ p hp},
  rw nat_mult_lcm_eq_max_mult _ _ p hp,
  exact min_max_distrib_left,
end

lemma gcd_mul (a b c : ℤ) (hcop : b.gcd c = 1) : a.gcd (b*c) = (a.gcd b) * (a.gcd c) :=
begin
  have t0 := gcd_lcm a b c,
  have t1 := int.gcd_mul_lcm b c,
  have t2 : (a.gcd b).gcd (a.gcd c) = 1 := by {
    change ((a.gcd b) : ℤ).gcd (a.gcd c) = 1,
    rw [int.gcd_comm a c, ← int.gcd_assoc, int.gcd_assoc a b c, hcop],
    simp,
  },
  have t3 := nat.gcd_mul_lcm (a.gcd b) (a.gcd c),
  rw [hcop, one_mul] at t1,
  rw [t2, one_mul] at t3,
  rw [t1, t3, ← int.abs_eq_nat_abs (b * c), ← abs.stupid_gcd a (b * c)] at t0,
  exact t0,
end

lemma mul_gcd (a b c : ℤ) (hcop : a.gcd b = 1) : (a*b).gcd c = (a.gcd c) * (b.gcd c) :=
begin
  repeat {rw int.gcd_comm _ c},
  exact gcd_mul c a b hcop,
end

lemma nat_mul_coprime_prime' {a b p k : ℕ}
(hapos : 0 < a) (hbpos : 0 < b) (hcop : a.gcd b = 1) (hp : nat.prime p) (h1 : a * b = p ^ k)
: (a = p ^ k ∧ b = 1) ∨ (a = 1 ∧ b = p ^ k) :=
begin
  have hp' : prime p := nat.prime_iff.mp hp,
  by_cases hle : multiplicity p a ≤ multiplicity p b, {
    right,
    rw mul_comm at h1,
    have ha := multiplicity_eq_zero_of_coprime (nat.prime.ne_one hp) hle hcop,
    have hb := h1, apply_fun multiplicity p at hb,
    rw [multiplicity.mul hp', ha, add_zero, multiplicity.multiplicity_pow_self_of_prime hp'] at hb,
    replace hb := nat.dvd_antisymm (dvd.intro a h1) (multiplicity.eq_some_iff.1 hb).1,
    rw hb at h1,
    replace h1 : p ^ k * a = p ^ k * 1 := by { rw h1, ring, },
    replace h1 := mul_left_cancel' (pow_ne_zero k (nat.prime.ne_zero hp)) h1,
    exact ⟨ h1, hb ⟩,
  },
  replace hle : multiplicity p b ≤ multiplicity p a := le_of_lt (not_le.mp hle),
  left,
  rw nat.gcd_comm at hcop,
  have hb := multiplicity_eq_zero_of_coprime (nat.prime.ne_one hp) hle hcop,
  have ha := h1, apply_fun multiplicity p at ha,
  rw [multiplicity.mul hp', hb, add_zero, multiplicity.multiplicity_pow_self_of_prime hp'] at ha,
  replace ha := nat.dvd_antisymm (dvd.intro b h1) (multiplicity.eq_some_iff.1 ha).1,
  rw ha at h1,
  replace h1 : p ^ k * b = p ^ k * 1 := by { rw h1, ring, },
  replace h1 := mul_left_cancel' (pow_ne_zero k (nat.prime.ne_zero hp)) h1,
  exact ⟨ ha, h1 ⟩,
end

lemma nat_pow_coprime_prime' {a b c p n k : ℕ}
(hapos : 0 < a) (hbpos : 0 < b) (hcop : a.gcd b = 1) (hp : nat.prime p) (h1 : a * b = p ^ k * c ^ n)
: ∃ a' b' : ℕ, 0 < a' ∧ 0 < b' ∧ a'.gcd b' = 1
∧ ((a = p ^ k * a' ^ n ∧ b = b' ^ n) ∨ (a = a' ^ n ∧ b = p ^ k * b' ^ n)) :=
begin
  have hp' : prime p := nat.prime_iff.mp hp,
  by_cases hn : n = 0, {
    rw hn at h1 ⊢,
    ring at h1 ⊢,
    rw mul_comm at h1,
    -- sloppy, should use [1, c]
    use [1, 1],
    use (by norm_num),
    use (by norm_num),
    use (by norm_num),
    exact nat_mul_coprime_prime' hapos hbpos hcop hp h1,
  },
  replace hn : 0 < n := nat.pos_of_ne_zero hn,
  have key : ∀ C a b c : ℕ, c ≤ C → 0 < a → 0 < b → a.gcd b = 1 → a * b = p ^ k * c ^ n
  → ∃ a' b' : ℕ, 0 < a' ∧ 0 < b' ∧ a'.gcd b' = 1
  ∧ ((a = p ^ k * a' ^ n ∧ b = b' ^ n) ∨ (a = a' ^ n ∧ b = p ^ k * b' ^ n)) := by {
    clear h1 hcop hbpos hapos c b a,
    intros C,
    induction C with C hind, {
      intros a b c hc hapos hbpos hcop h1,
      exfalso,
      replace hc : c = 0 := by linarith only [hc],
      rw [hc, zero_pow hn, mul_zero, mul_eq_zero] at h1,
      cases h1 with ha hb,
      { linarith only [hapos, ha], },
      { linarith only [hbpos, hb], },
    },
    intros a b c hc hapos hbpos hcop h1,
    by_cases hc' : c < C.succ, {
      have : c ≤ C := nat.lt_succ_iff.mp hc',
      exact hind a b c this hapos hbpos hcop h1,
    },
    replace hc : c = C.succ := by linarith only [hc, hc'],
    clear hc',
    by_cases hc' : c = 1, {
      rw [hc', one_pow, mul_one] at h1,
      use [1, 1],
      use (by norm_num),
      use (by norm_num),
      use (by norm_num),
      rw one_pow, repeat {rw mul_one},
      exact nat_mul_coprime_prime' hapos hbpos hcop hp h1,
    },
    let q := c.min_fac,
    have hq : nat.prime q := nat.min_fac_prime hc',
    have hq' : prime q := nat.prime_iff.mp hq,
    have hq1 : q ∣ c := nat.min_fac_dvd c,
    have k1 : q^n ∣ a ∨ q^n ∣ b := by {
      have := calc q^n ∣ c^n : by { rw nat.pow_dvd_pow_iff hn, exact hq1 }
      ... ∣ p^k * c^n : dvd_mul_left (c^n) (p^k)
      ... = a*b : h1.symm,
      replace this := nat_dvd_iff_mult_le.tfae1 (q ^ n) (a * b) this q,
      rw [multiplicity.mul hq', multiplicity.multiplicity_pow_self_of_prime hq'] at this,
      by_cases hle : multiplicity q a ≤ multiplicity q b, {
        right,
        rw [multiplicity_eq_zero_of_coprime (nat.prime.ne_one hq) hle hcop, zero_add] at this,
        exact multiplicity.pow_dvd_of_le_multiplicity this,
      },
      replace hle : multiplicity q b ≤ multiplicity q a := le_of_lt (not_le.mp hle),
      left,
      rw nat.gcd_comm at hcop,
      rw [multiplicity_eq_zero_of_coprime (nat.prime.ne_one hq) hle hcop, add_zero] at this,
      exact multiplicity.pow_dvd_of_le_multiplicity this,
    },
    let c'' := c / q,
    have hc1 : c'' * q = c := nat.div_mul_cancel hq1,
    have hc2 : c'' < C.succ := by {
      by_contradiction, push_neg at h,
      have : 0 < C.succ := nat.succ_pos C,
      have : 0 < c'' := by linarith,
      have := calc c'' = c'' * 1 : by ring
      ... < c'' * q : mul_lt_mul_of_pos_left (nat.prime.one_lt hq) this,
      linarith,
    },
    replace hc2 : c'' ≤ C := nat.lt_succ_iff.mp hc2,
    cases k1 with k1 k1, {
      let a'' := a/q^n,
      have ha1 : a'' * q^n = a := nat.div_mul_cancel k1,
      have ha''pos : 0 < a'' := by {
        by_contradiction, simp at h, rw h at ha1,
        simp at ha1, linarith only [ha1, hapos],
      },
      have hcop'' : a''.gcd b = 1 := nat.coprime.coprime_div_left hcop k1,
      have h1'' : a'' * b = p ^ k * c'' ^ n := by {
        apply mul_left_cancel' (pow_ne_zero n (nat.prime.ne_zero hq)),
        rw [← ha1, ← hc1] at h1,
        calc q ^ n * (a'' * b) = a'' * q ^ n * b : by ring
        ... = q ^ n * (p ^ k * c'' ^ n) : by { rw [h1, mul_pow], ring, },
      },
      rcases hind a'' b c'' hc2 ha''pos hbpos hcop'' h1'' with ⟨ a', b', ha'pos, hb'pos, hcop', h1' ⟩,
      use [a'*q, b'],
      use mul_pos ha'pos (nat.prime.pos hq),
      use hb'pos,
      split, {
        have : q.gcd b' = 1 := by {
          cases nat.coprime_or_dvd_of_prime hq b' with h h, { exact h, },
          exfalso,
          replace h : q^n ∣ b := by {
            cases h1' with h1' h1', {
              rw [h1'.2, nat.pow_dvd_pow_iff hn], exact h,
            }, {
              rw h1'.2, exact dvd_mul_of_dvd_right ((nat.pow_dvd_pow_iff hn).2 h) (p ^ k),
            },
          },
          replace h : q^n ∣ a.gcd b := nat.dvd_gcd k1 h,
          rw hcop at h,
          rw ← nat.pow_lt_iff_lt_right (nat.prime.two_le hq) at hn,
          ring at hn,
          exact nat_not_dvd_of_pos_of_lt nat.zero_lt_one hn h,
        },
        exact nat.coprime.mul hcop' this,
      },
      rw [← ha1, mul_pow],
      rcases h1' with ⟨ h1a, h1b ⟩ | ⟨ h1a, h1b ⟩,
      { left, rw [h1a, h1b], simp, ring, },
      { right, rw [h1a, h1b], simp, },
    }, {
      let b'' := b/q^n,
      have hb1 : b'' * q^n = b := nat.div_mul_cancel k1,
      have hb''pos : 0 < b'' := by {
        by_contradiction, simp at h, rw h at hb1,
        simp at hb1, linarith only [hb1, hbpos],
      },
      have hcop'' : a.gcd b'' = 1 := nat.coprime.coprime_div_right hcop k1,
      have h1'' : a * b'' = p ^ k * c'' ^ n := by {
        apply mul_left_cancel' (pow_ne_zero n (nat.prime.ne_zero hq)),
        rw [← hb1, ← hc1] at h1,
        calc q ^ n * (a * b'') = a * (b'' * q ^ n) : by ring
        ... = q ^ n * (p ^ k * c'' ^ n) : by { rw [h1, mul_pow], ring, },
      },
      rcases hind a b'' c'' hc2 hapos hb''pos hcop'' h1'' with ⟨ a', b', ha'pos, hb'pos, hcop', h1' ⟩,
      use [a', b'*q],
      use ha'pos,
      use mul_pos hb'pos (nat.prime.pos hq),
      split, {
        have : q.gcd a' = 1 := by {
          cases nat.coprime_or_dvd_of_prime hq a' with h h, { exact h, },
          exfalso,
          replace h : q^n ∣ a := by {
            cases h1' with h1' h1', {
              rw h1'.1, exact dvd_mul_of_dvd_right ((nat.pow_dvd_pow_iff hn).2 h) (p ^ k),
            }, {
              rw [h1'.1, nat.pow_dvd_pow_iff hn], exact h,
            },
          },
          replace h : q^n ∣ a.gcd b := nat.dvd_gcd h k1,
          rw hcop at h,
          rw ← nat.pow_lt_iff_lt_right (nat.prime.two_le hq) at hn,
          ring at hn,
          exact nat_not_dvd_of_pos_of_lt nat.zero_lt_one hn h,
        },
        rw nat.gcd_comm at this,
        exact nat.coprime.mul_right hcop' this,
      },
      rw [← hb1, mul_pow],
      rcases h1' with ⟨ h1a, h1b ⟩ | ⟨ h1a, h1b ⟩,
      { left, rw [h1a, h1b], simp, },
      { right, rw [h1a, h1b], simp, ring, },
    },
  },
  exact key c a b c (by linarith) hapos hbpos hcop h1,
end

lemma int_pow_coprime_prime' {a b c : ℤ} {p n k : ℕ}
(hapos : 0 < a) (hbpos : 0 < b) (hcop : a.gcd b = 1) (hp : nat.prime p) (h1 : a * b = p ^ k * c ^ n)
: ∃ a' b' : ℤ, 0 < a' ∧ 0 < b' ∧ a'.gcd b' = 1
∧ ((a = p ^ k * a' ^ n ∧ b = b' ^ n) ∨ (a = a' ^ n ∧ b = p ^ k * b' ^ n)) :=
begin
  have t1 := mul_pos hapos hbpos,
  rw [h1, mul_pos_iff] at t1,
  rcases t1 with ⟨ t1, t2 ⟩ | ⟨ t1, t2 ⟩, {
    replace h1 : a.nat_abs * b.nat_abs = p ^ k * c.nat_abs ^ n := by {
      zify,
      repeat {rw ← int.abs_eq_nat_abs},
      rw [pow_abs c n, abs_of_pos hapos, abs_of_pos hbpos, abs_of_pos t2],
      exact h1,
    },
    have ta : 0 < a.nat_abs := by { zify, rw [← int.abs_eq_nat_abs, abs_of_pos hapos], exact hapos, },
    have tb : 0 < b.nat_abs := by { zify, rw [← int.abs_eq_nat_abs, abs_of_pos hbpos], exact hbpos, },
    rcases nat_pow_coprime_prime' ta tb hcop hp h1 with ⟨ a', b', ha'pos, hb'pos, hcop', h1' ⟩,
    use [a', b'],
    split, { norm_cast, exact ha'pos, },
    split, { norm_cast, exact hb'pos, },
    use hcop',
    zify at h1',
    repeat {rw ← int.abs_eq_nat_abs at h1'},
    rw [abs_of_pos hapos, abs_of_pos hbpos] at h1',
    exact h1',
  },
  exfalso,
  have t3 := pow_pos (nat.prime.pos hp) k,
  zify at t3,
  linarith only [t1, t3],
end

lemma int_pow_coprime {a b c : ℤ} {n : ℕ}
(hapos : 0 < a) (hbpos : 0 < b) (hcop : a.gcd b = 1) (h1 : a * b = c ^ n)
: ∃ a' b' : ℤ, 0 < a' ∧ 0 < b' ∧ a'.gcd b' = 1 ∧ a = a' ^ n ∧ b = b' ^ n :=
begin
  let p := 2,
  have hp : nat.prime p := nat.prime_two,
  replace h1 : a * b = p ^ 0 * c ^ n := by { rw h1, ring, },
  rcases int_pow_coprime_prime' hapos hbpos hcop hp h1 with ⟨ a', b', ha'pos, hb'pos, hcop', h1' ⟩,
  use [a', b', ha'pos, hb'pos, hcop'],
  simp at h1',
  exact h1',
end

lemma int_pow_coprime_prime {a b c : ℤ} {p n : ℕ}
(hapos : 0 < a) (hbpos : 0 < b) (hcop : a.gcd b = 1) (hp : nat.prime p) (h1 : a * b = p * c ^ n)
: ∃ a' b' : ℤ, 0 < a' ∧ 0 < b' ∧ a'.gcd b' = 1
∧ ((a = p * a' ^ n ∧ b = b' ^ n) ∨ (a = a' ^ n ∧ b = p * b' ^ n)) :=
begin
  replace h1 : a * b = p ^ 1 * c ^ n := by { rw h1, ring, },
  rcases int_pow_coprime_prime' hapos hbpos hcop hp h1 with ⟨ a', b', ha'pos, hb'pos, hcop', h1' ⟩,
  use [a', b', ha'pos, hb'pos, hcop'],
  simp at h1',
  exact h1',
end

lemma pythagorean_triple.coprime_classification_pos {x y z : ℤ}
(hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hpy : x^2+y^2=z^2) (hcop : x.gcd y = 1)
: ∃ (a b : ℤ), 0 < a ∧ 0 < b ∧ b < a
∧ (x = a ^ 2 - b ^ 2 ∧ y = 2 * a * b ∨ x = 2 * a * b ∧ y = a ^ 2 - b ^ 2)
∧ z = a ^ 2 + b ^ 2 ∧ a.gcd b = 1
∧ (a % 2 = 0 ∧ b % 2 = 1 ∨ a % 2 = 1 ∧ b % 2 = 0) :=
begin
  replace hpy : pythagorean_triple x y z := by { unfold pythagorean_triple, ring, exact hpy, },
  rcases pythagorean_triple.coprime_classification.1 ⟨ hpy, hcop ⟩ with ⟨ a, b, t1, t2, t3, t4 ⟩,
  have hab : 0 < a * b := by {
    cases t1 with t1 t1, {
      by_contradiction, push_neg at h,
      replace t1 := t1.2,
      linarith only [h, t1, hypos],
    }, {
      by_contradiction, push_neg at h,
      replace t1 := t1.1,
      linarith only [h, t1, hxpos],
    },
  },
  have hab' : a * b ≠ 0 := by linarith only [hab],
  rw mul_ne_zero_iff at hab',
  set! a' := abs a with ha', clear_value a',
  set! b' := abs b with hb', clear_value b',
  use [a', b'],
  have hapos := abs_pos.2 hab'.1, rw ← ha' at hapos, use hapos,
  have hbpos := abs_pos.2 hab'.2, rw ← hb' at hbpos, use hbpos,
  split, {
    have : b^2<a^2 := by {
      cases t1 with t1 t1, {
        replace t1 := t1.1,
        linarith only [t1, hxpos],
      }, {
        replace t1 := t1.2,
        linarith only [t1, hypos],
      },
    },
    rw [← abs.stupid_sqr a, ← abs.stupid_sqr b, ← ha', ← hb'] at this,
    exact lt_of_pow_lt_pow 2 (calc 0 ≤ a' : by linarith only [hapos]) this,
  },
  split, {
    rwa [ha', hb', abs.stupid_sqr a, abs.stupid_sqr b, mul_assoc, ← abs_mul, abs_of_pos hab, ← mul_assoc],
  },
  split, {
    rw [ha', hb', abs.stupid_sqr a, abs.stupid_sqr b],
    cases t2 with t2 t2, { exact t2, },
    exfalso,
    have t3 := pow_two_pos_of_ne_zero a hab'.1,
    have t4 := pow_two_pos_of_ne_zero b hab'.2,
    linarith only [hzpos, t2, t3, t4],
  },
  split, {
    rwa [ha', hb', ← abs.stupid_gcd, int.gcd_comm, ← abs.stupid_gcd, int.gcd_comm],
  },
  rwa [ha', hb', abs.stupid_mod_two a, abs.stupid_mod_two b],
end
