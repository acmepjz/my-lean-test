import data.int.basic
import data.int.parity
import data.nat.prime
import data.rat.basic
import number_theory.pythagorean_triples
import tests.test157lemmas
import tactic

noncomputable theory

def is_congr_num (n : ℤ) := 0 < n ∧ (∃ x y z : ℚ, x ^ 2 + y ^ 2 = z ^ 2 ∧ x * y / 2 = n)

lemma is_congr_num_iff_xyzZpos (n : ℤ) :
is_congr_num n ↔ 0 < n ∧ (∃ (x y z : ℤ) (m : ℚ), 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < m
∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ (x : ℚ) * y / 2 = n * m ^ 2) :=
begin
  split, {
    rintros ⟨ hn, x, y, z, h1, h2 ⟩,
    split, { exact hn, },
    have hn' : n ≠ 0 := by linarith only [hn],
    cancel_denoms at h2,
    have h2' : x ≠ 0 ∧ y ≠ 0 := by { rw [← mul_ne_zero_iff, h2], field_simp [hn'], },
    have h3 : z ≠ 0 := by {
      by_contradiction,
      push_neg at h,
      have := calc 0 = x^2+y^2 : by { rw [h1, h], ring, }
      ... > 0 : add_pos (pow_two_pos_of_ne_zero x h2'.1) (pow_two_pos_of_ne_zero y h2'.2),
      linarith only [this],
    },
    rcases rat.stupid x with ⟨ x1, x2, x2pos, hx ⟩,
    rcases rat.stupid y with ⟨ y1, y2, y2pos, hy ⟩,
    rcases rat.stupid z with ⟨ z1, z2, z2pos, hz ⟩,
    have x2nz : x2 ≠ 0 := by linarith only [x2pos],
    have y2nz : y2 ≠ 0 := by linarith only [y2pos],
    have z2nz : z2 ≠ 0 := by linarith only [z2pos],
    have x1nz : x1 ≠ 0 := by { have := h2'.1, rw hx at this, field_simp [x2nz] at this, exact this, },
    have y1nz : y1 ≠ 0 := by { have := h2'.2, rw hy at this, field_simp [y2nz] at this, exact this, },
    have z1nz : z1 ≠ 0 := by { have := h3, rw hz at this, field_simp [z2nz] at this, exact this, },
    set! x' := abs x1 * y2 * z2 with hx', clear_value x',
    set! y' := abs y1 * z2 * x2 with hy', clear_value y',
    set! z' := abs z1 * x2 * y2 with hz', clear_value z',
    set! m' := x2 * y2 * z2 with hm', clear_value m',
    use [x', y', z', m'],
    split, { rw hx', exact mul_pos (mul_pos (abs_pos.2 x1nz) y2pos) z2pos, },
    split, { rw hy', exact mul_pos (mul_pos (abs_pos.2 y1nz) z2pos) x2pos, },
    split, { rw hz', exact mul_pos (mul_pos (abs_pos.2 z1nz) x2pos) y2pos, },
    split, { rw hm', norm_cast, exact mul_pos (mul_pos x2pos y2pos) z2pos, },
    split, {
      rw [hx', hy', hz'],
      rw [hx, hy, hz] at h1,
      field_simp [x2nz, y2nz, z2nz] at h1,
      norm_cast at h1,
      ring at h1 ⊢,
      rw [abs.stupid_sqr x1, abs.stupid_sqr y1, abs.stupid_sqr z1, ← h1],
      ring,
    },
    cancel_denoms, norm_cast,
    rw [hx', hy', hm'],
    rw [hx, hy] at h2,
    field_simp [x2nz, y2nz] at h2,
    norm_cast at h2,
    have := calc x1 * y1 = 2 * n * (y2 * x2) : h2
    ... > 0 : mul_pos (by linarith only [hn]) (mul_pos y2pos x2pos),
    replace := abs_of_pos this,
    rw abs_mul at this,
    calc abs x1 * y2 * z2 * (abs y1 * z2 * x2) = abs x1 * abs y1 * y2 * z2 * z2 * x2 : by ring
    ... = 2 * n * (y2 * x2) * y2 * z2 * z2 * x2 : by rw [this, h2]
    ... = 2 * n * (x2 * y2 * z2) ^ 2 : by ring,
  },
  rintros ⟨ hn, x, y, z, m, hx, hy, hz, hm, h1, h2 ⟩,
  split, { exact hn, },
  use [(x:ℚ)/m, (y:ℚ)/m, (z:ℚ)/m],
  replace hm : (m:ℚ) ≠ 0 := by { norm_cast, linarith only [hm], },
  field_simp [hm],
  norm_cast,
  split, { exact h1, },
  field_simp at h2, norm_cast at h2, rw h2, ring,
end

lemma is_congr_num_iff_xyzZpos_coprime (n : ℤ) :
is_congr_num n ↔ 0 < n ∧ (∃ (x y z : ℤ) (m : ℚ), 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < m
∧ x.gcd y = 1 ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ (x : ℚ) * y / 2 = n * m ^ 2) :=
begin
  rw is_congr_num_iff_xyzZpos n,
  split, {
    rintros ⟨ hn, x, y, z, m, hx, hy, hz, hm, h1, h2 ⟩,
    split, { exact hn, },
    let d := ((x.gcd y) : ℤ),
    let x' := x/d,
    let y' := y/d,
    let z' := z/d,
    have tx : x = x' * d := int.eq_mul_of_div_eq_left (int.gcd_dvd_left x y) rfl,
    have ty : y = y' * d := int.eq_mul_of_div_eq_left (int.gcd_dvd_right x y) rfl,
    have tz := dvd_add
      ((int.pow_dvd_pow_iff zero_lt_two).2 (int.gcd_dvd_left x y))
      ((int.pow_dvd_pow_iff zero_lt_two).2 (int.gcd_dvd_right x y)),
    rw [h1, int.pow_dvd_pow_iff zero_lt_two] at tz,
    replace tz : z = z' * d := int.eq_mul_of_div_eq_left tz rfl,
    have hd : 0 < d := by { norm_cast, exact int.gcd_pos_of_non_zero_right x (calc y ≠ 0 : by linarith only [hy]), },
    have t3 := int.gcd_mul_right x' d y',
    rw [← tx, ← ty] at t3,
    simp at t3,
    zify at t3,
    replace t3 := int.eq_one_of_mul_eq_self_left (calc d ≠ 0 : by linarith only [hd]) t3.symm,
    norm_cast at t3,
    use [x', y', z', m/d],
    split, { rw [tx, mul_pos_iff] at hx, cases hx with hx hx, exact hx.1, exfalso, linarith, },
    split, { rw [ty, mul_pos_iff] at hy, cases hy with hy hy, exact hy.1, exfalso, linarith, },
    split, { rw [tz, mul_pos_iff] at hz, cases hz with hz hz, exact hz.1, exfalso, linarith, },
    split, { refine div_pos hm _, norm_cast at ⊢ hd, exact hd, },
    split, { exact t3, },
    split, {
      replace h1 := calc (x'^2+y'^2)*d^2 = (x'*d) ^ 2 + (y'*d) ^ 2 : by ring
      ... = (z'*d) ^ 2 : by rw [← tx, ← ty, ← tz, h1]
      ... = z'^2*d^2 : by ring,
      exact mul_right_cancel' (calc d^2≠0 : by linarith only [pow_pos hd 2]) h1,
    },
    rw [tx, ty] at h2,
    have : (d:ℚ)≠0 := by { norm_cast at ⊢ hd, linarith only [hd], },
    clear_value d,
    field_simp [this] at ⊢ h2,
    rw ← h2, ring,
  },
  rintros ⟨ hn, x, y, z, m, hx, hy, hz, hm, hgcd, h1, h2 ⟩,
  exact ⟨ hn, x, y, z, m, hx, hy, hz, hm, h1, h2 ⟩,
end

lemma is_congr_num_iff_rsQ (n : ℤ) :
is_congr_num n ↔ 0 < n ∧ (∃ r s m : ℚ, m ≠ 0 ∧ r * s * (r + s) * (r - s) = n * m ^ 2) :=
begin
  split, {
    rintros ⟨ h1, x, y, z, h2, h3 ⟩,
    split, { exact h1, },
    replace h1 : n ≠ 0 := by linarith only [h1],
    have t1 : x ≠ 0 ∧ y ≠ 0 := by {
      cancel_denoms at h3,
      have := mul_ne_zero (calc (2 : ℚ) ≠ 0 : by norm_num) (calc (n : ℚ) ≠ 0 : int.cast_ne_zero.mpr h1),
      rw [← h3, mul_ne_zero_iff] at this,
      exact this,
    },
    have t3 : z ≠ 0 := by {
      by_contradiction,
      push_neg at h,
      have := calc 0 = x^2+y^2 : by { rw [h2, h], ring, }
      ... > 0 : add_pos (pow_two_pos_of_ne_zero x t1.1) (pow_two_pos_of_ne_zero y t1.2),
      linarith only [this],
    },
    set! k := y / (x + z) with hk, clear_value k,
    have tk : 1+k^2 ≠ 0 := by linarith only [pow_two_nonneg k],
    have t5 : x + z ≠ 0 := by {
      by_contradiction,
      push_neg at h,
      have := calc y^2 = (x+z)*(z-x) : by { ring, rw ← h2, ring, }
      ... = 0 : by { rw h, ring, },
      have : y = 0 := pow_eq_zero this,
      exact t1.2 this,
    },
    have hk': y = k * (x + z) := by { rw hk, field_simp [t5], },
    have t6 : x = (1-k^2)/(1+k^2)*z := by {
      have := calc 0 = x^2+y^2-z^2 : by { rw h2, ring, }
      ... = (x+z)*((1+k^2)*x-(1-k^2)*z) : by { rw hk', ring, },
      field_simp [t5] at this,
      field_simp [tk],
      linarith only [this],
    },
    have t7 : y = (2*k)/(1+k^2)*z := by {
      rw [hk', t6],
      field_simp [tk],
      ring,
    },
    use [1, k, (1+k^2)/z],
    split, { exact div_ne_zero tk t3, },
    rw [← h3, t6, t7],
    field_simp [t3, tk],
    ring,
  },
  rintros ⟨ h1, r, s, m, h2, h3 ⟩,
  unfold is_congr_num,
  split, { exact h1, },
  use [(r^2-s^2)/m, 2*r*s/m, (r^2+s^2)/m],
  split, { ring, },
  calc (r ^ 2 - s ^ 2) / m * (2 * r * s / m) / 2 = r * s * (r + s) * (r - s) / m ^ 2 : by { field_simp [h2], ring, }
  ... = n * m ^ 2 / m ^ 2 : by rw h3
  ... = n : by field_simp [h2],
end

lemma is_congr_num_iff_ec (n : ℤ) :
is_congr_num n ↔ 0 < n ∧ (∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - n ^ 2 * x) :=
begin
  rw is_congr_num_iff_rsQ,
  split, {
    rintros ⟨ h1, r, s, m, h2, h3 ⟩,
    split, { exact h1, },
    replace h1 : n ≠ 0 := by linarith only [h1],
    have t1 : s ≠ 0 := by {
      by_contradiction, push_neg at h,
      have := calc r * s * (r + s) * (r - s) = n * m ^ 2 : h3
      ... ≠ 0 : mul_ne_zero (calc (n : ℚ) ≠ 0 : int.cast_ne_zero.mpr h1) (pow_ne_zero 2 h2),
      rw h at this,
      simp at this,
      exact this,
    },
    use [n*r/s, n^2*m/s^2],
    split, { field_simp [t1, h1, h2], },
    have t2 : (n : ℚ) = r * s * (r + s) * (r - s) / m ^ 2 := by { field_simp [h2], exact h3.symm, },
    rw t2,
    field_simp [h2, t1],
    ring,
  },
  rintros ⟨ h1, x, y, h2, h3 ⟩,
  split, { exact h1, },
  replace h1 : n ≠ 0 := by linarith only [h1],
  use [x/n, 1, y/n^2],
  split, { exact div_ne_zero h2 (pow_ne_zero 2 (calc (n : ℚ) ≠ 0 : int.cast_ne_zero.mpr h1)), },
  field_simp [h1],
  rw h3,
  ring,
end

example : is_congr_num 5 :=
begin
  unfold is_congr_num,
  split, { norm_num, },
  use [3/2, 20/3, 41/6],
  norm_num,
end

example : is_congr_num 6 :=
begin
  unfold is_congr_num,
  split, { norm_num, },
  use [3, 4, 5],
  norm_num,
end

example : is_congr_num 7 :=
begin
  unfold is_congr_num,
  split, { norm_num, },
  use [35/12, 24/5, 337/60],
  norm_num,
end

-- just slow
/- example : is_congr_num 157 :=
begin
  unfold is_congr_num,
  split, { norm_num, },
  use [411340519227716149383203/21666555693714761309610,
    6803298487826435051217540/411340519227716149383203,
    224403517704336969924557513090674863160948472041/8912332268928859588025535178967163570016480830],
  norm_num,
end -/

def heegner7 := ∀ p : ℕ, nat.prime p → p % 8 = 7 → is_congr_num p

def cnp := ∀ n : ℕ, (n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7) → is_congr_num n

theorem fermat123 (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ (nat.prime n ∧ n % 8 = 3)) : ¬ is_congr_num n :=
begin
  intro h0,
  have hn' : n > 0 := by {
    rcases hn with hn | hn | hn,
    { linarith only [hn], },
    { linarith only [hn], },
    exact nat.prime.pos hn.1,
  },
  have h_infinite_descent : ∀ N : ℕ, ¬ (∃ (x y z : ℤ) (m : ℚ), 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < m
  ∧ x.gcd y = 1 ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ (x : ℚ) * y / 2 = n * m ^ 2 ∧ z ≤ N) := by {
    intro N,
    induction N with N hind, {
      rintros ⟨ x, y, z, m, hxpos, hypos, hzpos, hmpos, h1, h2, h3, h4 ⟩,
      norm_cast at h4,
      linarith only [hzpos, h4],
    },
    rintros ⟨ x, y, z, m', hxpos, hypos, hzpos, hmpos, h1, h2, h3, h4 ⟩,
    rcases pythagorean_triple.coprime_classification_pos hxpos hypos hzpos h2 h1
      with ⟨ a, b, ha, hb, hab, hxy, hz, h12cop, hparity ⟩,
    have h3' : (a:ℚ)*b*(a+b)*(a-b)=(x:ℚ)*y/2 := by {
      rcases hxy with ⟨ t1a, t1b ⟩ | ⟨ t1a, t1b ⟩,
      { rw [t1a, t1b], cancel_denoms, norm_cast, ring, },
      { rw [t1a, t1b], cancel_denoms, norm_cast, ring, },
    },
    rw h3 at h3', norm_cast at h3',
    have : ∃ m : ℤ, m' = m := by {
      sorry,
    },
    cases this with m hm,
    rw hm at hmpos h3 h3',
    norm_cast at hmpos h3',
    clear hm m',
    have key : ∃ r s u v : ℤ, a=r^2 ∧ b=n*s^2 ∧ a+b=u^2 ∧ a-b=v^2 ∧ r%2=1 ∧ s%2=0 := by {
      have h13cop : a.gcd (a+b) = 1 := by { rw gcd_add a b 1 at h12cop, rw ← h12cop, rw add_comm, ring, },
      have h14cop : a.gcd (a-b) = 1 := by { rw [gcd_neg a b, gcd_add a (-b) 1] at h12cop, rw ← h12cop, rw add_comm, ring, },
      have h23cop : b.gcd (a+b) = 1 := by { rw [int.gcd_comm, gcd_add b a 1] at h12cop, rw ← h12cop, ring, },
      have h24cop : b.gcd (a-b) = 1 := by { rw [int.gcd_comm, gcd_add b a (-1)] at h12cop, rw ← h12cop, ring, },
      have h34cop : (a+b).gcd (a-b) = 1 := by sorry,
      have h123cop : (a*b).gcd (a+b) = 1 := by { rw [mul_gcd a b (a+b) h12cop, h13cop, h23cop], ring, },
      have h124cop : (a*b).gcd (a-b) = 1 := by { rw [mul_gcd a b (a-b) h12cop, h14cop, h24cop], ring, },
      -- have h134cop : (a*(a+b)).gcd (a-b) = 1 := by { rw [mul_gcd a (a+b) (a-b) h13cop, h14cop, h34cop], ring, },
      have h1234cop : (a*b*(a+b)).gcd (a-b) = 1 := by { rw [mul_gcd (a*b) (a+b) (a-b) h123cop, h124cop, h34cop], ring, },
      have haplusb : 0 < a + b := by linarith only [ha, hb],
      have haminusb : 0 < a - b := by linarith only [hab],
      have hpos2 := mul_pos ha hb,
      have hpos3 := mul_pos hpos2 haplusb,
      -- have hpos4 := mul_pos hpos3 haminusb,
      cases hn with hn hn, {
        rw hn at h3' ⊢,
        norm_cast at h3' ⊢,
        rw one_mul at h3',
        rcases int_pow_coprime hpos3 haminusb h1234cop h3' with ⟨ a3, v, ha3p, hvp, hab3cop, ha3, hv ⟩,
        rcases int_pow_coprime hpos2 haplusb h123cop ha3 with ⟨ a2, u, ha2p, hup, hab2cop, ha2, hu ⟩,
        rcases int_pow_coprime ha hb h12cop ha2 with ⟨ r, s, hrp, hsp, hab1cop, hr, hs ⟩,
        use [r, s, u, v, hr],
        split, { ring, exact hs, },
        use [hu, hv],
        rcases hparity with ⟨ hpa, hpb ⟩ | ⟨ hpa, hpb ⟩, {
          exfalso,
          rw hr at hpa,
          replace hpa := int_even_sq_mod_4 r ((int_even_iff_sq_even r).2 hpa),
          rw ← hr at hpa,
          rw hs at hpb,
          replace hpb := int_odd_sq_mod_4 s ((int_odd_iff_sq_odd s).2 hpb),
          rw ← hs at hpb,
          apply_fun (λ x : ℤ, x % 4) at hv,
          rw [int.sub_mod, hpa, hpb] at hv,
          cases int_sq_mod_4 v with h h,
          { rw h at hv, norm_num at hv, },
          { rw h at hv, norm_num at hv, },
        }, {
          rw hr at hpa,
          use (int_odd_iff_sq_odd r).2 hpa,
          rw hs at hpb,
          use (int_even_iff_sq_even s).2 hpb,
        },
      },
      have hnp : nat.prime n := by {
        cases hn with hn hn,
        { rw hn, exact nat.prime_two, },
        exact hn.1,
      },
      rcases int_pow_coprime_prime hpos3 haminusb h1234cop hnp h3' with
      ⟨ a3, v, ha3p, hvp, hab3cop, ⟨ ha3, hv ⟩ | ⟨ ha3, hv ⟩ ⟩, {
        rcases int_pow_coprime_prime hpos2 haplusb h123cop hnp ha3 with
        ⟨ a2, u, ha2p, hup, hab2cop, ⟨ ha2, hu ⟩ | ⟨ ha2, hu ⟩ ⟩, {
          rcases int_pow_coprime_prime ha hb h12cop hnp ha2 with
          ⟨ r, s, hrp, hsp, hab1cop, ⟨ hr, hs ⟩ | ⟨ hr, hs ⟩ ⟩, {
            exfalso,
            sorry,
          }, {
            use [r, s, u, v, hr, hs, hu, hv],
            rcases hparity with ⟨ hpa, hpb ⟩ | ⟨ hpa, hpb ⟩, {
              exfalso,
              rw hs at hpb,
              cases hn with hn hn,
              { rw [hn, int.mul_mod] at hpb, simp at hpb, exact hpb, },
              rw hr at hpa,
              replace hpa := int_even_sq_mod_4 r ((int_even_iff_sq_even r).2 hpa),
              rw ← hr at hpa,
              rw [← int.not_even_iff, int.even_mul, not_or_distrib] at hpb,
              replace hpb := int_odd_sq_mod_4 s ((int_odd_iff_sq_odd s).2 (int.not_even_iff.1 hpb.2)),
              replace hn : (n : ℤ) % 4 = 3 := by {
                norm_cast,
                rw [← nat.mod_mod_of_dvd n (calc 4 ∣ 8 : by norm_num), hn.2],
                norm_num,
              },
              apply_fun (λ x : ℤ, x % 4) at hu,
              rw [int.add_mod, hpa, hs, int.mul_mod, hpb, hn] at hu,
              cases int_sq_mod_4 u with h h,
              { rw h at hu, norm_num at hu, },
              { rw h at hu, norm_num at hu, },
            }, {
              rw hr at hpa,
              replace hpa := (int_odd_iff_sq_odd r).2 hpa,
              use hpa,
              cases hn with hn hn, {
                by_contradiction,
                rw int.mod_two_ne_zero at h,
                apply_fun (λ x : ℤ, x % 4) at hu,
                rw [int.add_mod, hr, hs, int.mul_mod, int_odd_sq_mod_4 r hpa, int_odd_sq_mod_4 s h, hn] at hu,
                cases int_sq_mod_4 u with h h,
                { rw h at hu, norm_num at hu, },
                { rw h at hu, norm_num at hu, },
              },
              rw [← int.even_iff, hs, int.even_mul] at hpb,
              replace hn : ¬ even (n : ℤ) := by {
                rw int.not_even_iff,
                norm_cast,
                rw [← nat.mod_mod_of_dvd n (calc 2 ∣ 8 : by norm_num), hn.2],
                norm_num,
              },
              cases hpb with hpb hpb, { exfalso, exact hn hpb, },
              rw [int.even_iff, ← int_even_iff_sq_even s] at hpb,
              exact hpb,
            },
          },
        }, {
          exfalso,
          rcases int_pow_coprime ha hb h12cop ha2 with ⟨ r, s, hrp, hsp, hab1cop, hr, hs ⟩,
          have k1 : (a+b)%4=1 := by {
            rcases hparity with ⟨ hpa, hpb ⟩ | ⟨ hpa, hpb ⟩, {
              rw hr at hpa,
              replace hpa := int_even_sq_mod_4 r ((int_even_iff_sq_even r).2 hpa),
              rw ← hr at hpa,
              rw hs at hpb,
              replace hpb := int_odd_sq_mod_4 s ((int_odd_iff_sq_odd s).2 hpb),
              rw ← hs at hpb,
              rw [int.add_mod, hpa, hpb], norm_num,
            }, {
              rw hr at hpa,
              replace hpa := int_odd_sq_mod_4 r ((int_odd_iff_sq_odd r).2 hpa),
              rw ← hr at hpa,
              rw hs at hpb,
              replace hpb := int_even_sq_mod_4 s ((int_even_iff_sq_even s).2 hpb),
              rw ← hs at hpb,
              rw [int.add_mod, hpa, hpb], norm_num,
            },
          },
          rw [hu, int.mul_mod] at k1,
          cases int_sq_mod_4 u with k2 k2, {
            rw k2 at k1, norm_num at k1, exact k1,
          },
          cases hn with hn hn, {
            rw [k2, hn] at k1, norm_num at k1,
          },
          replace hn : (n : ℤ) % 4 = 3 := by {
            norm_cast,
            rw [← nat.mod_mod_of_dvd n (calc 4 ∣ 8 : by norm_num), hn.2],
            norm_num,
          },
          rw [k2, hn] at k1, norm_num at k1,
        },
      }, {
        exfalso,
        rcases int_pow_coprime hpos2 haplusb h123cop ha3 with ⟨ a2, u, ha2p, hup, hab2cop, ha2, hu ⟩,
        rcases int_pow_coprime ha hb h12cop ha2 with ⟨ r, s, hrp, hsp, hab1cop, hr, hs ⟩,
        sorry,
      },
    },
    rcases key with ⟨ r, s, u, v, hr, hs, hu, hv, hpa, hpb ⟩,
    clear hparity,
    set! x' := (u-v)/2 with hx', clear_value x',
    replace hx' : x'*2=u-v := by {
      rw hx',
      have : (u-v)%2=0 := by {
        have t1 := calc 2*(a-u*v) = (a+b)+(a-b)-2*u*v : by ring
        ... = u^2+v^2-2*u*v : by rw [hu, hv]
        ... = (u-v)^2 : by ring,
        have t2 : (2*(a-u*v))%2=0 := int.mul_mod_right 2 (a-u*v),
        rw [← int.even_iff, t1, int.even_pow, int.even_iff] at t2,
        exact t2.1,
      },
      exact int.div_mul_cancel_of_mod_eq_zero this,
    },
    set! y' := x'+v with hy', clear_value y',
    replace hy' := calc y'*2=(x'+v)*2 : by rw hy'
    ... = x'*2+v*2 : by ring
    ... = (u-v)+v*2 : by rw hx'
    ... = u+v : by ring,
    have hbxy := calc b*2=(a+b)-(a-b) : by ring
    ... = (u+v)*(u-v) : by { rw [hu, hv], ring, }
    ... = x'*y'*2*2 : by { rw [← hx', ← hy'], ring, },
    rw mul_left_inj' (calc (2:ℤ) ≠ 0 : by norm_num) at hbxy,
    set! s' := s/2 with hs', clear_value s',
    replace hs' : s'*2=s := by { rw hs', exact int.div_mul_cancel_of_mod_eq_zero hpb, },
    have hpy := calc 4*(x'^2+y'^2) = (x'*2)^2+(y'*2)^2 : by ring
    ... = 2*u^2 + 2*v^2 : by { rw [hx', hy'], ring, }
    ... = 4*(r^2) : by { rw [← hu, ← hv, hr], ring, },
    rw mul_right_inj' (calc (4 : ℤ) ≠ 0 : by norm_num) at hpy,
    have hcoprime : x'.gcd y' = 1 := by {
      sorry,
    },
    apply hind,
    use [x', y', r, s'],
    split, { exact hpy, },
    split, { exact hcoprime, },
    sorry,
  },
  rw is_congr_num_iff_xyzZpos_coprime n at h0,
  replace h0 := h0.2,
  rcases h0 with ⟨ x, y, z, m, hxpos, hypos, hzpos, hmpos, h1, h2, h3 ⟩,
  set! N := z with hN, clear_value N,
  lift N to ℕ using (calc N ≥ 0 : by linarith only [hzpos, hN]),
  apply h_infinite_descent N,
  use [x, y, z, m],
  replace hN : z ≤ (N : ℤ) := by linarith only [hN],
  exact ⟨ hxpos, hypos, hzpos, hmpos, h1, h2, h3, hN ⟩,
end
