import data.real.basic
import analysis.special_functions.exp_log
import analysis.special_functions.pow
import analysis.calculus.deriv
import algebra.group.pi

noncomputable theory

/-
Problem:
Let a,b,t∈ℝ be positive such that a≠b, a=tb^3, and a^a=b^b.
(1) If t=4, prove that 1/e+4/e^3 < a+b < 1.
(2) Let a,b,t be such that a+b>2/sqrt(t). View a,b as functions of t and denote g(t)=a+b.
  Compute the range of t and prove that g(t) increases as t increases.

Human readable proof:
Let y=f(x)=x log x for x>0, then f(x)<0 when x<1, f(x)=0 when x=1,
f(x)>0 when x>1.
We have f'(x)=1+log x, and
f'(x)<0 when x<1/e, f'(x)>0 when x>1/e.
Therefore f(x) decreases as x increases if x∈(0,1/e),
f(x) increases as x increases if x∈(1/e, +∞),
and f(x) takes minimun at x=1/e with value -1/e.
Therefore if a≠b such that a^a=b^b, then f(a)=f(b)=:y, we must have
y∈(-1/e,0), a,b∈(0,1/e)∪(1/e,1), and
- b decreases and t increases as a increases,
- either a∈(0,1/e),b∈(1/e,1),t∈(0,e^2), or a∈(1/e,1),b∈(0,1/e),t∈(e^2,+∞).
- If a > b, then 1/sqrt(t)=sqrt(b^3/a) < sqrt(b^3/b)=b and hence a+b > 2b > 2/sqrt(t).
- If a < b, then 1/sqrt(t)=sqrt(b^3/a) > sqrt(b^3/b)=b and hence a+b < 2b < 2/sqrt(t).
Therefore the (1) comes from that since t=4 < e^2, we have a < 1/e < b,
hence a+b < 2/sqrt(t)=1 and a+b=tb^3+b>t/e^3+1/e=1/e+4/e^3.
In (2), the range of t is (e^2,+∞). Since t increases as a increases, we only need to show that
g increases as a increases, namely d(a+b)/da>0. We have
d(a+b)/da=1+db/da=1+(dy/da)/(dy/db)=1+(1+log a)/(1+log b). Since 1+log b<0, we only need to show
log b+log a+2<0, namely ab<1/e^2, namely b<1/ae^2. Since b<1/e and 1/ae^2<1/e, this is equivalent to
f(b)>f(1/ae^2), namely a log a > 1/ae^2 * (-2-log a), note that f(a)=f(b).
This is equivalent to g(x)>0 for x∈(1/e,1),
where g(x)=(x+1/xe^2)log x + 2/xe^2. Since g(1/e)=0, we only need to show that
g'(x)>0 for x∈(1/e,1). This is true since
g'(x)= ... = (1-1/x^2e^2)(1+log x).

Please translate it into a machine readable proof.
-/

def condition {a b t : ℝ} (ha : a > 0) (hb : b > 0) (ht : t > 0) := a ≠ b ∧ a = t * b ^ 3 ∧ a ^ a = b ^ b

def e : ℝ := real.exp 1

lemma e_gt_one : e > 1 :=
begin
  change 1 < e,
  unfold e,
  rw real.one_lt_exp_iff,
  linarith,
end

lemma e_gt_two : e > 2 :=
begin
  unfold e,
  have key := real.exp_approx_end 2 3 1 (by norm_num) (by norm_num),
  norm_num at key,
  rw abs_le at key,
  linarith,
end

lemma einv_lt_one : 1/e < 1 := by { rw one_div e, exact inv_lt_one e_gt_one, }

def xlogx (x : ℝ) : ℝ := x * real.log x

lemma eq1_iff_eq2 {a b : ℝ} (ha : a > 0) (hb : b > 0) : a ^ a = b ^ b ↔ xlogx a = xlogx b :=
begin
  unfold xlogx,
  split, {
    intro h,
    rw [← real.log_rpow ha a, ← real.log_rpow hb b, h],
  }, {
    intro h,
    rw [← real.log_rpow ha a, ← real.log_rpow hb b] at h,
    have h2 : real.exp (real.log (a ^ a)) = real.exp (real.log (b ^ b)) := by rw h,
    rw [real.exp_log (real.rpow_pos_of_pos ha a), real.exp_log (real.rpow_pos_of_pos hb b)] at h2,
    exact h2,
  },
end

lemma xlogx_pos_iff {x : ℝ} (hx : x > 0)
: xlogx x > 0 ↔ x > 1 :=
begin
  unfold xlogx,
  split, {
    intro h,
    exact (real.log_pos_iff hx).mp ((zero_lt_mul_left hx).mp h),
  }, {
    intro h,
    exact mul_pos hx (real.log_pos h),
  },
end

lemma xlogx_neg_iff {x : ℝ} (hx : x > 0)
: xlogx x < 0 ↔ x < 1 :=
begin
  unfold xlogx,
  split, {
    intro h,
    have h1 : x * (-real.log x) > 0 := by linarith,
    have h2 : (-real.log x) > 0 := (zero_lt_mul_left hx).mp h1,
    have h3 : real.log x < 0 := by linarith,
    exact (real.log_neg_iff hx).mp h3,
  }, {
    intro h,
    have h1 := real.log_neg hx h,
    have h2 : (-real.log x) > 0 := by linarith,
    have h3 : x * (-real.log x) > 0 := mul_pos hx h2,
    linarith,
  },
end

lemma xlogx_zero_iff {x : ℝ} (hx : x > 0)
: xlogx x = 0 ↔ x = 1 :=
begin
  unfold xlogx,
  split, {
    intro h,
    have h1 : x ≠ 0 := by linarith,
    have h2 : real.log x = 0 := by { rw mul_eq_zero at h, tauto },
    symmetry,
    calc 1 = real.exp 0 : real.exp_zero.symm
      ... = real.exp (real.log x) : by rw ← h2
      ... = x : real.exp_log (by linarith),
  }, {
    intro h,
    rw [h, real.log_one],
    ring,
  },
end

lemma xlogx_cont : continuous_on (λ u : ℝ, xlogx u) (set.Ioi 0) :=
begin
  refine continuous_on.mul continuous_on_id _,
  intros u hu,
  exact continuous_at.continuous_within_at (real.continuous_at_log hu),
end

lemma xlogx_diff_on : differentiable_on ℝ (λ u : ℝ, xlogx u) (set.Ioi 0) :=
begin
  refine differentiable_on.mul differentiable_on_id (differentiable_on_id.log _),
  intros u hu,
  have : u > 0 := hu, rw id, linarith,
end

lemma xlogx_has_deriv_at {u : ℝ} (hu : u > 0)
: has_deriv_at (λ u : ℝ, xlogx u) (1 + real.log u) u :=
begin
  have d0 := has_deriv_at_id' u,
  have d2 : u ≠ 0 := by linarith,
  have d1 := real.has_deriv_at_log d2,
  have d3 := has_deriv_at.mul d0 d1,
  have d4 : u * u⁻¹ = 1 := div_self d2,
  rw [d4, add_comm] at d3,
  simp at d3,
  exact d3,
end

lemma xlogx_mvt {a b : ℝ} (ha : a > 0) (hab: a < b)
: ∃ (c : ℝ), a < c ∧ c < b ∧ 1 + real.log c = (xlogx b - xlogx a) / (b - a) :=
begin
  have hb : b > 0 := by linarith,
  have c0 : (set.Icc a b) ⊆ (set.Ioi 0) := (set.Ioi 0).Icc_subset ha hb,
  have c1 : continuous_on (λ u : ℝ, xlogx u) (set.Icc a b) := continuous_on.mono xlogx_cont c0,
  have c2 : (set.Ioo a b) ⊆ (set.Ioo 0 b) := set.Ioo_subset_Ioo (by linarith) (by linarith),
  have c3 : (set.Ioo a b) ⊆ (set.Ioi 0) := set.subset.trans c2 set.Ioo_subset_Ioi_self,
  have c4 : differentiable_on ℝ (λ u : ℝ, xlogx u) (set.Ioo a b) := differentiable_on.mono xlogx_diff_on c3,
  
  have mvt1 := exists_deriv_eq_slope xlogx hab c1 c4,
  cases mvt1 with c mvt2,
  cases mvt2 with H mvt3,
  use c,
  rw ← set.Ioo_def at H,
  have z1 : a < c := H.1,
  have z2 : c < b := H.2,
  have z4 := xlogx_has_deriv_at (calc c > 0 : by linarith),
  have z3 : deriv xlogx c = 1 + real.log c := has_deriv_at.deriv z4,
  rw z3 at mvt3,
  exact ⟨ z1, z2, mvt3 ⟩,
end

lemma log_einv_eq_minus_one : real.log (1/e) = -1 := calc
  real.log (1/e) = real.log (e⁻¹) : by { rw one_div e }
  ... = -real.log e : e.log_inv
  ... = -1 : by { congr, exact real.log_exp 1 }

lemma xlogx_monotone {x y : ℝ} (hx : x > 0) (hy : y > 0)
: (1/e ≤ x → x < y → xlogx x < xlogx y) ∧ (1/e ≥ x → x > y → xlogx x < xlogx y) :=
begin
  split, {
    intros h1 h2,
    cases xlogx_mvt hx h2 with c mvt1,
    have d1 : c > 1/e := by linarith,
    have d2 : real.log c > -1 := by { rw ← log_einv_eq_minus_one, exact real.log_lt_log (one_div_pos.mpr (1 : ℝ).exp_pos) d1 },
    have d3 : xlogx y - xlogx x > 0 := calc
      xlogx y - xlogx x = (1 + real.log c) * (y - x) : by { have : y - x ≠ 0 := by linarith, rw ← div_eq_iff this, rw mvt1.2.2 }
      ... > 0 : by { have d4 : 0 < 1 + real.log c := by linarith, have d5 : 0 < y - x := by linarith, exact mul_pos d4 d5 },
    linarith,
  }, {
    intros h1 h2,
    cases xlogx_mvt hy h2 with c mvt1,
    have d1 : c < 1/e := by linarith,
    have d2 : real.log c < -1 := by { rw ← log_einv_eq_minus_one, exact real.log_lt_log (by linarith) d1 },
    have d3 : xlogx x - xlogx y < 0 := calc
      xlogx x - xlogx y = (1 + real.log c) * (x - y) : by { have : x - y ≠ 0 := by linarith, rw ← div_eq_iff this, rw mvt1.2.2 }
      ... < 0 : by { have d4 : 0 < -(1 + real.log c) := by linarith, have d5 : 0 < x - y := by linarith, have d6 := mul_pos d4 d5, linarith },
    linarith,
  },
end

lemma xlogx_inj {x y : ℝ} (hx : x > 0) (hy : y > 0)
: (1/e ≤ x → 1/e ≤ y → (x = y ↔ xlogx x = xlogx y)) ∧ (1/e ≥ x → 1/e ≥ y → (x = y ↔ xlogx x = xlogx y)) :=
begin
  split, {
    intros hxx hyy,
    split, { intro hxy, rw hxy, },
    intro hxy,
    by_contradiction,
    have d0 : x ≠ y := h,
    by_cases hxy2 : x < y, {
      linarith [(xlogx_monotone hx hy).1 hxx hxy2],
    }, {
      have d1 : y < x := (ne.le_iff_lt d0.symm).mp (by linarith),
      linarith [(xlogx_monotone hy hx).1 hyy d1],
    },
  }, {
    intros hxx hyy,
    split, { intro hxy, rw hxy, },
    intro hxy,
    by_contradiction,
    have d0 : x ≠ y := h,
    by_cases hxy2 : x < y, {
      linarith [(xlogx_monotone hy hx).2 hyy hxy2],
    }, {
      have d1 : y < x := (ne.le_iff_lt d0.symm).mp (by linarith),
      linarith [(xlogx_monotone hx hy).2 hxx d1],
    },
  },
end

lemma xlogx_monotone_iff {x y : ℝ} (hx : x > 0) (hy : y > 0)
: (1/e ≤ x → 1/e ≤ y → (x < y ↔ xlogx x < xlogx y)) ∧ (1/e ≥ x → 1/e ≥ y → (x > y ↔ xlogx x < xlogx y)) :=
begin
  split, {
    intros hxx hyy,
    split, { exact (xlogx_monotone hx hy).1 hxx, },
    contrapose, push_neg, intro hxy,
    by_cases hxy2 : y = x, { rw hxy2, },
    have := (xlogx_monotone hy hx).1 hyy ((ne.le_iff_lt hxy2).mp hxy),
    linarith,
  }, {
    intros hxx hyy,
    split, { exact (xlogx_monotone hx hy).2 hxx, },
    contrapose, push_neg, intro hxy,
    by_cases hxy2 : x = y, { rw hxy2, },
    have := (xlogx_monotone hy hx).2 hyy ((ne.le_iff_lt hxy2).mp hxy),
    linarith,
  },
end

lemma range_of_a {a b : ℝ} (ha : a > 0) (hb : b > 0) (h1 : a ≠ b) (h2 : a ^ a = b ^ b)
: a < 1 ∧ a ≠ 1/e :=
begin
  rw eq1_iff_eq2 ha hb at h2,
  split, {
    have e1 := einv_lt_one,
    by_cases b1 : b ≥ 1, {
      by_contradiction,
      have a1 : a ≥ 1 := by linarith,
      rw ← (xlogx_inj ha hb).1 (by linarith) (by linarith) at h2,
      contradiction,
    }, {
      have b2 : xlogx b < 0 := (xlogx_neg_iff hb).2 (by linarith),
      rw ← h2 at b2,
      exact (xlogx_neg_iff ha).1 b2,
    },
  }, {
    by_contradiction,
    have hh : a = 1/e := by finish,
    by_cases h1a : a > b, {
      linarith [(xlogx_monotone ha hb).2 (by linarith) h1a],
    }, {
      have d0 : a < b := (ne.le_iff_lt h1).mp (by linarith),
      linarith [(xlogx_monotone ha hb).1 (by linarith) d0],
    },
  },
end

lemma range_of_a_b {a b : ℝ} (ha : a > 0) (hb : b > 0) (h1 : a ≠ b) (h2 : a ^ a = b ^ b)
: (a < 1/e ∧ b > 1/e ∧ b < 1)
∨ (a > 1/e ∧ a < 1 ∧ b < 1/e) :=
begin
  have haa := range_of_a ha hb h1 h2,
  have hbb := range_of_a hb ha h1.symm h2.symm,
  rw eq1_iff_eq2 ha hb at h2,
  by_cases ha2 : a < 1/e, {
    left,
    have r2 : b > 1/e := by {
      by_contradiction,
      rw ← (xlogx_inj ha hb).2 (by linarith) (by linarith) at h2,
      contradiction,
    },
    exact ⟨ ha2, r2, hbb.1 ⟩,
  }, {
    right,
    have ha2b : a > 1/e := (ne.le_iff_lt haa.2.symm).mp (by linarith),
    have r2 : b < 1/e := by {
      by_contradiction,
      rw ← (xlogx_inj ha hb).1 (by linarith) (by linarith) at h2,
      contradiction,
    },
    exact ⟨ ha2b, haa.1, r2 ⟩,
  },
end

lemma range_of_a_b_t {a b t : ℝ} (ha : a > 0) (hb : b > 0) (ht : t > 0) (h1 : condition ha hb ht)
: (a < 1/e ∧ b > 1/e ∧ b < 1 ∧ t < e^2 ∧ b < 1 / (real.sqrt t))
∨ (a > 1/e ∧ a < 1 ∧ b < 1/e ∧ t > e^2 ∧ b > 1 / (real.sqrt t)) :=
begin
  unfold condition at h1,
  have h121b : t = a / b^3 := by {
    symmetry,
    have : b^3 ≠ 0 := pow_ne_zero 3 (by linarith),
    rw div_eq_iff this, exact h1.2.1,
  },
  have stupid : (1/e) / (1/e)^3 = e^2 := by {
    rw one_div_pow 3,
    have t2 : e ≠ 0 := by linarith [e_gt_one],
    have t3 : e^3 ≠ 0 := pow_ne_zero 3 t2,
    have t1 : 1/e^3 ≠ 0 := one_div_ne_zero t3,
    rw [div_eq_iff t1, div_eq_iff t2], ring,
    symmetry, rw mul_comm, exact div_self t3,
  },
  cases range_of_a_b ha hb h1.1 h1.2.2 with ha2 ha2, {
    left,
    have r4 : t < e^2 := calc
      t = a / b^3 : h121b
      ... < (1/e) / (1/e)^3 : by {
        have t2 : (1/e)^3 < b^3 := pow_lt_pow_of_lt_left ha2.2.1 (by linarith) (by linarith),
        have t3 : (1/e)^3 ≤ b^3 := by linarith,
        exact div_lt_div ha2.1 t3 (by linarith) (pow_pos (by linarith) 3),
      }
      ... = e^2 : stupid,
    have r5 : 1 / real.sqrt t > b := by {
      ring,
      rw ← real.sqrt_inv,
      refine lt_of_pow_lt_pow 2 (by linarith [real.sqrt_pos.2 (inv_pos.2 ht)]) _,
      rw real.sqr_sqrt (calc 0 ≤ t⁻¹ : by linarith [inv_pos.2 ht]),
      rw [h121b, inv_div, lt_div_iff ha],
      have := mul_lt_mul_of_pos_left (calc a < b : by linarith) (pow_pos hb 2),
      have : b^2 * b = b^3 := by ring,
      linarith,
    },
    exact ⟨ ha2.1, ha2.2.1, ha2.2.2, r4, r5 ⟩,
  }, {
    right,
    have r4 : t > e^2 := calc
      t = a / b^3 : h121b
      ... > (1/e) / (1/e)^3 : by {
        have t2 : b^3 < (1/e)^3 := pow_lt_pow_of_lt_left ha2.2.2 (by linarith) (by linarith),
        have t3 : b^3 ≤ (1/e)^3 := by linarith,
        exact div_lt_div ha2.1 t3 (by linarith) (pow_pos hb 3),
      }
      ... = e^2 : stupid,
    have r5 : 1 / real.sqrt t < b := by {
      ring,
      rw ← real.sqrt_inv,
      refine lt_of_pow_lt_pow 2 (by linarith [real.sqrt_pos.2 (inv_pos.2 ht)]) _,
      rw real.sqr_sqrt (calc 0 ≤ t⁻¹ : by linarith [inv_pos.2 ht]),
      rw [h121b, inv_div, div_lt_iff ha],
      have := mul_lt_mul_of_pos_left (calc b < a : by linarith) (pow_pos hb 2),
      have : b^2 * b = b^3 := by ring,
      linarith,
    },
    exact ⟨ ha2.1, ha2.2.1, ha2.2.2, r4, r5 ⟩,
  },
end

lemma stupid_log_pow {x : ℝ} (hx : x ≠ 0) (n : ℕ) : real.log (x^n) = n * real.log x :=
begin
  induction n with n hn,
  simp,
  rw pow_succ,
  rw [real.log_mul hx (pow_ne_zero n hx), hn, nat.succ_eq_add_one],
  ring,
  rw mul_comm,
  refl,
end

lemma range_of_a_times_b_0 {a b : ℝ} (ha : a > 0) (hb : b > 0) (h1 : a ≠ b) (h2 : a ^ a = b ^ b)
(haa : a > 1/e) : a * b < 1/e^2 :=
begin
  cases range_of_a_b ha hb h1 h2 with hh hh, {
    exfalso, linarith,
  }, {
    have rab : a > 1/e ∧ a < 1 ∧ b < 1/e
      := by { cases range_of_a_b ha hb h1 h2 with hh hh, { exfalso, linarith }, exact hh, },
    rw eq1_iff_eq2 ha hb at h2,
    suffices : 1/(a*e^2) > b, {
      have := mul_lt_mul_of_pos_right this (calc a > 0 : by linarith),
      rw [div_helper (e^2) (calc a ≠ 0 : by linarith), mul_comm] at this,
      exact this,
    },
    have t1 : 0 < 1/(a*e^2) := by {
      rw [one_div, inv_pos],
      exact mul_pos (by linarith) (pow_pos (by linarith only [e_gt_one]) 2),
    },
    have e_ne_zero : e ≠ 0 := by linarith only [e_gt_one],
    rw (xlogx_monotone_iff (calc 1/(a*e^2) > 0 : by linarith only [t1]) hb).2 (calc 1/e ≥ 1/(a*e^2) : by {
      change 1/(a*e^2) ≤ 1/e,
      repeat {rw one_div},
      refine (inv_le_inv _ _).2 _,
      { exact mul_pos (by linarith) (pow_pos (by linarith only [e_gt_one]) 2), },
      { linarith only [e_gt_one], },
      calc e = (1/e) * e^2 : by { rw [← mul_div_right_comm, eq_div_iff e_ne_zero], ring, }
      ... ≤ a * e^2 : mul_le_mul_of_nonneg_right (calc 1/e ≤ a : by linarith only [haa]) (pow_nonneg (calc e ≥ 0 : by linarith only [e_gt_one]) 2),
    }) (by linarith),
    rw ← h2,
    unfold xlogx,
    rw [one_div, real.log_inv],
    rw real.log_mul (calc a ≠ 0 : by linarith only [ha]) (pow_ne_zero 2 e_ne_zero),
    rw (calc real.log (e^2) = 2 : by {
      rw stupid_log_pow e_ne_zero 2,
      unfold e,
      rw real.log_exp (1 : ℝ),
      simp,
    }),
    suffices : 0 < (a + (a * e ^ 2)⁻¹) * real.log a + 2 * (a * e ^ 2)⁻¹, {
      rw add_mul at this,
      rw [← neg_mul_comm, mul_add],
      linarith,
    },
    let g := λ (x : ℝ), (x + (x * e ^ 2)⁻¹) * real.log x + 2 * (x * e ^ 2)⁻¹,
    have g_has_deriv_at : ∀ (u : ℝ), u > 0 → (has_deriv_at g ((1 - (u^2 * e^2)⁻¹) * (1 + real.log u)) u) := by {
      intros u hu,
      have d0 : u ≠ 0 := by linarith only [hu],
      have d1 := real.has_deriv_at_log d0,
      have d2 := has_deriv_at_inv d0,
      have d3 := has_deriv_at.const_mul (e^2) d2,
      sorry,
    },
    sorry,
  },
end

lemma range_of_a_times_b {a b : ℝ} (ha : a > 0) (hb : b > 0) (h1 : a ≠ b) (h2 : a ^ a = b ^ b)
: a * b < 1/e^2 :=
begin
  cases range_of_a_b ha hb h1 h2 with hh hh, {
    rw mul_comm,
    exact range_of_a_times_b_0 hb ha h1.symm h2.symm hh.2.1,
  }, {
    exact range_of_a_times_b_0 ha hb h1 h2 hh.1,
  },
end

theorem prob1 {a b t : ℝ} (ha : a > 0) (hb : b > 0) (ht : t > 0) (h1 : condition ha hb ht) (h2 : t = 4)
: 1/e + 4/e^3 < a + b ∧ a + b < 1 :=
begin
  have esq_gt_four : e^2 > 4 := calc
    e^2 > 2^2 : pow_lt_pow_of_lt_left e_gt_two (by linarith) (by linarith)
    ... = 4 : by ring,
  cases range_of_a_b_t ha hb ht h1 with hh hh, {
    unfold condition at h1,
    split, {
      calc a + b = 4*b^3 + b : by rw [h1.2.1, h2]
      ... > 1/e + 4/e^3 : by {
        have t1 : b^3 > (1/e)^3 := pow_lt_pow_of_lt_left hh.2.1 (by linarith) (by linarith),
        rw one_div_pow 3 at t1,
        have : 4*b^3 > 4*(1/e^3) := by linarith,
        have : 4*(1/e^3) = 4/e^3 := by ring,
        linarith,
      },
    }, {
      have : 1 / real.sqrt t = 1 / 2 := by {
        have : real.sqrt (2*2) = 2 := real.sqrt_mul_self (by linarith),
        ring at this,
        rw [h2, this],
      },
      linarith,
    },
  }, {
    exfalso,
    linarith,
  },
end

theorem prob2a {a b t : ℝ} (ha : a > 0) (hb : b > 0) (ht : t > 0) (h1 : condition ha hb ht)
(h2 : a + b > 2 / real.sqrt t)
: t > e^2 :=
begin
  cases range_of_a_b_t ha hb ht h1 with hh hh, {
    exfalso,
    have := calc
      a + b < 2 * b : by linarith
      ... < 2 * (1 / real.sqrt t) : by linarith
      ... = 2 / real.sqrt t : by ring,
    linarith,
  }, {
    exact hh.2.2.2.1,
  },
end

theorem prob2b {t : ℝ} (hte2 : t > e^2) : ∃ a b : ℝ,
∃ (ha : a > 0), ∃ (hb : b > 0), ∃ (ht : t > 0), (condition ha hb ht) ∧ (a + b > 2 / real.sqrt t) :=
begin
  have xlogx_surj_1 : ∀ y : ℝ, y < 0 → y > -1/e
  → ∃ x : ℝ, x > 0 ∧ x < 1/e ∧ y = xlogx x := by {
    intros y hy0 hy,
    sorry,
  },
  have xlogx_surj_2 : ∀ y : ℝ, y ≥ -1/e
  → ∃ x : ℝ, x > 1/e ∧ y = xlogx x := by {
    intros y hy,
    sorry,
  },
  sorry,
  -- intermediate_value_Icc
end

theorem prob2c {a b t a' b' t' : ℝ} (ha : a > 0) (hb : b > 0) (ht : t > 0) (h1 : condition ha hb ht)
(h2 : a + b > 2 / real.sqrt t) (ha' : a' > 0) (hb' : b' > 0) (ht' : t' > 0) (h1' : condition ha' hb' ht')
(h2' : a' + b' > 2 / real.sqrt t') (htt : t < t') : a + b < a' + b' :=
begin
  have hte2 := prob2a ha hb ht h1 h2,
  have hte2' := prob2a ha' hb' ht' h1' h2',
  have rabt : a > 1/e ∧ a < 1 ∧ b < 1/e ∧ t > e^2 ∧ b > 1 / (real.sqrt t)
    := by { cases range_of_a_b_t ha hb ht h1 with hh hh, { exfalso, linarith }, exact hh, },
  have rabt' : a' > 1/e ∧ a' < 1 ∧ b' < 1/e ∧ t' > e^2 ∧ b' > 1 / (real.sqrt t')
    := by { cases range_of_a_b_t ha' hb' ht' h1' with hh hh, { exfalso, linarith }, exact hh, },
  unfold condition at h1 h1',
  rw eq1_iff_eq2 ha hb at h1,
  rw eq1_iff_eq2 ha' hb' at h1',
  have haa : a < a' := by {
    by_contradiction,
    push_neg at h,
    by_cases aeq : a' = a, {
      have beq := by calc
        xlogx b' = xlogx a' : h1'.2.2.symm
        ... = xlogx a : by rw aeq
        ... = xlogx b : h1.2.2,
      rw ← (xlogx_inj hb' hb).2 (by linarith) (by linarith) at beq,
      rw [h1.2.1, h1'.2.1, beq] at aeq,
      have : t' = t := (mul_left_inj' (calc b^3 ≠ 0 : pow_ne_zero 3 (by linarith))).mp aeq,
      linarith,
    }, {
      rw ne.le_iff_lt aeq at h,
      have hbb := (xlogx_monotone ha' ha).1 (by linarith) h,
      rw [h1.2.2, h1'.2.2] at hbb,
      rw ← (xlogx_monotone_iff hb' hb).2 (by linarith) (by linarith) at hbb,
      have : b ^ 3 < b' ^ 3 := pow_lt_pow_of_lt_left hbb (by linarith) (by linarith),
      have := mul_lt_mul htt (calc b ^ 3 ≤ b' ^ 3 : by linarith) (pow_pos hb 3) (by linarith),
      rw [h1.2.1, h1'.2.1] at h,
      linarith,
    },
  },
  have hbb : b > b' := by {
    rw (xlogx_monotone_iff hb hb').2 (by linarith) (by linarith),
    rw [← h1.2.2, ← h1'.2.2],
    exact (xlogx_monotone ha ha').1 (by linarith) haa,
  },
  rcases xlogx_mvt ha haa with ⟨ c, ⟨ hc1, hc2, mvt ⟩ ⟩,
  rcases xlogx_mvt hb' hbb with ⟨ c', ⟨ hc1', hc2', mvt' ⟩ ⟩,
  rw [← h1.2.2, ← h1'.2.2] at mvt',
  let A := xlogx a' - xlogx a,
  have AA1 : xlogx a' - xlogx a = A := by refl,
  have AA2 : xlogx a - xlogx a' = -A := by linarith only [AA1],
  have Apos : A > 0 := by linarith[(xlogx_monotone ha ha').1 (by linarith) haa],
  have logc : real.log c > -1 := by {
    rw ← log_einv_eq_minus_one,
    exact real.log_lt_log (one_div_pos.mpr (1 : ℝ).exp_pos) (calc c > 1/e : by linarith),
  },
  have logc' : real.log c' < -1 := by {
    rw ← log_einv_eq_minus_one,
    exact real.log_lt_log (by linarith) (calc c' < 1/e : by linarith),
  },
  have logcB : 1 + real.log c ≠ 0 := by linarith only [logc],
  have logcB' : 1 + real.log c' ≠ 0 := by linarith only [logc'],
  rw [
    AA1, eq_div_iff (calc a' - a ≠ 0 : by linarith only [haa]),
    mul_comm, ← eq_div_iff logcB] at mvt,
  rw [
    AA2, eq_div_iff (calc b - b' ≠ 0 : by linarith only [hbb]),
    mul_comm, ← eq_div_iff logcB'] at mvt',
  have key := calc
    (a' + b') - (a + b) = (a' - a) - (b - b') : by ring
    ... = A / (1 + real.log c) + A / (1 + real.log c') : by { rw [mvt, mvt'], ring }
    ... = (A * (1 + real.log c') + (1 + real.log c) * A) / ((1 + real.log c) * (1 + real.log c')) : div_add_div A A logcB logcB'
    ... = (A * (2 + real.log c + real.log c')) / ((1 + real.log c) * (1 + real.log c')) : by { congr, ring, }
    ... > 0 : by {
      have d1 : (1 + real.log c) * (1 + real.log c') < 0 := mul_neg_of_pos_of_neg (by linarith only [logc]) (by linarith only [logc']),
      have d2 : 2 + real.log c + real.log c' < 0 := by sorry, -- incorrect !!!
      have d3 : A * (2 + real.log c + real.log c') < 0 := mul_neg_of_pos_of_neg Apos d2,
      change 0 < (A * (2 + real.log c + real.log c')) / ((1 + real.log c) * (1 + real.log c')),
      rw div_pos_iff, right, exact ⟨ d3, d1 ⟩,
    },
  linarith only [key],
end
