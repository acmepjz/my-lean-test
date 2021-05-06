import data.nat.basic
import data.nat.prime
import data.rat.basic
import algebra.field
import algebra.char_zero
import algebra.char_p
import tactic

lemma char_is_prime_or_zero'
(R : Type*) [semiring R] [no_zero_divisors R] [nontrivial R]
: nat.prime (ring_char R) ∨ ring_char R = 0 :=
begin
  set p := ring_char R with h,
  rw ring_char.eq_iff at h,
  exact char_p.char_is_prime_or_zero R p,
end

example : char_zero ℚ :=
begin
  exact char_p.char_p_to_char_zero ℚ,
end

example : ring_char ℚ = 0 :=
begin
  rw ring_char.eq_iff,
  exact char_p.of_char_zero ℚ,
end

lemma prime_neq_char_is_non_zero
(R : Type*) [semiring R] [nontrivial R]
(q : ℕ) (hq : nat.prime q) (hneq : ring_char R ≠ q) : (q : R) ≠ 0 :=
begin
  intro h0,
  replace h0 := ring_char.dvd h0,
  cases (nat.dvd_prime hq).1 h0 with hp' hp', {
    apply (show (1:R) ≠ 0, from one_ne_zero),
    exact_mod_cast (ring_char.spec R 1).2 (by { rw hp', }),
  },
  exact hneq hp',
end

lemma power_of_prime_neq_char_is_non_zero
(R : Type*) [semiring R] [no_zero_divisors R] [nontrivial R]
(n : ℕ) (q : ℕ) (a : ℕ) (hq : nat.prime q) (hn : n = q^a) (hneq : ring_char R ≠ q) : (n : R) ≠ 0 :=
begin
  have h := prime_neq_char_is_non_zero R q hq hneq,
  rw hn,
  field_simp [h],
end

lemma dvd_char_is_zero_N
{R : Type*} [semiring R] {p : ℕ} (hp : ring_char R = p) (n : ℕ) (hdvd : p ∣ n) : (n : R) = 0 :=
begin
  rw ring_char.eq_iff at hp,
  rw @char_p.cast_eq_zero_iff R _ p hp n,
  exact hdvd,
end

lemma dvd_char_is_zero
{R : Type*} [ring R] {p : ℕ} (hp : ring_char R = p) (n : ℤ) (hdvd : (p : ℤ) ∣ n) : (n : R) = 0 :=
begin
  rw ring_char.eq_iff at hp,
  rw @char_p.int_cast_eq_zero_iff R _ p hp n,
  exact hdvd,
end

lemma ndvd_char_is_non_zero_N
{R : Type*} [semiring R] {p : ℕ} (hp : ring_char R = p) (n : ℕ) (hdvd : ¬ p ∣ n) : (n : R) ≠ 0 :=
begin
  rw ring_char.eq_iff at hp,
  rw [ne.def, @char_p.cast_eq_zero_iff R _ p hp n],
  exact hdvd,
end

lemma ndvd_char_is_non_zero
{R : Type*} [ring R] {p : ℕ} (hp : ring_char R = p) (n : ℤ) (hdvd : ¬ (p : ℤ) ∣ n) : (n : R) ≠ 0 :=
begin
  rw ring_char.eq_iff at hp,
  rw [ne.def, @char_p.int_cast_eq_zero_iff R _ p hp n],
  exact hdvd,
end

lemma cong_char_is_eq_N'
{R : Type*} [semiring R] {p : ℕ} (hp : ring_char R = p) (a b : ℕ) (hleq : a ≤ b) (hdvd : (p : ℤ) ∣ (b - a)) : (a : R) = (b : R) :=
begin
  by_cases hpzero : p = 0, {
    rw hpzero at hdvd,
    simp [sub_eq_zero] at hdvd,
    rw hdvd,
  },
  replace hpzero := pos_iff_ne_zero.mpr hpzero,
  zify at hpzero,
  cases hdvd with c hdvd,
  rw ring_char.eq_iff at hp,
  zify at hleq,
  replace hleq : ((b:ℤ) - a) ≥ 0 := by linarith,
  rw hdvd at hleq,
  simp [hpzero] at hleq,
  lift c to ℕ using hleq,
  replace hdvd : (b:ℤ) = a + p * c := by { rw ← hdvd, ring, },
  norm_cast at hdvd,
  rw hdvd,
  push_cast,
  simp [(@char_p.cast_eq_zero_iff R _ p hp p).2 (dvd_refl p)],
end

lemma cong_char_is_eq_N
{R : Type*} [semiring R] {p : ℕ} (hp : ring_char R = p) (a b : ℕ) (hdvd : (p : ℤ) ∣ (b - a)) : (a : R) = (b : R) :=
begin
  by_cases h : b ≥ a, {
    exact cong_char_is_eq_N' hp a b h hdvd,
  },
  replace h : a ≥ b := by linarith,
  replace hdvd : (p : ℤ) ∣ (a - b) := by {
    cases hdvd with c hdvd,
    use -c,
    replace hdvd : (b:ℤ) = a + p * c := by { rw ← hdvd, ring, },
    rw hdvd,
    ring,
  },
  exact (cong_char_is_eq_N' hp b a h hdvd).symm,
end

lemma cong_char_is_eq
{R : Type*} [ring R] {p : ℕ} (hp : ring_char R = p) (a b : ℤ) (hdvd : (p : ℤ) ∣ (b - a)) : (a : R) = (b : R) :=
begin
  rw ring_char.eq_iff at hp,
  rw @char_p.int_coe_eq_int_coe_iff R _ p hp a b,
  rw int.modeq.modeq_iff_dvd,
  exact hdvd,
end

lemma ncong_char_is_neq
{R : Type*} [ring R] {p : ℕ} (hp : ring_char R = p) (a b : ℤ) (hdvd : ¬ (p : ℤ) ∣ (b - a)) : (a : R) ≠ (b : R) :=
begin
  rw ring_char.eq_iff at hp,
  rw [ne.def, @char_p.int_coe_eq_int_coe_iff R _ p hp a b],
  rw int.modeq.modeq_iff_dvd,
  exact hdvd,
end

section char_specific

  lemma char_two_bit0 {R : Type*} [semiring R] (hchar : ring_char R = 2) (x : R) : bit0 x = 0 := begin
    unfold bit0,
    transitivity (2:R) * x,
    { rw [bit0, add_mul, one_mul], },
    rw ring_char.eq_iff at hchar,
    have := @char_p.cast_eq_zero R _ 2 hchar,
    norm_cast at this,
    rw [this, zero_mul],
  end

  lemma char_two_bit1 {R : Type*} [semiring R] (hchar : ring_char R = 2) (x : R) : bit1 x = 1 := begin
    unfold bit1,
    rw [char_two_bit0 hchar, zero_add],
  end

  example {R : Type*} [semiring R] (hchar : ring_char R = 2) : (35 : R) = 37 := begin
    simp [char_two_bit0 hchar, char_two_bit1 hchar],
  end

  open tactic (get_local infer_type)
  open interactive (parse)
  open lean.parser (ident)
  open interactive (loc.ns)
  open interactive.types (texpr location)

  meta def repeat_at_most : ℕ → tactic unit → tactic unit
  | 0 t := tactic.skip
  | (n+1) t := (do t, repeat_at_most n t) <|> tactic.skip

  meta def ring_char_tactic_internal (s : simp_lemmas) (u : list name) (loc : parse location) : tactic unit :=
  do
    s ← s.add_simp ``pow_zero,
    s ← s.add_simp ``pow_one,
    s ← s.add_simp ``zero_mul,
    s ← s.add_simp ``mul_zero,
    s ← s.add_simp ``zero_pow,
    s ← s.add_simp ``one_pow,
    ns ← loc.get_locals,
    -- FIXME: add a maximal repeat time since sometimes simp will change the goal randomly
    repeat_at_most 4 (do
      ret1 ← tactic.replace_at (
        λ e, do (a1, a2, _) ← tactic.simplify s u e, return (a1, a2)
      ) ns loc.include_goal,
      ret2 ← tactic.replace_at (
        tactic.ring.normalize tactic.transparency.reducible
      ) ns loc.include_goal,
      if ret1 || ret2 then tactic.skip else tactic.failed
    ),
    when loc.include_goal $ tactic.try (tactic.triv <|> tactic.reflexivity <|> tactic.contradiction)

  -- (hchar_ : parse texpr)
  -- hchar ← tactic.i_to_expr hchar_,
  -- `(ring_char _ = 2) ← infer_type hchar,

  /--
  Experimental ring tactic for characteristic 2.
  FIXME: You must provide a `hchar2 : ring_char R = 2` hypothesis.
  -/
  meta def tactic.interactive.ring_char2 (loc : parse location) : tactic unit :=
  do
    hchar ← get_local `hchar2,
    `(ring_char _ = 2) ← infer_type hchar | tactic.fail "hchar2 : ring_char R = 2 is expected",
    (s, u) ← tactic.mk_simp_set ff [] [], -- FIXME: this includes all default simp lemmas into it
    s ← tactic.to_expr ``(char_two_bit0 %%hchar) >>= s.add,
    s ← tactic.to_expr ``(char_two_bit1 %%hchar) >>= s.add,
    ring_char_tactic_internal s u loc

  example {R : Type*} [semiring R] (hchar2 : ring_char R = 2) : (35 : R) = 37 := begin
    ring_char2,
  end

  example {R : Type*} [semiring R] (hchar2 : ring_char R = 2) (x : R) (h : (35 : R) * x = 37) : x = 39 := begin
    ring_char2 at h ⊢,
    exact h,
  end

  /-lemma char_three_2_is_invertible {R : Type*} [semiring R] (hchar : ring_char R = 3) : is_unit (2:R) := begin
    use [(2:R),(2:R)],
    { norm_num, exact_mod_cast cong_char_is_eq_N hchar 4 1 (by norm_num), },
    { norm_num, exact_mod_cast cong_char_is_eq_N hchar 4 1 (by norm_num), },
    fconstructor,
  end-/

  lemma char_three_3_eq_0 {R : Type*} [semiring R] (hchar : ring_char R = 3) : (3:R) = 0 := begin
    exact_mod_cast dvd_char_is_zero_N hchar 3 (by norm_num),
  end

  lemma char_three_4_eq_1 {R : Type*} [semiring R] (hchar : ring_char R = 3) : (4:R) = 1 := begin
    exact_mod_cast cong_char_is_eq_N hchar 4 1 (by norm_num),
  end

  lemma char_three_5_eq_2 {R : Type*} [semiring R] (hchar : ring_char R = 3) : (5:R) = 2 := begin
    exact_mod_cast cong_char_is_eq_N hchar 5 2 (by norm_num),
  end

  example {R : Type*} [semiring R] (hchar : ring_char R = 3) : (34 : R) = 37 := begin
    simp [char_three_3_eq_0 hchar, char_three_4_eq_1 hchar, char_three_5_eq_2 hchar],
  end

  /--
  Experimental ring tactic for characteristic 3.
  FIXME: You must provide a `hchar3 : ring_char R = 3` hypothesis.
  -/
  meta def tactic.interactive.ring_char3 (loc : parse location) : tactic unit :=
  do
    hchar ← get_local `hchar3,
    `(ring_char _ = 3) ← infer_type hchar | tactic.fail "hchar3 : ring_char R = 3 is expected",
    (s, u) ← tactic.mk_simp_set ff [] [], -- FIXME: this includes all default simp lemmas into it
    -- s ← tactic.to_expr ``(char_three_2_is_invertible %%hchar) >>= s.add,
    s ← tactic.to_expr ``(char_three_3_eq_0 %%hchar) >>= s.add,
    s ← tactic.to_expr ``(char_three_4_eq_1 %%hchar) >>= s.add,
    s ← tactic.to_expr ``(char_three_5_eq_2 %%hchar) >>= s.add,
    ring_char_tactic_internal s u loc

  example {R : Type*} [semiring R] (hchar3 : ring_char R = 3) : (34 : R) = 37 := begin
    ring_char3,
  end

  /-example {R : Type*} [semiring R] (hchar3 : ring_char R = 3) (x : R) (h : (35 : R) * x = 0) : x = 0 := begin
    ring_char3 at h,
  end-/

  lemma char_p_a_plus_p_eq_a {R : Type*} [semiring R] {p : ℕ} (hchar : ring_char R = p)
  (a : ℕ) : ((a+p) : R) = a :=
  begin
    exact_mod_cast (cong_char_is_eq_N hchar a (a+p) (by simp)).symm,
  end

  meta def repeat_n_times {T : Type*} : ℕ → (ℕ → T → tactic T) → T → tactic T
  | 0 func t := (do return t)
  | (n+1) func t := (do func n t >>= repeat_n_times n func)

  /--
  Experimental ring tactic for characteristic p for p an integer literal.
  FIXME: You must provide a `hchar : ring_char R = p` hypothesis.
  -/
  meta def tactic.interactive.ring_charp (loc : parse location) : tactic unit :=
  do
    hchar ← get_local `hchar,
    `(ring_char _ = %%pp) ← infer_type hchar | tactic.fail "hchar : ring_char R = p is expected",
    p ← pp.to_nat <|> tactic.fail "p must be an integer literal",
    step ← norm_num.get_step,
    (s, u) ← tactic.mk_simp_set ff [] [], -- FIXME: this includes all default simp lemmas into it
    s ← repeat_n_times p (λ n (ss : simp_lemmas), do
      char_p_a_plus_p_eq_a ← tactic.to_expr ``(char_p_a_plus_p_eq_a %%hchar %%n),
      (_, a2) ← infer_type char_p_a_plus_p_eq_a >>= norm_num.derive' step,
      ss ← tactic.mk_eq_mp a2 char_p_a_plus_p_eq_a >>= ss.add,
      return ss
    ) s,
    ring_char_tactic_internal s u loc

  example {R : Type*} [semiring R] (hchar : ring_char R = 5) : (123567 : R) = 51832 := begin
    ring_charp,
  end

end char_specific
