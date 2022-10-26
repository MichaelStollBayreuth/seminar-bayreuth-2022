-- Example for seminar announcement

import data.zmod.basic -- import relevant part of the library

-- First state and prove the two lemmas that we will need.

/- The first lemma says that `7` is not a sum of three squares in `ℤ/8ℤ`.
This is a finite problem; `dec_trivial` can prove such statements. -/
lemma three_squares_mod_8 : ∀ a b c : zmod 8, a^2 + b^2 + c^2 ≠ 7 := dec_trivial

-- The second lemma says that when `x^2 + y^2 + z^2` is divisible by `4`
-- (where `x`, `y`, `z` are in `ℕ`), then `x`, `y` and `z` are even.
lemma three_squares_even : ∀ x y z : ℕ, 4 ∣ x^2 + y^2 + z^2 → 2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z :=
begin
  -- we first formulate the corresponding statement in `ℤ/4ℤ`
  have h₂ : ∀ a b c : zmod 4,
            a^2 + b^2 + c^2 = 0 → (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2) ∧ (c = 0 ∨ c = 2)
  := dec_trivial, -- again a finite problem
  -- now we need a statement that allows us to translate from `ℤ/4ℤ` to `ℕ`
  have h₄ : ∀ x : ℕ, (x : zmod 4) = 0 ∨ (x : zmod 4) = 2 → 2 ∣ x :=
  begin
    rintros x (hx₁ | hx₂), -- two goals with different assumptions on `x`
    { -- here we assume that `x ≡ 0 mod 4`
      have hx₁' := (zmod.nat_coe_zmod_eq_zero_iff_dvd x 4).mp hx₁,
      rw (show 4 = 2*2, from by norm_num) at hx₁',
      exact dvd_of_mul_left_dvd hx₁', },
    { -- here we assume that `x ≡ 2 mod 4`
      have hx₂' : x % 4 = 2 % 4 := (zmod.nat_coe_eq_nat_coe_iff' _ _ _).mp hx₂,
      apply_fun (λ z, z % 2) at hx₂', -- reduce mod `2`
      rw [nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 4)] at hx₂',
      norm_num at hx₂', -- replace `2 % 4 % 2` by `0`
      exact nat.dvd_of_mod_eq_zero hx₂', },
  end,
  -- now use `h₂` and `h₄` to prove the claim
  intros x y z h,
  have h' := (zmod.nat_coe_zmod_eq_zero_iff_dvd _ _).mpr h, -- write as equality in `ℤ/4ℤ`
  push_cast at h',
  cases h₂ x y z h' with hx hyz,
  cases hyz with hy hz,
  split,
  { apply h₄ x, exact hx, },
  split,
  { apply h₄ y, exact hy, },
  apply h₄ z, exact hz,
  -- rcases h₂ x y z h' with ⟨hx, hy, hz⟩,
  -- exact ⟨h₄ x hx, h₄ y hy, h₄ z hz⟩,
end

-- Now we state the theorem:
-- A natural number of the form `4^k * (8*m + 7)` is not a sum of three squares
theorem three_squares (k m : ℕ) : ¬ ∃ x y z : ℕ, x^2 + y^2 + z^2 = 4^k*(8*m + 7) :=
begin
  push_neg, -- change to `∀ x y z, x^2 + y^2 + z^2 ≠ 4^k*(8*m+7)`
  intros x y z hxyz, -- now we have to show a contradiction
  -- we do induction on `k`, but with the statement `∀ x y z, ...`
  induction k with k ih generalizing x y z,
  { -- the base case: `k = 0`
    apply_fun (coe : ℕ → zmod 8) at hxyz, -- reduce mod `8`
    norm_num at hxyz, -- simplify and apply `three_squares_mod_8`
    exact three_squares_mod_8 x y z hxyz, },
  { -- the inductive step; `ih` is the induction hypothesis
    rw [pow_succ _ k, mul_assoc] at hxyz, -- replace `4^(k+1)*...` by `4*(4^k*...)`
    have h : 4 ∣ x^2 + y^2 + z^2 := 
    begin
      change ∃ a : ℕ, x^2 + y^2 + z^2 = 4*a,
      use 4 ^ k * (8 * m + 7),
      exact hxyz,
    end,
    -- ⟨4^k*(8*m+7), hxyz⟩,
    -- it follows that `x`, `y` and `z` are divisible by `2`
    -- we need to spell this out, so that we can replace `x` by `2*x₁` etc.
    rcases three_squares_even x y z h with ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩, ⟨z₁, hz₁⟩⟩,
    rw [hx₁, hy₁, hz₁,
        -- the following does the calculation that allows us to cancel `4*...`
        (by ring : (2*x₁)^2 + (2*y₁)^2 + (2*z₁)^2 = 4*(x₁^2 + y₁^2 + z₁^2))] at hxyz,
    exact ih x₁ y₁ z₁ (mul_left_cancel₀ (by norm_num : 4 ≠ 0) hxyz), },
end

open nat

/-- Helper lemma for gcds -/
lemma gcd_mul_coprime {a b : ℕ} (c : ℕ) (h₁ : gcd a b = 1) : (gcd a c) * (gcd b c) = gcd (a*b) c :=
begin
  -- this is `nat.coprime.gcd_mul` up to the symmetry of `gcd`
  rw [gcd_comm a, gcd_comm b, gcd_comm (a*b), coprime.gcd_mul _ h₁],
end

/- Descent Lemma -/
lemma descent {a b c : ℕ} (h₁ : gcd a b = 1) (h₂ : a*b = c^2) : ∃ u v, a = u^2 ∧ b = v^2 ∧ c = u*v :=
begin
  cases eq_or_ne c 0 with hc hc,
  -- first deal with the case `c = 0`
  { simp [hc] at *,
    cases h₂ with h₀ h₀,
    all_goals { simp [h₀] at *, simp [h₁] },
    { use [0, 1], simp, },
    { use [1, 0], simp, } },
  -- now `c ≠ 0`; this implies that `a*b ≠ 0`
  have h₀ : a*b ≠ 0,
  { intro h, rw h at h₂, exact hc (pow_eq_zero h₂.symm), },
  -- we can take `u = gcd a c` and `v = gcd b c`
  use [gcd a c, gcd b c],
  -- prove the last statement
  have h₃ : (gcd a c) * (gcd b c) = c,
  { rw [gcd_mul_coprime c h₁, h₂, pow_two, gcd_mul_left_left], },
  -- this implies `u^2 * v^2 = a*b`
  have h₄ : (gcd a c)^2 * (gcd b c)^2 = a*b,
  { rw h₂, conv_rhs {rw [← h₃]}, ring, },
  -- since `a` and `b` are coprime, `a` is coprime to `v^2`
  have ha : coprime a ((gcd b c)^2),
  { rw [coprime_pow_right_iff (by norm_num : 0 < 2), nat.gcd_comm],
    exact coprime.gcd_right c h₁, },
  -- similarly, `b` is coprime to `u^2`
  have hb : coprime b ((gcd a c)^2),
  { rw [coprime_pow_right_iff (by norm_num : 0 < 2), nat.gcd_comm],
    have h₁' : gcd b a = 1, { rw nat.gcd_comm, exact h₁, },
    exact coprime.gcd_right c h₁', },
  -- we deduce that `a` divides `u^2` and `b` divides `v^2`
  have ha' : a ∣ (gcd a c)^2,
  { refine coprime.dvd_of_dvd_mul_left ha _,
    rw [mul_comm, h₄],
    exact dvd_mul_right a b, },
  have hb' : b ∣ (gcd b c)^2,
  { refine coprime.dvd_of_dvd_mul_left hb _,
    rw [h₄],
    exact dvd_mul_left b a, },
  -- write `u^2 = a * r` and `v^2 = b * s`
  cases ha' with r hr,
  cases hb' with s hs,
  -- then `(a*b) * (r*s) = a*b`, which implies `r*s = 1`
  rw [hr, hs, mul_comm b, mul_assoc, ← mul_assoc r, mul_comm _ b, ← mul_assoc] at h₄,
  nth_rewrite 1 ← mul_one (a * b) at h₄,
  have hrs := mul_left_cancel₀ h₀ h₄,
  -- and therefore `r = s = 1`
  rw [eq_one_of_mul_eq_one_right hrs, mul_one] at hr,
  rw [eq_one_of_mul_eq_one_left hrs, mul_one] at hs,
  exact ⟨hr.symm, hs.symm, h₃.symm⟩,
end
