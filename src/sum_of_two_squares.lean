import number_theory.sum_two_squares

/-!
# Sums of two squares

The goal of this project is to prove the following statement.

**Theorem.** Let n be a positive natural number. Then n can be written
as n = a² + b² with natural numbers a and b if and only if every prime
q ≡ 3 mod 4 occurs with an even exponent in the prime factorization of n.

mathlib has *Fermat's two-squares theorem* that says that a prime p ≡ 1 mod 4
is a sum of two squares.

theorem nat.prime.sq_add_sq {p : ℕ} [fact (nat.prime p)] (hp : p % 4 = 1) :
  ∃ (a b : ℕ), a ^ 2 + b ^ 2 = p

From this (and the facts that 2 is a sum of two squares and that the set
of sums of two squares is multiplicative), the "if" direction follows
fairly easily. For the "only if" direction, one has to show the following

**Lemma.** If q ≡ 3 mod 4 is a prime and q divides a² + b², then q
divides a and b (and hence q² divides a² + b²).

There are the following lemmas in mathlib, which might be helpful.

theorem zmod.exists_sq_eq_neg_one_iff {p : ℕ} [fact (nat.prime p)] :
  is_square (-1 : zmod p) ↔ p % 4 ≠ 3

theorem zmod.mod_four_ne_three_of_sq_eq_neg_sq' {p : ℕ} [fact (nat.prime p)]
  {x y : zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
  p % 4 ≠ 3
-/
