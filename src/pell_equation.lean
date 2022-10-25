import number_theory.pell

/-!
# Pell's Equation

The goal of this project is to prove the following

**Theorem.** Let d be a natural number that is not a square. Then the equation
  x² - d y² = 1                                                     (31)
has a nontrivial (i.e., y ≠ 0) solution in integers.

In fact, there are infinitely many solutions that can all be obtained from
the smallest positive solution (the "fundamental solution"). Here is the relevant
text from §17.5 in Ireland-Rosen.

**Proposition 17.5.1.** If ξ ∈ ℝ is irrational, then there are infinitely many rational
numbers x/y, gcd(x, y) = 1, such that |x/y - ξ| < 1/y².

PROOF. Partition the half-open interval [0, 1) by
  [0, 1) = [0, 1/n) ∪ [1/n, 2/n) ∪ ... ∪ [(n-1)/n, 1).
If [α] denotes, as usual, the largest integer less than or equal to α, then the
fractional part of α is defined by α - [α], It lies in a unique member of the
partition. Consider the fractional parts of 0, ξ, 2 ξ, ..., n ξ. At least two of these
must lie in the same subinterval. In other words there exist j, k with j > k,
0 ≤ j, k ≤ n such that
  |j ξ - [j ξ] - (k ξ - [k ξ])| < 1/n.                              (32)

Put y = j - k, x = [k ξ] - [j ξ], so that (32) becomes [x - Y ξ| < 1/n. Here
we may assume that gcd(x, y) = 1, since division by gcd(x, y) only strengthens the
inequality. But 0 < y < n implies that |x/y - ξ| < Ilny < 1/(n y) < 1/y². To obtain
infinitely many solutions, note that |x/y - ξ| ≠ 0 and choose an integer 
m > 1/|x/y - ξ|. The ~ above procedure gives the existence of integers x₁, y₁
such that |x₁/y₁ - ξ| < 1/(m y\¹) < |x/< - ξ| and 0 < y₁ < m. This procedure
leads to an infinite number of solutions. QED

This proposition will be applied to show that |x² - d y²| assumes the same
value infinitely often.

**Lemma 1.** If d is a positive square-free integer, then there is a constant M such
that |x² - d y²| < M has infinitely many inteqral solutions.

PROOF. Write x² - d y² = (x + √d y)(x - √d y). By Proposition 17.5.1,
there exist infinitely many pairs of relatively prime integers (x, y), y > 0,
satisfying |x - √d y| < 1/y. It follows that
  |x + √d y| < |x - √d y| + 2 √d |y| < 1/y + 2 √d y.
Hence |x² - d y²| < |1/y + 2 √d y|/y ≤ 2 √d + 1 and the proof is complete. QED

The main result of this section is as follows.

**Proposition 17.5.2.** If d is a positive square-free integer, then x² - d y² = 1 has
infinitely many inteqral solutions. Furthermore, there is a solution (x₁, y₁) such
that every solution has the form ±(xₙ, yₙ), where xₙ + √d yₙ = (x₁ + √d y₁)ⁿ, n ∈ ℤ.

PROOF. By Lemma 1 there is an m ∈ ℤ such that x² - d y² = m for infinitely
many integral pairs (x, y), x > 0, y > 0. We may assume that the x components
are distinct. Furthermore, since there are only finitely many residue
classes modulo |m|, one can find (x₁, y₁), (x₂, y₂), x₁ ≠ x₂ such that
x₁ ≡ x₂ mod |m|, y₁ ≡ y₂ mod |m|. Put α = x₁ - y₁ √d, β = x₂ - y₂ √d.
If γ = x - y √d, let γ' = x + y √d denote the conjugate of γ and
N(γ) = x² - d y² denote the norm of γ. Recall that N(α β) = N(α) N(β). A short
calculation shows that α β' = A + B √d, where m ∣ A, m ∣ B. Thus α β' = m(u + v √d)
for integers u and v. Taking norms of both sides gives m² = m²(u² - v² d). Thus
  u² - d v² = 1                                                     (33)
It remains to see that v ≠ 0. However, if v = 0, then u = ±1 and α β' = ±m.
Multiplying by β gives α m = ±m β or α = ±β. But this implies that x₁ = x₂.
Thus Pell's equation has a solution with x y ≠ O.

To prove the second assertion, let us say that a solution (x, y) is greater than
a solution (u, v) if x + y √d > u + v √d. Now consider the smallest solution
α with x > 0, y > O. Such a solution clearly exists (why?) and is unique. It is
called the *fundamental solution*.

Consider any solution β = u + v √d, u > 0, v > O. We show that there is a
positive integer n such that β = αⁿ. For otherwise chose n > 0 so that αⁿ < β < aⁿ⁺¹.
Then, since α' = α⁻¹, 1 < (α')ⁿ β < α. But if (α')ⁿ β = A + B √d,
(A, B) is a solution to Pell's equation and 1 < A + B √d < α.
Now A + B √d > 0, so A - B √d = (A + B √d)⁻¹ > O. Thus A > O.
Also A - B √d = (A + B √d)⁻¹ < 1, so B √d > A - 1 ≥ O. Thus B > 0. This contradicts
the choice of α. If β = a + b √d is a solution with a > 0, b < 0,
then β⁻¹ = a - b √d = aⁿ by the above, so β = α⁻ⁿ. The cases a < 0, b > 0 and
a < 0, b < 0 lead obviously to -αⁿ for n ∈ ℤ. The proof is now complete. QED
-/
