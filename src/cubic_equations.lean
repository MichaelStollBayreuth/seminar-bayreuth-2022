import tactic

/-!
# Cubic equations with infinitely many solutions

The goal of this project is to prove the following

**Theorem.** If a > 2 is a cube-free integer such that the equation
  x³ + y³ = a                                                       (59)
has a solution in rational numbers, then it has infinitely many rational solutions.

See Ireland-Rosen, §17.9:

We say that an integer a is *cube-free* if ordₚ a ≤ 2 for all primes p, that is,
no cube ≠ ±1 divides a.

PROOF (of the theorem above).
Let (α, β) be a rational point on (59). If α = x₁/z₁, β = y₁/z₁' and
gcd(x₁, z₁) = gcd(y₁, z₁') = 1 with x₁, y₁, z₁, z₁' integers, then it is easy to see
that z₁ = z₁'. Since a > 2 is cube-free, x₁ y₁ ≠ 0 and x₁ ≠ y₁. The tangent line to (59) at
(α, β) is α² x + β² y = a. Solving for y and substituting in (59) gives
  x³ + ((a - α² x)/β²)³ - a = 0.                                    (60)
The left-hand side of (60) is a cubic pol ynomial with α as a double root (at least).
Ifthe third root is γ, then since the sum of the roots is the negative of
the coefficient of x², we obtain after a simple calculation,
  2 α + γ = 3 α⁴/(α³ - β³) .                                        (61)
Thus
  γ = α(α³ + 2β³)/(α³ - β³) = (x₁/z₁) (x₁³ + 2y₁³)/(x₁³ - y₁³) .    (62)
The corresponding value for y = (a - α² x)/β² is
  ρ = (-y₁/z₁) (2x₁³ + y₁³)/(x₁³ - y₁³)                             (63)
and by (60), (γ, ρ) is a rational point on the cubic. The reader may verify
directly, of course, that (γ, ρ) satisfies γ³ + ρ³ = a. It remains to show that
(γ, ρ) is distinct from (α, β) and moreover that one obtains by this process an
infinite number of points on the curve. Define the integer A by A > 0 and
  A x₂ = x₁(x₁³ + 2y₁³),
  A y₂ = -y₁(2x₁³ + y₁³),                                           (64)
  A z₂ = z₁(x₁³ - y₁³),
with gcd(x₂, y₂, z₂) = 1. Thus A is the greatest common divisor of the integers on
the right-hand side of (64). Clearly one has
  x₂³ + y₂³ = a z₂³,  z₂ ≠ 0.                                       (65)
Since a is cube-free and gcd(x₂, y₂, z₂) = 1, we see that gcd(x₂, y₂) = gcd(x₂, z₂) =
gcd(y₂, z₂) = 1. We claim that A is equal to 1 or 3. For if p is prime and p ∣ A, then
it follows without difficulty from (64) that p does not divide x₁ y₁ z₁. Thus p divides
each of the second factors on the right-hand side of (64) and consequently p ∣ 3 y₁³.
Thus p is 1 or 3. Notice, also, that gcd(A, z₁) = 1 implies A ∣ x₁³ - y₁³.

The proof will be completed by showing that |z₂| > |z₁|. To this end one has
  |z₂| = (|z₁|/A) |x₁³ - y₁³| = (|z₁|/A) |x₁ - y₁| |x₁² + x₁ y₁ + y₁²|. (66)
One sees, 4 |x₁² + x₁ y₁ + y₁²| = |(2x₁ + Y₁)² + 3y₁²| > 4 and consequently
one has the inequality |z₂| > |z₁| |x₁ - y₁|/A. If A = 1, then (66) shows
that |z₂| > |z₁|. On the other hand, if A = 3, then since A | x₁³ - y₁³, one has
x₁³ ≡ y₁³ mod 3, which implies that x₁ ≡ y₁ mod 3, and once again (66) implies
that |z₂| > |z₁|. Continuing in this manner, one obtains a succession of points
(xₙ/zₙ, yₙ/zₙ), xₙ yₙ ≠ 0, gcd(xₙ, zₙ) = gcd(yₙ, zₙ) = 1 and |zₙ| > |zₙ₋₁|, and the
proof is co mplete. QED

-/