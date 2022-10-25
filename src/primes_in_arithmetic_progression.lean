import tactic

/-!
# Dirichlet density of primes ≡ 1 and primes ≡ 3 mod 4

The goal of this project is to prove

**Theorem.** The sets of primes p ≡ 1 mod 4 and of primes p ≡ 3 mod 4 both have 
Dirichlet density 1/2.

This is covered in Ireland-Rosen, §16.1-2:

## §1 The Zeta Function

The Riemann zeta function ζ(s) is defined by ζ(s) = ∑_{n=1}^∞ n⁻ˢ.
It converges for s > 1 and converges uniformly for s ≥ 1 + δ > 1, for each δ > O.

**Proposition 16.1.1.** For s > 1.
  ζ(s) = ∏ₚ (1 - p⁻ˢ)⁻¹,
where the product is over all primes p > 0.

PROOF. For s > 1, p⁻ˢ < 1, so we have (1 - p⁻ˢ)⁻¹ = ∑_{m=0}^∞ p⁻ᵐˢ.
By the theorem of unique factorization
  ∏_{p ≤ N} (1 - p⁻ˢ)⁻¹ = ∑_{n ≤ N} n⁻ˢ + R_N(s) .
Clearly, R_N(s) ≤ ∑_{n=N+1}^∞ n⁻ˢ. Since ζ(s) converges, R_N(s) → 0 as N → ∞. The
result follows. QED

The behavior of ζ(s) as s → 1 is very important. Since ∑_{n=1}^∞ n⁻¹ diverges,
we, of course, suspect ζ(s) → ∞ as s → 1. In fact,

**Proposition 16.1.2.** Assume s > 1. Then
  lim_{s → 1} (s - l) ζ(s) = 1.

PROOF. For fixed s, t⁻ˢ is a monotone decreasing function of t. Thus,
  (n + 1)⁻ˢ < ∫_n^{n+1} t⁻ˢ dt < n⁻ˢ .
Summing from n = 1 to ∞,
  ζ(s) - 1 < ∫_1^∞ t⁻ˢ dt < ζ(s) .
The value of the integral is (s - 1)⁻¹. It follows that 1 < (s - 1) ζ(s) < s.
Taking the limit as s → 1 gives the result. QED

**Corollary.** As s → 1 we have
  (ln ζ(s))/(ln (s-1)⁻¹) → 1 .

PROOF. Let (s - 1) ζ(s) = ρ(s). Then ln(s - 1) + ln ζ(s) = ln ρ(s), so we have
ln ζ(s)/ln(s - 1)⁻¹ = 1 + (ln ρ(s))/ln(s - 1)^⁻¹.
As s → 1, ρ(s) → 1 by the proposition. Therefore, ln ρ(s) → 0, and the
result follows. QED

**Proposition 16.1.3.** ln ζ(s) = ∑ₚ p⁻ˢ + R(s), where R(s) remains bounded as
s → 1.

PROOF. We use the formula -ln(1 - x) = x + x²/2 + x³/3 + ..., which is
valid for -1 < x < 1.
By Proposition 16.1.1 we have
  ζ(s) = ∏_{p ≤ N} (1 - p⁻ˢ)⁻¹ λ_N(s) ,
where λ_N(S) → 1 as N → ∞. Taking the logarithm of both sides yields
ln ζ(s) = ∑_{p ≤ N} ∑_{m=1}^∞ m⁻¹ p⁻ᵐˢ + ln λ_N(s).
Taking the limit as N → ∞
  ln ζ(s) = ∑ₚ ∑_{m=1}^∞ m⁻¹ p⁻ᵐˢ = ∑ₚ p⁻ˢ + ∑ₚ ∑_{m=2}^∞ m⁻¹ p⁻ᵐˢ .
The second sum is less than
  ∑ₚ ∑_{m=2}^∞ p⁻ᵐˢ = ∑ₚ p⁻²ˢ (1 - p⁻ˢ)⁻¹ ≤ (1 - 2⁻ˢ)⁻¹ ∑ₚ p⁻²ˢ ≤ 2 ζ(2).
Throughout we have used the assumption that s > 1. QED

**Definition.** A set of positive primes 𝒫 is said to have *Dirichlet density* if
  lim_{s → 1} (∑_{p ∈ 𝒫} p⁻ˢ)/ln (s-1)⁻¹
exists. If the limit exists we set it equal to d(𝒫) and call d(𝒫) the
*Dirichlet density* of 𝒫.

**Proposition 16.1.4.** Let 𝒫 be a set of positive prime numbers. Then
(a) If 𝒫 is finite, then d(𝒫) = 0.
(b) If 𝒫 consists of all but finitely many positive primes, then d(𝒫) = 1.
(c) If 𝒫 = 𝒫₁ ∪ 𝒫₂ where 𝒫₁ and 𝒫₂ are disjoint and d(𝒫₁) and d(𝒫₂) both
exist, then d(𝒫) = d(𝒫₁) + d(𝒫₂).

PROOF. Parts (a) and (c) are clear from the definition of Dirichlet density.
Part (b) follows quickly from the corollary to Proposition 16.1.2 and Proposition 16.1.3.
QED

We are now in a position to state the main theorem of this chapter. The
proof will be spread out over the next three sections.

**Theorem 1** (L. Dirichlet). Suppose a, m ∈ ℤ, with gcd(a, m) = 1. Let 𝒫(a; m) be the
set of positive primes p such that p ≡ a mod m. Then d(𝒫(a; m)) = 1/ϕ(m).

Note that Theorem 1 certainly implies 𝒫(a; m) is infinite, since if it were
finite, its density would be zero.


## §2 A Special Case

We will first prove Theorem 1 in the case where m = 4. The basic ideas of the
proof are all present in this special case, but the details are more transparent.
Define a function χ from ℤ to {0, ±1} as follows; χ(n) = 0 if n is even,
χ(n) = 1 if n ≡ 1 mod 4, and χ(n) = -1 if n ≡ 3 mod 4. It is easily seen that
χ(m n) = χ(m) χ(n) for all m, n ∈ ℤ.

Define L(s, χ) = ∑_{n=1}^∞ χ(n) n⁻ˢ = 1 - 3⁻ˢ + 5⁻ˢ - 7⁻ˢ + ... . For all n
we have |χ(n) n⁻ˢ| ≤ n⁻ˢ. It follows that the terms of L(s, χ) are dominated in
absolute value by the terms of ζ(s). Thus L(s, χ) converges and is continuous
for s > 1. Since χ is completely multiplicative, the proof of Proposition 16.1.1.
shows that
  L(s, χ) = ∏ₚ (1 - χ(p) p⁻ˢ)^⁻¹ .
It is useful to modify ζ(s) so as to suppress the even terms. Define ζ*(s) = ∑{n odd} n⁻ˢ.
Since
  ζ(s) = ∑_{n=1}^∞ n⁻ˢ = ∑_{n odd} n⁻ˢ + ∑_{n even} n⁻ˢ = ζ*(s) + 2⁻ˢ ζ(s)
we have ζ*(s) = (1 - 2⁻ˢ) ζ(s) and so
  ζ*(s) = ∏_{p odd} (1 - p⁻ˢ)⁻¹ .
Using the method of proof of Proposition 16.1.3 we find
  ln L(s, χ) = ∑_{p odd} χ(p) p⁻ˢ + R₁(s)                            (i)
    ln ζ*(s) = ∑_{p odd} p⁻ˢ + R₂(s)                                (ii)
where R₁(s) and R₂(s) remain bounded as s → 1.

We have 1 + χ(p) = 2 if p ≡ 1 mod 4 and 1 + χ(p) = 0 if p ≡ 3 mod 4. Similarly,
1 - χ(p) = 2 if p ≡ 3 mod 4 and 1 - χ(p) = 0 if p ≡ 1 mod 4.  From (i) and (ii) we
deduce
  ln ζ*(s) + ln L(s, χ) = 2 ∑_{p ≡ 1 mod 4} p⁻ˢ + R₃(s)            (iii)
  ln ζ*(s) - ln L(s, χ) = 2 ∑_{p ≡ 3 mod 4} p⁻ˢ + R₄(s)             (iv)
 where R₃(s) and R₄(s) remain bounded as s → 1.

The next step is to show that ln L(s, χ) remains bounded as s → 1. To see
this, write
  L(s, χ) = (1 - 3⁻ˢ) + (5⁻ˢ - 7⁻ˢ) + ... = 1 - (3⁻ˢ - 5⁻ˢ) - (7⁻ˢ - 9⁻ˢ) - ... .
It follows that for all s > 1 we have 2/3 < L(s, χ) < 1. Thus, for s > 1 we have
ln 2/3 < ln L(s, χ) < ln 1 = 0.

As a final preparatory step we note that ln ζ*(s) = ln(1 - 2⁻ˢ) + ln ζ(s), so
by the corollary to Proposition 16.1.2. we have ln ζ*(s)/ln(s - 1)⁻¹ → 1 as s → 1.

Now divide each term of Equations (iii) and (iv) by ln(s - 1)⁻¹ and take
the limit as s → 1. The result is

**Proposition 16.2.1.** d(𝒫(1; 4)) = 1/2 and d(𝒫(3; 4)) = 1/2.

-/