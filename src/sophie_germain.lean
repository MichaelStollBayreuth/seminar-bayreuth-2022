import tactic

/-!
# Sophie Germain's Theorem

The goal of this project is to prove **Sophie Germain's Theorem**
(see Ireland-Rosen, §17.4):

If p is an odd prime such that q = 2p+1 is also prime, then
  xᵖ + yᵖ + zᵖ = 0                                                     (24)
has no integral solution such that p does not divide x y z.

PROOF. Assume on the contrary that such a solution exists and suppose that
gcd(x, y, z) = 1. Write
  -xᵖ = (y + z)(zᵖ⁻¹ - zᵖ⁻² y + ... + yᵖ⁻¹).                           (25)
The two factors on the right are relatively prime. For clearly p does not divide y + z
and if r ≠ p is a prime dividing both factors then since y ≡ -z mod r one has
  0 ≡ zᵖ⁻¹ - zᵖ⁻² y + ... + yᵖ⁻¹ mod r,
which implies that r ∣ y. This in turn implies that r ∣ z (by (24)) contradicting the
assumption that gcd(x, y, z) = l. By unique factorization in ℤ we conclude that
  y + z = A^p                                                          (26)
  zᵖ⁻¹ - zᵖ⁻² y + ... + yᵖ⁻¹ = Tᵖ                                      (27)
for suitable integers A and T. Similarly
  x + y = Bᵖ                                                           (28)
  x + z = Cᵖ.                                                          (29)
Since p = (q-1)/2, reducing (24) modulo q gives
  x^{(q-1)/2} + y^{(q-1)/2} + z^{(q-1)/2} ≡ 0 mod q.
If q does not divide x y z, then each of the terms on the left-hand side is ±1 modulo q.
This is impossible, since q > 5. Thus, by symmetry, we may assume that q ∣ x. From
(26), (28) and (29) we conclude that
  Bᵖ + Cᵖ - Aᵖ = 2x
so that
  B^{(q-1)/2} + C^{(q-1)/2} - A^{(q-1)/2} ≡ 0 mod q.                   (30)
Once again it follows that q ∣ A B C. However, since q ∣ x, (28) and (29) imply
that q ∣ B C is impossible. Thus q ∣ A. By (26) and (27) we see that
  Tᵖ ≡ p yᵖ⁻¹ mod q.
By (28), y ≡ Bᵖ mod q; and since gcd(A, T) = 1, q does not divide T. Thus,
since p = (q - 1)/2, we have ±1 ≡ p mod q, which is impossible.
Thus the proof is complete. 
-/
