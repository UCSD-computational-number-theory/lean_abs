import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Order.Height
import Mathlib.Order.WithBot
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Span.Defs
--import Mathlib.Data.Real.ENNReal

variable {R : Type _} [CommRing R]

variable (I : Ideal R)

#check Ideal.IsPrime

noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
  Order.height {J : PrimeSpectrum R | J.asIdeal < I}

-- noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
--   Order.height (fun _ : PrimeSpectrum R => I)

#check height

-- Minimal prime proof
theorem minimal_prime_IsMin (I : Ideal R) (P : Ideal R)
    (Pmin : P ∈ Ideal.minimalPrimes I) :
    IsMin P := by
  rw [Ideal.minimalPrimes] at Pmin
  rcases Pmin with ⟨hPrime, hMinimal⟩
  intros Q hQ
  have QPrime : Q.IsPrime := by
    sorry
  have IleQ : I ≤ Q := by
    sorry
  specialize hMinimal ?_
  apply Q; simp [IleQ, QPrime];
  exact hMinimal (by assumption)


lemma height_eq_zero_if_minimal [h : I.IsPrime] :
    I ∈ minimalPrimes R → height I = 0 := by
  intro hmin
  unfold height
  simp
  sorry

theorem height_1_of_principal_of_prime [h : I.IsPrime] [h' : I.IsPrincipal] : height I ≤ 1 := by
  rw [height, Order.height]
  simp_all
  intro ltseries relseries
  sorry
  -- Associated primes, Krull's principal ideal theorem,
