import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Order.WithBot
import Mathlib.Order.Height
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Span.Defs
--import Mathlib.Data.Real.ENNReal

variable {R : Type _} [CommRing R]

variable (I : Ideal R)

#check Ideal.IsPrime

noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
  Order.height {J : PrimeSpectrum R | J.asIdeal ≤ I}

#check height

--noncomputable def height [h : IsPrime I] : WithBot ℕ∞ :=
  --Order.height (PrimeSpectrum R) (I : PrimeSpectrum R)


theorem height_1_of_principal_of_prime [h : I.IsPrime] [h' : I.IsPrincipal] : height I ≤ 1 := by
  rw [height, Order.height]
  simp_all
  intro ltseries relseries

  -- Associated primes, Krull's principal ideal theorem,
