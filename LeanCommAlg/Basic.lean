import Mathlib.AlgebraicGeometry.PrimeSpectrum.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Span.Defs
--import Mathlib.Data.Real.ENNReal

variable {R : Type _} [CommRing R]

variable (I : Ideal R)

#check Ideal.IsPrime

noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
  Order.height (λ _ : PrimeSpectrum R => I)

#check height

--noncomputable def height [h : IsPrime I] : WithBot ℕ∞ :=
  --Order.height (PrimeSpectrum R) (I : PrimeSpectrum R)


theorem height_1_of_principal_of_prime [h : I.IsPrime] [h' : I.IsPrincipal] : height I ≤ 1 := by
  rw [height, Order.height]

  -- Associated primes, Krull's principal ideal theorem, 
