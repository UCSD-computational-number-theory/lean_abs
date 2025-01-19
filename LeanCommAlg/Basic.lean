import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
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

-- noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
--   Order.height {J : PrimeSpectrum R | J.asIdeal ≤ I}


noncomputable def height (p : Ideal R) [hp : p.IsPrime] : WithBot ℕ∞ :=
  let ps : PrimeSpectrum R := ⟨p, hp⟩
  Order.height ps

-- noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
--   Order.height (fun _ : PrimeSpectrum R => I)

#check height

@[simp] lemma singleton_of_minimal_prime [h : I.IsPrime] :
    I ∈ minimalPrimes R → {J : PrimeSpectrum R | J.asIdeal ≤ I} = {⟨I, h⟩} := by
  intro hmin
  rcases hmin with ⟨hl, hr⟩
  dsimp at hr
  ext J
  simp [PrimeSpectrum.ext_iff]
  constructor
  . intro hJ
    specialize hr ⟨J.2, bot_le⟩
    have : I ≤ J.asIdeal := by
      apply hr hJ
    apply le_antisymm hJ this
  . intro hJ
    apply le_iff_lt_or_eq.mpr; right; apply hJ

@[simp] theorem minimal_prime_is_min_over_I
    (I P : Ideal R) (hP : P ∈ Ideal.minimalPrimes I) :
    ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q ≤ P → Q = P := by
  rw [Ideal.minimalPrimes] at hP
  rcases hP with ⟨hPPrime, hPMinimal⟩
  intro Q a IQ QP
  simp_all
  ext x; constructor
  · intro xQ; apply QP xQ
  · intro xP; exact hPMinimal a IQ QP xP

lemma height_zero_of_minimal_prime [h : I.IsPrime] :
    I ∈ minimalPrimes R → height I = 0 := by
  intros Imin; rcases Imin with ⟨bot_le_I, y_minimal⟩; simp_all
  by_contra height_neq_0
  rw [height, Order.height] at height_neq_0
  simp [height] at *
  obtain ⟨ltseries, ⟨rel_last, len_neq_0⟩⟩ := height_neq_0
  have head_le_last : RelSeries.head ltseries < RelSeries.last ltseries := by
    apply RelSeries.rel_of_lt; contrapose! len_neq_0; simp_all
  have head_lt_I : (RelSeries.head ltseries).asIdeal < I := by
    exact gt_of_ge_of_gt rel_last head_le_last
  have head_le_I : (RelSeries.head ltseries).asIdeal ≤ I := by
    apply le_of_lt head_lt_I
  specialize y_minimal ?_
  . apply (RelSeries.head ltseries).asIdeal
  . exact PrimeSpectrum.isPrime (RelSeries.head ltseries)
  . absurd (y_minimal head_le_I)
    exact not_le_of_lt (head_lt_I)

/-
I think this should be true? If you consider the chain of ideals, then `J` must contain `I`, and thus have a height of at least `height I`
-/
lemma height_le_prime_of_minimal_prime (J : Ideal R) [hJ : J.IsPrime] [hI : I.IsPrime] :
    J ∈ I.minimalPrimes → height I ≤ height J  := by
  intro hmin
  sorry

theorem height_1_of_principal_of_prime [h : I.IsPrime] [h' : I.IsPrincipal] : height I ≤ 1 := by
  rw [height, Order.height]
  simp_all
  intro ltseries relseries
  sorry
  -- Associated primes, Krull's principal ideal theorem,
