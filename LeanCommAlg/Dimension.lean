import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Order.Height
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Order.WithBot
import Mathlib.Order.KrullDimension
import Mathlib.LinearAlgebra.Span.Defs
--import Mathlib.Data.Real.ENNReal

variable {R : Type _} [CommRing R]
variable (I : Ideal R)
variable (P : Ideal R)

#check Ideal.height

-- noncomputable def Ideal.IsPrime.height (p : Ideal R) [hp : p.IsPrime] : WithBot ℕ∞ :=
--   Order.height (⟨p, hp⟩ : PrimeSpectrum R)

-- #check Ideal.IsPrime.height

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

@[simp] lemma height_zero_of_minimal_prime [h : I.IsPrime] :
    I ∈ minimalPrimes R → Ideal.primeHeight I = 0 := by
  intros Imin; rcases Imin with ⟨bot_le_I, y_minimal⟩; simp_all
  by_contra height_neq_0
  rw [Ideal.primeHeight, Order.height] at height_neq_0
  simp [Ideal.primeHeight] at *
  obtain ⟨ltseries, ⟨rel_last, len_neq_0⟩⟩ := height_neq_0
  have head_lt_last : RelSeries.head ltseries < RelSeries.last ltseries := by
    apply RelSeries.rel_of_lt; contrapose! len_neq_0; simp_all
  have head_lt_I : (RelSeries.head ltseries).asIdeal < I := by
    exact gt_of_ge_of_gt rel_last head_lt_last
  have head_le_I : (RelSeries.head ltseries).asIdeal ≤ I := by
    apply le_of_lt head_lt_I
  specialize y_minimal ?_
  . apply (RelSeries.head ltseries).asIdeal
  . exact PrimeSpectrum.isPrime (RelSeries.head ltseries)
  . absurd (y_minimal head_le_I)
    exact not_le_of_lt (head_lt_I)

/-
I think this should be true? If you consider the chain of ideals,
then `J` must contain `I`, and thus have a height of at least `height I`
-/
lemma height_le_prime_of_minimal_prime (J : Ideal R) [hJ : J.IsPrime] [hI : I.IsPrime] :
    J ∈ I.minimalPrimes → I.primeHeight ≤ J.primeHeight := by
  intro Imin; rcases Imin with ⟨I_le_J, _⟩; simp_all
  exact Ideal.primeHeight_mono I_le_J

/-
Krull's Principal Ideal Theorem
- The height of a principl prime ideal is at most 1
-/
theorem height_1_of_principal_of_prime [h : I.IsPrime] [h_principal : I.IsPrincipal] :
    Ideal.primeHeight I ≤ 1 := by
  rw [Ideal.primeHeight]
  rcases h_principal with ⟨span⟩
  simp_all only [Ideal.submodule_span_eq]
  obtain ⟨w, h_1⟩ := span
  subst h_1

  sorry

/-
rad(I) is the intersection of all minimal primes containing I
-/
theorem radical_intersection_minimal_primes (I : Ideal R) :
    I.radical = ⨅ (P : Ideal R) (hP : P ∈ I.minimalPrimes), P := by
  ext x; constructor
  case h.mp =>
    intro x_in_rad
    sorry
  case h.mpr =>
    intro x_in_inter
    simp at x_in_inter
    sorry

theorem kurll_principal_ideal (I : Ideal R) [hI : I.IsPrincipal] (P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    Ideal.height P ≤ 1 := by
      sorry
