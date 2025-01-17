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

  intros Imin
  rcases Imin with ⟨bot_le_I, y_minimal⟩
  simp_all
  by_contra height_neq_0
  rw [height, Order.height] at height_neq_0
  simp [height] at *
  obtain ⟨ltseries, ⟨rel_last, len_neq_0⟩⟩ := height_neq_0
  have len_ge_1 : 1 ≤ ltseries.length := by
    contrapose! len_neq_0; simp_all

  -- have : RelSeries.head ltseries < {⟨I, h⟩} := by
  --   simp_all only [Set.lt_eq_ssubset]
  --   simp_all [RelSeries.head, Set.ssubset_def]
  --   constructor
  --   . case _ =>
  --       intro psr
  --       intro tofun0
  --       sorry
  --   . case _ =>
  --       sorry
  --   -- use rel_last

  have head_le_last : RelSeries.head ltseries < RelSeries.last ltseries := by
    apply RelSeries.rel_of_lt
    exact len_ge_1

  have head_lt_I : RelSeries.head ltseries < ⟨I, h⟩ := by
    apply lt_of_lt_of_le head_le_last rel_last
  have head_le_I : RelSeries.head ltseries ≤ ⟨I, h⟩ := by
    apply le_of_lt head_lt_I
  have head_ideal_le_I_ideal :
      (RelSeries.head ltseries).asIdeal ≤ I := by
    apply head_le_I
  -- have I_le_H : ⟨I, h⟩ ≤ RelSeries.head ltseries := by
  obtain ⟨head_ideal, head_prime⟩ := RelSeries.head ltseries

  have head_ideal_lt_I : head_ideal < I := by
    sorry

  have head_ideal_le_I : head_ideal ≤ I := by
    sorry

  specialize y_minimal ?_
  . apply head_ideal
  . apply head_prime
  . case _ =>

    have I_le_head_ideal : I ≤ head_ideal := by
      apply y_minimal head_ideal_le_I

    absurd I_le_head_ideal
    exact not_le_of_lt head_ideal_lt_I


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
