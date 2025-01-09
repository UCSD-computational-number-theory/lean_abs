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

noncomputable def height [h : I.IsPrime] : WithBot ℕ∞ :=
  Order.height {J : PrimeSpectrum R | J.asIdeal ≤ I}

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
  intro hmin
  rw [height, Order.height]
  simp_all
  intros lt hy
  rw [RelSeries.length_eq_zero]
  . case _ =>
    intro set₁ h₁ set₂ h₂
    simp_all
    specialize hy ⟨I, h⟩
    apply Set.ext
    have this : {J : PrimeSpectrum R | J.asIdeal ≤ I} = {⟨I, h⟩} := singleton_of_minimal_prime I hmin
    have set₁unique : set₁ = {⟨I, h⟩} := by
      sorry
    have set₂unique : set₂ = {⟨I, h⟩} := by
      sorry
    simp [set₁unique, set₂unique]
  . case _ =>
    intro prime_spectrum_set h
    rcases h with ⟨h1, h2⟩
    contradiction

#check IsMin

#check I

lemma height_zero_of_minimal_prime' [h : I.IsPrime] :
    I ∈ minimalPrimes R → height I = 0 := by

  intros Imin
  rcases Imin with ⟨bot_le_I, y_minimal⟩
  simp_all
  by_contra height_neq_0
  simp [height] at *
  -- have : {J : PrimeSpectrum R | J.asIdeal ≤ I} ≠ ∅ := by
  --   intro h
  --   apply height_neq_0
  --   exact h
  have nonempty_m : Nonempty {J : PrimeSpectrum R | J.asIdeal ≤ I} := by
    exact Set.nonempty_iff_ne_empty'.mpr height_neq_0
  let J := Classical.choice nonempty_m
  apply Nonempty.elim nonempty_m
  simp; intro a
  sorry

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
