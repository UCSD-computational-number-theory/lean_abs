import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime

variable {R : Type _} [CommRing R]
variable (I : Ideal R)

#check Submodule.eq_smul_of_le_smul_of_le_jacobson

