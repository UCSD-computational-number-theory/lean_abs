import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.Basis.Defs

open RingTheory

#check IsRegular

variable {R S M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable (rs : List R)

#check List.length rs

#check Sequence.IsRegular M rs

def depth (I : Ideal R) [Module R M]  : ℕ∞ :=
  {rs : Sequence.IsRegular M rs} 
