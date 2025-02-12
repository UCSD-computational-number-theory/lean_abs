import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.Basis.Defs

open RingTheory

#check IsRegular

variable {R S M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable (rs : List R)

noncomputable def depth (I : Ideal R) [Module R M] : ℕ :=
  ⨆(rs : List R), ⨆(_ : Sequence.IsRegular M rs), rs.length


def list_I_to_R {R : Type*} [CommRing R] (I : Ideal R) (L : List I) : List R :=
  (L : List R)
