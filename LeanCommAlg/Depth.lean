import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.Basis.Defs

open RingTheory

variable {R : Type u_1}
variable {M : Type u_2}

variable [CommRing R] [AddCommGroup M] [Module R M]
variable (I : Ideal R)

variable (rs : List R)

noncomputable def depth (I : Ideal R) (M : Type u_2) [AddCommGroup M] [Module R M] : ℕ∞ :=
  WithTop.some (⨆(rs : List I), ⨆(_ : Sequence.IsRegular M (rs : List R)), ↑rs.length)

--theorem auslander_buchsbaum_formula [IsLocalRing R] :

#check depth (⊤ : Ideal R) M -- depth R is the same as depth of maximal ideal
