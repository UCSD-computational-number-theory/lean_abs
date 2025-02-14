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


noncomputable def depth_length (I : Ideal R) (M : Type u_2) [AddCommGroup M] [Module R M] [AddCommGroup N] : ℕ∞ :=
  letI := Classical.propDecidable
  if (⊤ : Submodule R M) = ⊥ then ⊤ else
  WithTop.some (⨆(rs : List I), ⨆(_ : Sequence.IsRegular M (rs : List R)), ↑rs.length)

noncomputable def depth_ext (I : Ideal R) (M : Type u_2) [AddCommGroup M] [Module R M] : ℕ∞ :=
  sorry

#check depth_length (⊤ : Ideal R) M -- depth R is the same as depth of maximal ideal
