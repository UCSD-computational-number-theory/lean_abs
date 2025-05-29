import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.LinearAlgebra.Basis.Defs
--import Mathlib.Algebra.Homology

open RingTheory

variable {R : Type u}
variable {M : Type v}

open CategoryTheory Limits Category ModuleCat


variable [CommRing R] [AddCommGroup M] [Module R M] (C : Type u_2) [Category C] [Abelian C] [Linear R C]
  [EnoughProjectives C] [HasZeroObject C]

variable (I : Ideal R)

variable (rs : List R)

-- Some homology





noncomputable def depth_length (I : Ideal R) (M : Type u_2) [AddCommGroup M] [Module R M] : ℕ∞ :=
  letI := Classical.propDecidable
  if (⊤ : Submodule R M) = ⊥ then ⊤ else
  WithTop.some (⨆(rs : List I), ⨆(_ : Sequence.IsRegular M (rs : List R)), ↑rs.length)

noncomputable def depth_ext (I : Ideal R) (M : Type u_2) [AddCommGroup M] [Module R M] : ℕ :=
  sorry




#check depth_length (⊤ : Ideal R) M -- depth R is the same as depth of maximal ideal
#check ModuleCat.of R M
#check (Ext R C 0).obj
--#check CategoryTheory.Limits.IsZero (((Ext R C 0).obj (Opposite.op (R ⧸ I))).obj M)
def rquot := R ⧸ I

example (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
example (M : ModuleCat.{v} R) : of R M = M := by with_reducible rfl
