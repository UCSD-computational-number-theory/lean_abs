import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.DirectSum.Module
--import Mathlib.Algebra.DirectSum.Proj
import Mathlib.RingTheory.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

open Classical Equiv Perm Algebra DirectSum Function

#check Perm

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]

-- semiring / add_comm_group
--variable {M' : Type*} [AddCommGroup M'] [Module R M']
--variable {N' : Type*} [AddCommGroup N'] [Module R N']
variable {ι ι' ι'' : Type*} [Fintype ι]


/-- A symmetric map from `ι → M` to `N` is a multilinear map that is
invariant under permutation of its arguments. -/
structure SymmetricMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is symmetric: for any permutation `e` of `v`, `f v = f e v`. -/
  map_eq_perm' : ∀ (v : ι → M) (e : Perm ι), toFun v = toFun (v ∘ e)

/-- A skew symmetric map from `ι → M` to `N` is a multilinear map that is
invariant under even permutations and changes sign under odd permutations of its arguments. -/
structure SkewSymmetricMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is skew symmetric: for any permutation `e` of `v`, `sgn(e) f v = f e v`. -/
  map_eq_perm_sign' : ∀ (v : ι → M) (e : Perm ι), (Perm.sign e) • toFun v = toFun (v ∘ e)
