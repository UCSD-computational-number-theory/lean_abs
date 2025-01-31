import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ComplexShape
--import Mathlib.Data.Real.ENNReal

variable {R : Type _} [CommRing R]
variable (I : Ideal R)
variable {M : Type _} [AddCommGroup M]
variable [Module R M]

-- k-th differential of Koszul complex
def d_k [Module.Free R M] (k : ℕ) (s : M →ₗ[R] R) : M →ₗ[R] M :=
  have h : ∃ (S : Set M), Nonempty (Basis (↑S) R M) := by
    apply (Module.free_iff_set R M).mp; assumption
  sorry
