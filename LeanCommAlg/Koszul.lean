import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.GradedObject

--import Mathlib.Data.Real.ENNReal

variable {R : Type _} [CommRing R]
variable (I : Ideal R)
variable {M : Type _} [AddCommGroup M]
variable [Module R M]

universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {ι : Type*}
variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]
variable {c : ComplexShape ℕ} (C : HomologicalComplex V c)

noncomputable def zeroObj : V := (HasZeroObject.zero' V).1
#check zeroObj

lemma comp_zero_is_zero : 𝟙 (zeroObj V) ≫ 𝟙 (zeroObj V) = 0 := by
  simp_all
  refine zero_of_target_iso_zero (𝟙 (zeroObj V)) ?_
  rfl

-- the complex 0 → 0 → 0 → 0
noncomputable def trivialComplex : ShortComplex V := {
  X₁ := zeroObj V,
  X₂ := zeroObj V,
  X₃ := zeroObj V,
  f := 𝟙 (zeroObj V),
  g := 𝟙 (zeroObj V),
  zero := comp_zero_is_zero V
}

-- the homological complex
-- 0 → 0 → 0 → 0 → ...
noncomputable def trivialHomologicalComplex : HomologicalComplex V c := {
  X := λ i => zeroObj V,
  d := λ i => 0,
  shape := c,
  d_comp_d' := λ i j k hij hjk => by
    simp_all
}

-- k-th differential of Koszul complex
def d_k [Module.Free R M] (k : ℕ) (s : M →ₗ[R] R) : M →ₗ[R] M :=
  have h : ∃ (S : Set M), Nonempty (Basis (↑S) R M) := by
    apply (Module.free_iff_set R M).mp; assumption
  sorry


def KoszulComplexShape : ComplexShape (ULift ℤ) := {
  Rel     := (fun i j => j.down = i.down + 1),
  next_eq := (fun {i j j'} h h' => by
    simp_all only
    have fwd : ℤ := i.down
    ext : 1
    simp_all only
  ),
  prev_eq := (fun {i i' j} h h' => by simp_all only [add_left_inj, ULift.down_inj])
}

/-
`[Module.Free R M]` is a typeclass that says `M` is free as an `R`-module.
-/
noncomputable def KoszulComplex [Module.Free R M] : HomologicalComplex KoszulComplexShape M :=
  {
    X := (λ i, if i = 0 then M else ExteriorAlgebra R (I ^ i)),
    d := (λ d, d_k I i ),
    shape := sorry
    d_comp_d' := sorry
  }
