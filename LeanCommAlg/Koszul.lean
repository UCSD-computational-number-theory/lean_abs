import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.GradedObject

--import Mathlib.Data.Real.ENNReal
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι R A M σ : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommRing R] [Semiring A] [Algebra R A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
variable (I : Ideal R)
variable [AddCommGroup M]
variable [Module R M]

universe v u
variable {ι : Type*}
variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]
variable {c : ComplexShape ℤ}


noncomputable def zeroObj : V := (HasZeroObject.zero' V).1
#check zeroObj
#check ExteriorAlgebra.gradedAlgebra R M
#check ExteriorAlgebra R M
#check (ExteriorAlgebra.ι R)
#check (ExteriorAlgebra.ιMulti R) 1
#check DirectSum.lof
#check DirectSum.toModule

/-
theorem mul_alternating :

-/

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
  shape := by
    intro i j a
    simp_all only [Pi.zero_apply],
  d_comp_d' := λ i j k hij hjk => by
    simp_all
}

open ExteriorAlgebra

--lemma linear_of_ext_mul

def mul_a (a : M) : ExteriorAlgebra R M → ExteriorAlgebra R M :=
  --include a into ExteriorAlgebra, then apply the multiplication
  --fun m => m * a
  sorry

noncomputable def ext_inclusion (i : ℕ) : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M :=
  sorry

noncomputable def ext_proj (i : ℕ) : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M :=
  sorry

noncomputable def ext_mul_a (a : M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  { toFun := mul_a a
    map_add' := fun x y => sorry
    map_smul' := fun r x => sorry}

noncomputable def diff_map (i : ℕ) (a : M) : ⋀[R]^i M →ₗ[R] ⋀[R]^(i+1) M :=
  ((ext_proj (i+1)).comp (ext_mul_a a)).comp (ext_inclusion i)



def KoszulComplexShape : ComplexShape ℤ := {
  Rel     := (fun i j => j = i + 1),
  next_eq := (fun {i j j'} h h' => by subst h h'; rfl  ),
  prev_eq := (fun {i i' j} h h' => by subst h; exact (Int.add_left_inj 1).mp h')
}
abbrev kcs := KoszulComplexShape

/-
`[Module.Free R M]` is a typeclass that says `M` is free as an `R`-module.
-/
noncomputable def KoszulComplex [Module R M] : CochainComplex V ℤ :=
  {
    X := (fun i => sorry),
    d := (fun d => sorry),
    shape := sorry
    d_comp_d' := sorry
  }
