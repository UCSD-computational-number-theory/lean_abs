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
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.GradedObject

--import Mathlib.Data.Real.ENNReal
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

infixr:20 "<∘ₗ>" => LinearMap.comp

variable {ι R A M σ : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommRing R] [Semiring A] [Algebra R A]
variable (I : Ideal R)
variable [AddCommGroup M]
variable [Module R M]
-- variable [Module.Finite R M] -- allows you to decompose into the direct sum without trouble

universe v u
variable {ι : Type*}
variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]
-- variable (Rmod : Type u) [Category.{v} Rmod] [HasZeroMorphisms Rmod] [HasZeroObject Rmod]
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

-- Koszul complex

#check ModuleCat R -- category of R-mod

def mulRight (b : A) : A →ₗ[R] A :=
{ toFun := λ a => a * b,
  map_add' := λ x y => by exact RightDistribClass.right_distrib x y b,
  map_smul' := λ m x => by exact smul_mul_assoc m x b }

--lemma linear_of_ext_mul
@[simp] def ext_mul_a' (a : M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  mulRight (ExteriorAlgebra.ι R a)

#check ⋀[R]^2 M

@[simp] noncomputable def ext_inclusion (i : ℕ) : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M :=
  (⋀[R]^i M).subtype

@[simp] noncomputable def ext_proj (i : ℕ) : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M := {
  toFun := fun a => ((ExteriorAlgebra.GradedAlgebra.liftι R M) a) i,
  map_add' := λ x y => by simp,
  map_smul' := λ m x => by simp; rfl
}

@[simp] noncomputable def diff_map (i j : ℕ) (a : M) : ⋀[R]^i M →ₗ[R] ⋀[R]^j M :=
  (ext_proj j) ∘ₗ (ext_mul_a' a) ∘ₗ (ext_inclusion i)


-- def KoszulComplexShape : ComplexShape ℕ := {
--   Rel     := (fun i j => j = i + 1),
--   next_eq := (fun {i j j'} h h' => by subst h h'; rfl  ),
--   prev_eq := (fun {i i' j} h h' => by subst h; exact Nat.succ_inj'.mp h')
-- }

-- abbrev kcs := KoszulComplexShape

noncomputable def KoszulComplex (a : M) [Module R M] : CochainComplex (ModuleCat R) ℕ := {
  X := (fun i => ModuleCat.of R (⋀[R]^i M)),
  d := λ i j => if j == i + 1 then ModuleCat.ofHom (diff_map i j a) else 0,
  shape := fun i j h => by
    simp_all; intro h'
    exact False.elim (h (id (Eq.symm h'))),
  d_comp_d' := by
    intro i j k hij hjk
    rw [← ExteriorAlgebra.ι_sq_zero a]



    sorry
}
