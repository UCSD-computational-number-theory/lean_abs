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

variable {ι σ : Type*} [DecidableEq ι] [AddMonoid ι]
variable {A : Type*} [Semiring A]
variable {R : Type*} [CommRing R] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M]

universe v u
variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

noncomputable def zeroObj : V := (HasZeroObject.zero' V).1
#check zeroObj
#check ExteriorAlgebra.gradedAlgebra R M
#check ExteriorAlgebra R M
#check (ExteriorAlgebra.ι R)
#check (ExteriorAlgebra.ιMulti R) 1
#check DirectSum.lof
#check DirectSum.toModule


lemma comp_zero_is_zero : 𝟙 (zeroObj V) ≫ 𝟙 (zeroObj V) = 0 := by
  simp; exact zero_of_target_iso_zero (𝟙 (zeroObj V)) (by rfl)

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
  shape := by intros; simp_all only [Pi.zero_apply],
  d_comp_d' := λ i j k hij hjk => by simp_all
}

open ExteriorAlgebra

-- Koszul complex

#check ModuleCat R -- category of R-mod
open ModuleCat

def mulRight (b : A) : A →ₗ[R] A :=
{ toFun := λ a => a * b,
  map_add' := λ x y => by exact RightDistribClass.right_distrib x y b,
  map_smul' := λ m x => by exact smul_mul_assoc m x b }

--lemma linear_of_ext_mul
def ext_mul_a' (a : M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  mulRight (ExteriorAlgebra.ι R a)

#check ⋀[R]^2 M

noncomputable def ext_inclusion (i : ℕ) : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M :=
  (⋀[R]^i M).subtype

variable (fds : ExteriorAlgebra R M)
#check ((ExteriorAlgebra.gradedAlgebra R M).decompose' fds 1)

-- no clue why this is needed, but it makes it work
variable [NonUnitalSemiring (DirectSum ℕ fun i ↦ ↥(⋀[R]^i M))]
noncomputable def ext_proj (i : ℕ) : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M := {
  toFun := fun a => (
    (ExteriorAlgebra.gradedAlgebra R M).decompose' a) i,
  map_add' := λ x y => by simp,
  map_smul' := λ m x => by
    simp_all only [DirectSum.Decomposition.decompose'_eq, DirectSum.decompose_smul, RingHom.id_apply]
    rfl
}
omit [NonUnitalSemiring (DirectSum ℕ fun i ↦ ↥(⋀[R]^i M))]

noncomputable def diff_map (i j : ℕ) (a : M) : ⋀[R]^i M →ₗ[R] ⋀[R]^j M :=
  (ext_proj j) ∘ₗ (ext_mul_a' a) ∘ₗ (ext_inclusion i)

lemma ext_power_0_is_base : (⋀[R]^0 M) = Submodule.span R {1} := by
  simp_all; exact Submodule.one_eq_span

lemma ext_power_1_is_self : (⋀[R]^1 M) = Submodule.span R (Set.range (ExteriorAlgebra.ι R)) := by
  simp_all
  ext x; constructor;
  . rintro ⟨_, h⟩; subst h
    apply (SetLike.mem_of_subset Submodule.subset_span ?_)
    simp_all only [Set.mem_range, ι_inj, exists_eq]
  . intro hx
    simp_all [Submodule.span, Set.range]
    exact LinearMap.mem_range.mp (hx (LinearMap.range (ι R)) fun ⦃a⦄ a ↦ a)

@[simp] lemma ext_mul_a'_comp_zero (a : M) :
    (ext_mul_a' a) ∘ₗ (ext_mul_a' a) = (0 : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M) := by
  rw [ext_mul_a', mulRight]; apply LinearMap.ext
  intro x
  simp_all only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, LinearMap.zero_apply]
  rw [mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]

-- this is probably will not be used
lemma proj_incl_comp_id (i : ℕ) :
    (ext_proj i : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M) ∘ₗ (ext_inclusion i : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp_all only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  simp [ext_inclusion, ext_proj]

@[simp] lemma incl_proj_comp_id' (i : ℕ) (x : ⋀[R]^i M) :
    ext_inclusion i (ext_proj i (x : ExteriorAlgebra R M)) = x := by
  simp_all [ext_inclusion, ext_proj]

-- this is required for the proof to work
lemma incl_proj_comp_id (i : ℕ) :
    (ext_inclusion i : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M) ∘ₗ (ext_proj i : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M) = LinearMap.id := by

  apply LinearMap.ext; intro x
  rw [LinearMap.comp_apply (ext_inclusion i) (ext_proj i) x]
  simp_all only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  unfold ext_inclusion ext_proj
  apply DirectSum.decompose_of_mem_same (fun i ↦ ⋀[R]^i M) ?_
  simp_all

  sorry


theorem koszul_d_squared_zero (i : ℕ) (m : M) :
    (diff_map (i + 1) (i + 2) m) ∘ₗ (diff_map i (i + 1) m) = (0 : ⋀[R]^i M →ₗ[R] ⋀[R]^(i + 2) M) := by
  simp [diff_map]

  generalize p1 : (ext_proj (R := R) (M := M) (i + 1)) = proj1
  generalize p2 : (ext_proj (R := R) (M := M) (i + 2)) = proj2
  generalize ma : (ext_mul_a' (R := R) (M := M) m) = mula
  generalize i0 : (ext_inclusion (R := R) (M := M) i) = incl0
  generalize i1 : (ext_inclusion (R := R) (M := M) (i + 1)) = incl1

  have : (proj2 ∘ₗ mula ∘ₗ incl1) ∘ₗ proj1 ∘ₗ mula ∘ₗ incl0
        = proj2 ∘ₗ mula ∘ₗ (incl1 ∘ₗ proj1) ∘ₗ mula ∘ₗ incl0 := LinearMap.comp_assoc _ _ _
  rw [this, ← i1, ← p1]


  -- doing an ext proof is really annoying, so I tried avoiding it by showing the
  -- composition is a linear map
  -- however, i dont think it works because the map from ith power to ExtAlg to ith power is weird
  -- this might be because of how `ext_inclusion` is defined.

  -- apply LinearMap.ext; intro x
  -- simp
  -- generalize consume : (mula (incl0 x)) = cons
  -- rw [incl_proj_comp_id' (i + 1) cons]


  simp [incl_proj_comp_id (i + 1)]
  have : proj2 ∘ₗ mula ∘ₗ mula ∘ₗ incl0 = proj2 ∘ₗ (mula ∘ₗ mula) ∘ₗ incl0 := LinearMap.comp_assoc _ _ _
  rw [this, ← ma, ext_mul_a'_comp_zero, LinearMap.zero_comp, LinearMap.comp_zero]


noncomputable def KoszulComplex (a : M) [Module R M] : CochainComplex (ModuleCat R) ℕ := {
  X := (fun i => of R (⋀[R]^i M)),
  d := fun i j => if i + 1 == j then ofHom (diff_map i j a) else 0,
  shape := fun i j h => by simp_all,
  d_comp_d' := by
    intro i _ _ hij hjk
    simp at hij hjk; subst hij hjk; simp
    have conv (j : ℕ) (a : ⋀[R]^j M →ₗ[R] ⋀[R]^(j + 1) M) (b : ⋀[R]^(j + 1) M →ₗ[R] ⋀[R]^(j + 2) M) :
        ofHom a ≫ ofHom b = ofHom (b ∘ₗ a) := rfl
    rw [conv]
    have : i + 1 + 1 = i + 2 := rfl; rw [this]; clear this
    rw [koszul_d_squared_zero i a]
    rfl
}
