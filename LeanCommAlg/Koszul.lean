import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Functor.Hom

infixr:20 "<∘ₗ>" => LinearMap.comp

variable {A : Type*} [Semiring A]
variable {R : Type*} [CommRing R] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- Koszul Complex

#check ModuleCat R -- category of R-mod
open ModuleCat ExteriorAlgebra CategoryTheory

def mulRight (b : A) : A →ₗ[R] A :=
{ toFun := λ a => a * b,
  map_add' := λ x y => by exact RightDistribClass.right_distrib x y b,
  map_smul' := λ m x => by exact smul_mul_assoc m x b }

--lemma linear_of_ext_mul
def ext_mul_a (a : M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  mulRight (ExteriorAlgebra.ι R a)

#check ⋀[R]^2 M

def ext_inclusion (i : ℕ) : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M :=
  (⋀[R]^i M).subtype

def ext_proj (i : ℕ) : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M := {
  toFun := fun a => (
    (ExteriorAlgebra.gradedAlgebra R M).decompose' a) i,
  map_add' := λ x y => by simp,
  map_smul' := λ m x => by
    simp_all only [DirectSum.Decomposition.decompose'_eq, DirectSum.decompose_smul, RingHom.id_apply]
    rfl
}

def diff_map (i j : ℕ) (a : M) : ⋀[R]^i M →ₗ[R] ⋀[R]^j M :=
  (ext_proj j) ∘ₗ (ext_mul_a a) ∘ₗ (ext_inclusion i)

@[simp] lemma ext_mul_a_comp_zero (a : M) :
    (ext_mul_a a) ∘ₗ (ext_mul_a a) = (0 : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M) := by
  rw [ext_mul_a, mulRight]; apply LinearMap.ext
  intro x
  simp_all only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, LinearMap.zero_apply]
  rw [mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]

lemma proj_incl_comp_id (i : ℕ) :
    (ext_proj i : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M) ∘ₗ (ext_inclusion i : ⋀[R]^i M →ₗ[R] ExteriorAlgebra R M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp_all only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  simp [ext_inclusion, ext_proj]

lemma incl_proj_comp_preserves {i : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ (⋀[R]^i M)) :
    ext_inclusion i (ext_proj i x) = x := by
  dsimp [ext_inclusion, ext_proj]
  exact DirectSum.decompose_of_mem_same _ hx

lemma ext_mul_a_inc_grade (i : ℕ) (x : ⋀[R]^i M) :
    (ext_mul_a m) (x : ExteriorAlgebra R M) ∈ (⋀[R]^(i + 1) M) := by
  dsimp [ext_mul_a, mulRight]
  obtain ⟨_, hx⟩ := x
  apply (ExteriorAlgebra.gradedAlgebra R M).mul_mem hx ?_
  simp_all only [pow_one, LinearMap.mem_range, ι_inj, exists_eq]

lemma ext_mul_graded (hx : x ∈ ⋀[R]^i M) (hy : y ∈ ⋀[R]^j M) :
    (x * y : ExteriorAlgebra R M) ∈ ⋀[R]^(i + j) M :=
  (ExteriorAlgebra.gradedAlgebra R M).mul_mem hx hy

theorem koszul_d_squared_zero (i : ℕ) (m : M) :
    (diff_map (i + 1) (i + 2) m) ∘ₗ (diff_map i (i + 1) m) = (0 : ⋀[R]^i M →ₗ[R] ⋀[R]^(i + 2) M) := by
  simp [diff_map]
  apply LinearMap.ext; intro x
  simp [LinearMap.comp_apply]
  have pres : (ext_mul_a m) (x : ExteriorAlgebra R M) ∈ (⋀[R]^(i + 1) M) := ext_mul_a_inc_grade i x
  rw [incl_proj_comp_preserves]
  have sq_zero (y : ExteriorAlgebra R M) :
      (ext_mul_a m ((ext_mul_a m) y)) = (0 : ExteriorAlgebra R M) := by
    simp_all [ext_mul_a, mulRight]
    rw [mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]
  simp_all only [map_zero]
  exact pres

def KoszulComplex (a : M) [Module R M] : CochainComplex (ModuleCat R) ℕ := {
  X := (fun i => of R (⋀[R]^i M)),
  d := fun i j => if i + 1 == j then ofHom (diff_map i j a) else 0,
  shape := fun i j h => by simp_all,
  d_comp_d' := by
    intro i _ _ hij hjk
    simp at hij hjk; subst hij hjk; simp
    rw [← @ofHom_comp]
    have : i + 1 + 1 = i + 2 := rfl; rw [this];
    rw [koszul_d_squared_zero i a]
    rfl
}

-- Self-duality of the Koszul Complex
variable {E : Type*} [AddCommGroup E] [Module R E] [Module.Free R E] [Module.Finite R E]
variable [ CommMonoid (ExteriorAlgebra R E)]

#check Module.Dual R (⋀[R]^2 E)
#check (Module.Free R E)
#check exteriorPower.zeroEquiv
#check exteriorPower.oneEquiv

def DualKoszulComplex (e : E) : ChainComplex (ModuleCat R) ℕ := {
  X := fun i => of R (Module.Dual R (⋀[R]^i E)),
  d := fun i j => if j + 1 == i then @ofHom R _ _ _ _ _ _ _ (LinearMap.dualMap (diff_map j i e)) else 0,
  shape := fun i j h => by simp_all,
  d_comp_d' := by
    intro _ _ k hij hjk
    simp at hij hjk; subst hij hjk; simp
    rw [← @ofHom_comp]
    have : k + 1 + 1 = k + 2 := rfl; rw [this]; clear this
    rw [LinearMap.dualMap_comp_dualMap, koszul_d_squared_zero k e]
    rw [LinearMap.dualMap_eq_lcomp, LinearMap.lcomp, LinearMap.comp_zero]
    rfl
}
