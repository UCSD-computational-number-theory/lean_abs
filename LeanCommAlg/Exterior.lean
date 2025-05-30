import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.TensorPower.Pairing
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Order.Extension.Well

open Classical

infixr:20 "<∘ₗ>" => LinearMap.comp

variable {A : Type*} [Semiring A]
variable {R : Type*} [CommRing R] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M]

open ExteriorAlgebra CategoryTheory

-- Self-duality of the Koszul Complex
variable {E : Type*} [AddCommGroup E] [Module R E] [Module.Finite R E]
variable [ CommMonoid (ExteriorAlgebra R E)]

-- dual
-- abstract
-- standard koszul complex

-- [ ] ⋀[R]^i E ≃ free_module (Nat.choose rank_E i)
-- [X] Module.Dual R (free_module n) ≃ free_module n
-- [X] n choose i = n choose (n - i)

-- The linear map from the exterior power of the dual to the dual of the exterior power.
#check exteriorPower.pairingDual

noncomputable def dual_free_iso_free :
    Module.Dual R (Fin n → R) ≃ₗ[R] (Fin n → R) := by
  exact LinearEquiv.piRing R R (Fin n) R

namespace TensorPower
/--
Takes n linear functionals to construct a new linear functional that acts on
pure tensor.
-/
noncomputable def linearFormOfFamily (f : (_ : Fin n) → Module.Dual R M) :
    Module.Dual R (TensorPower R n M) :=
  PiTensorProduct.lift (MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) f)

-- the above theorem is this in the new(er) version
#check TensorPower.multilinearMapToDual


#check multilinearMapToDual_apply_tprod
open BigOperators in
@[simp]
theorem linearFormOfFamily_apply_tprod (f : (_ : Fin n) → (M →ₗ[R] R)) (v : Fin n → M) :
    linearFormOfFamily f (PiTensorProduct.tprod R v) = ∏ i, (f i (v i)) := by
  unfold linearFormOfFamily
  simp_all only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply,
    smul_eq_mul, _root_.mul_one]

end TensorPower

-- i think this is equal? not sure
#check exteriorPower.alternatingMapToDual
noncomputable def linearFormOfFamily {n : ℕ} (f : (_ : Fin n) → (Module.Dual R M)) :
    Module.Dual R (⋀[R]^n M) :=
  (TensorPower.multilinearMapToDual R M n f) ∘ₗ (exteriorPower.toTensorPower R M n)

@[simp]
lemma linearFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (x : ⋀[R]^n M) :
    linearFormOfFamily f x = TensorPower.linearFormOfFamily f (exteriorPower.toTensorPower R M n x) :=
  rfl

#check exteriorPower.toTensorPower_apply_ιMulti
lemma linearFormOfFamily_apply_ιMulti (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    linearFormOfFamily f (exteriorPower.ιMulti R n m) =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, f i (m (σ i)) := by
  simp_all only [linearFormOfFamily_apply, exteriorPower.toTensorPower_apply_ιMulti, map_sum, map_zsmul_unit,
    TensorPower.linearFormOfFamily_apply_tprod]


/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearFormOfFamily` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def linearFormOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) : ⋀[R]^n M →ₗ[R] R :=
  linearFormOfFamily (fun i ↦ b.coord (Finset.orderIsoOfFin s hs i))

@[simp]
lemma linearFormOfBasis_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) (v : Fin n → M) :
    linearFormOfBasis b hs (exteriorPower.ιMulti R n v) = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
    ∏ i, b.coord (Finset.orderIsoOfFin s hs i) (v (σ i)) := by
  unfold linearFormOfBasis
  rw [linearFormOfFamily_apply, exteriorPower.toTensorPower_apply_ιMulti, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod]


/-! ### Freeness and dimension of `⋀[R]^n M. -/

lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) := by
  -- linearIndependent_of_dualFamily _ (fun s ↦ linearFormOfBasis R n b s.2)
  -- (fun ⟨_, _⟩ ⟨_, _⟩ hst ↦ by
  --   rw [ne_eq, Subtype.mk.injEq] at hst
  --   exact linearFormOfBasis_apply_nondiag _ _ _ _ _ hst)
  -- (fun ⟨_, _⟩ ↦ linearFormOfBasis_apply_diag _ _ _ _)
  sorry

noncomputable def basisExteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R (⋀[R]^n M) := by

  -- Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    -- (eq_top_iff.mp <| span_top_of_span_top' R n (Basis.span_eq b))
  sorry

-- variable

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [hfree : Module.Free R M] : Module.Free R (⋀[R]^n M) := by
  have ⟨I, b⟩ := hfree.exists_basis
  -- letI : LinearOrder I := IsWellFounded.wellOrderExtension (@WellFoundedRelation.emptyWf I)

  letI : LinearOrder I := by
    apply IsWellFounded.wellOrderExtension emptyWf.rel


  apply Module.Free.of_basis (basisExteriorPower b)



variable [StrongRankCondition R]

set_option linter.unusedTactic false
#check Module.finrank_eq_card_basis'

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [hfree : Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) = Nat.choose (Module.finrank R M) n := by
  -- have : IsWellFounded ((Module.Free.ChooseBasisIndex R M)) (@emptyWf.wf (Module.Free.ChooseBasisIndex R M)) := by

  -- letI : LinearOrder hfree.ChooseBasisIndex := by
    -- apply IsWellFounded.wellOrderExtension (@emptyWf.wf (Module.Free.ChooseBasisIndex R M))




  have ⟨I, b⟩ := hfree.exists_basis
  letI lin : LinearOrder I := by sorry
  let B := @basisExteriorPower R _ M _ _ n I lin b
  rw [Module.finrank_eq_card_basis hfree.chooseBasis]


  haveI : Fintype {s : Finset I // s.card = n} := sorry
  rw [Module.finrank_eq_card_basis B]
  rw [← Fintype.card_finset_len]


  sorry



instance ExteriorAlgebraFinite [E_finite : Module.Finite R E] :
    Module.Finite R (ExteriorAlgebra R E) := by
  refine Module.finite_def.mpr ?_
  refine Submodule.fg_def.mpr ?_

  sorry

-- If [Module.Finite R M], then [Module.Finite R (⋀[R]^i M)]
instance exterior_power_finite (i : ℕ) [E_finite : Module.Finite R E] :
    Module.Finite R (⋀[R]^i E) := by
  obtain ⟨⟨E_gen, E_gen_span⟩⟩ := E_finite
  -- Then any tensor power ⊗[R]^i M is finite


  -- finite means there is a Finset that spans the module M
  apply Module.Finite.iff_fg.mpr
  refine Submodule.fg_iff_exists_fin_generating_family.mpr ?_
  use i
  rw [← ιMulti_span_fixedDegree]

  sorry

-- Conrad Theorem 4.1
-- If M has a d-element spanning set for d ≥ 1, then ⋀[R]^k Rᵈ = 0 for k > d
theorem zero_iff_less_generators (d : ℕ) (h : d ≥ 1) (k : ℕ) (hk : k > d) :
    ⋀[R]^k (Fin d → R) = 0 := by


  sorry


-- -- if `R^n` is a free R-Module, then `⋀[R] R^n` is also a free R-Module
-- #check exteriorPower.ιMulti_span
-- #check exteriorPower.ιMulti
-- #check exteriorPower.ιMulti_span_fixedDegree
-- theorem exteriorAlgebra_free :
--     Module.Free R (ExteriorAlgebra R (Fin n → R)) := by
--   let b : Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
--   apply @Module.Free.of_basis R _ _ _ _ ℕ
--   refine { repr := ?_ }

--   sorry

-- -- if `R^n` is a free R-Module, then `⋀[R]^i R^n` is also a free R-Module
-- theorem exteriorPower_free (n i : ℕ) :
--     Module.Free R (⋀[R]^i (Fin n → R)) := by
--   let b : Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
--   apply @Module.Free.of_basis R _ _ _ _ (Fin n)
--   rw [← exteriorPower.ιMulti_span_fixedDegree]
--   sorry

-- -- then we have a basis for `⋀[R]^i R^n`
-- noncomputable def exteriorBasis (i n : ℕ) :
--     Basis (Fin (Nat.choose n i)) R (ExteriorAlgebra.exteriorPower R i (Fin n → R)) := by
--   sorry

-- theorem ext_square_span :
--     Module.rank R (⋀[R]^2 (Fin 3 → R)) = 3 := by
--   have fin_basis : Basis (Fin 3) R (Fin 3 → R) := Pi.basisFun R (Fin 3)
--   -- wts fin_basis = {e_1, e_2, e_3}
--   -- the basis of the exterior power is {e_1 ∧ e_2, e_1 ∧ e_3, e_2 ∧ e_3}

--   sorry

-- -- Aluffi Chapter 8, Lemma 4.3
-- noncomputable def exterior_power_Rn_free (n i : ℕ) (h : i ≤ n) :
--     (⋀[R]^i (Fin n → R)) ≃ₗ[R] (Fin (n.choose i) → R) := by
--   have b_ni : Basis (Fin (n.choose i)) R (Fin (n.choose i) → R) := Pi.basisFun R (Fin (n.choose i))
--   have eq : ⋀[R]^0 (Fin n → R) ≃ₗ[R] R := exteriorPower.zeroEquiv R (Fin n → R)
--   have free_nCi : Module.Free R (Fin (n.choose i) → R) := Module.Free.of_basis b_ni


--   sorry

-- def k : ℕ := sorry
-- def n : ℕ := sorry
-- #check @exteriorPower.alternatingMapLinearEquiv R _ k (Fin n → R) (Fin (Nat.choose n k) → R) _ _ _ _

-- variable [Fintype (Fin k → R)] [DecidableEq (Fin k → R)] [Module R (Fin k → R)]

-- @[simp]
-- lemma choose_symm (n i : ℕ) (h : i ≤ n) :
--     Nat.choose n i = Nat.choose n (n - i) := Eq.symm (Nat.choose_symm h)
