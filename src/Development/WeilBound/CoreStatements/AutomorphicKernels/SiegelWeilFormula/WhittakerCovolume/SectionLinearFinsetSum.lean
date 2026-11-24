module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lin_addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

theorem lin_holValueAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (h : ι → ℂ → ℂ) (v : ι → ℂ) (s₀ : ℂ)
    (hh : ∀ i ∈ s, HolValueAt (h i) s₀ (v i)) :
    HolValueAt (fun z => ∑ i ∈ s, c i * h i z) s₀ (∑ i ∈ s, c i * v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((holValueAt_const (c j) s₀).mul (hh j (Finset.mem_insert_self j s))).add
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

section SDl

variable (d : SD σ)

def linRhoL (v : Mx F E d.m d.n) : d.Fn →ₗ[ℂ] d.Fn where
  toFun := d.dd.rho d.B.ψ (v * (incM F d.b.1.toCols₂)ᵀ)
  map_add' Φ Ψ := by
    funext y
    simp only [Darboux.rho, schr, Pi.add_apply]
    ring
  map_smul' a Φ := by
    funext y
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lin_T_eq (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T Φ X = d.l (linRhoL d X Φ) := rfl

end SDl

end PositivityTheory.SiegelWeilFormula.KWhit

end
