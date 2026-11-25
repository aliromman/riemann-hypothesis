module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.FinExtIntegers

theorem dvr_complete : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l), ∃ _ : IsDiscreteValuationRing ↥(OL LL), IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro l _ LL
  unfold OL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsScalarTower ℤ_[l] ℚ_[l] ↥LL.1 := inferInstance
  have hfin : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : FaithfulSMul ℤ_[l] ↥LL.1 := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥LL.1
  have hdvr : IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥LL.1) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥LL.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥LL.1
  refine ⟨hdvr, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _, ?_⟩
  intro hu
  have hl : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  apply hl
  apply (isUnit_map_iff (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) _).mp
  simpa using hu

end GlobalTheory.FinExtIntegers
