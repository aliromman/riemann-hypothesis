module

public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.FinPl
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

def intV (D : D7) (v : Pl D) : AddSubgroup (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers D.host.F, ∃ x : 𝓞 D.host.E, y = a ⊗ₜ[D.host.F] (x : D.host.E)}

def sigV (D : D7) (v : Pl D) : Fv D.host.F v ⊗[D.host.F] D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig

end GlobalTheory.FixedUnitNorm

end
