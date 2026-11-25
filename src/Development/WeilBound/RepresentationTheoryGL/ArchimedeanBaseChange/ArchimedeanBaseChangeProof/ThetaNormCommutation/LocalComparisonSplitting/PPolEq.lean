module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
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

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem poleq_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E)
    (hu : IsTransl u) (d : GL (Fin n) E) : d * u⁻¹ * thE E n (d * u⁻¹) = nrm d := by
  have h2 : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right hu.2
  rw [hu.1, map_mul, map_inv, h2, nrm]
  group

end PositivityTheory.Rg.BcB.G8

end
