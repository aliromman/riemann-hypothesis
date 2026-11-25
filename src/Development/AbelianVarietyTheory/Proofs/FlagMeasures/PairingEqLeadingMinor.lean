module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermCmpWedgeEqDet
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PrincipalMinorExterior

theorem pairing_eq_leading_minor : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp l (Formalism.QuantumDeterminants.Hpk k r))
      (cmp l g *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z' (Fin.castLE hl a))))
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) =
      ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  intro k r l hl z z' g
  rw [Formalism.QuantumDeterminants.herm, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge,
    GlobalTheory.TopMinorWedge.star_wedge_dot]
  rfl

end GlobalTheory.PrincipalMinorExterior
