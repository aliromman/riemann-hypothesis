module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  first | exact @GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd
