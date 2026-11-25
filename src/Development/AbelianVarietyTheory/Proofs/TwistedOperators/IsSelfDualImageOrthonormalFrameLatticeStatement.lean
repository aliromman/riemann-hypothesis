module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice : ∀ {D : D7} (S : HSp D) (fr : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1 → ∀ Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), SD D Ls → ∃ Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), (Λ : Set (Fin S.rank → D.host.E)) = GlobalTheory.MovedDict.inV fr Ls ∧ IsSelfDualC S Λ := by
  first | exact @GlobalTheory.MovedDict.isSelfDualC_inV
