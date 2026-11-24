module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
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
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.LocalRingCardinality.DataParams₂

@[expose] public section

noncomputable section

namespace GlobalTheory.SmallJumpExample

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW GlobalTheory.IndefiniteRowSideFullHecke
open scoped Formalism.Per

theorem isField_bdR (D : D7) (l : ℕ) [Fact l.Prime] : IsField (D.loc l).R.BdR :=
  MulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1 (D.locT l).eD.toMulEquiv

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (n : ℕ)

end Count

variable {D : D7} (L : SizeData₂ D)

end GlobalTheory.SmallJumpExample
