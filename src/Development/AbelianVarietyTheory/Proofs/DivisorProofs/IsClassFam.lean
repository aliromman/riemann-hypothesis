module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalToGlobal.Divisibility.Numbers
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
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

noncomputable section

namespace GlobalTheory.ColumnNormCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

@[reducible] def numDatumOfParameters (D : D7) (large₂ : SizeData₂ D) : NumDatum where
  R := D.R
  sc := large₂.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊D.s.Del⌋₊
  h0 := ⌈LevelStarExponents.h0 large₂⌉₊
  hc := fun z => D.hc (tauPl D z)

def plRec (D : D7) : RPl D.R ≃ D.what₂.Tau := GlobalTheory.InertCompare.plEquiv D

def codeRec {D : D7} (large₂ : SizeData₂ D) (u : D.what₂.Word) : Code (numDatumOfParameters D large₂) := D.s.letter u

section Rec

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

end Rec

end GlobalTheory.ColumnNormCompare
