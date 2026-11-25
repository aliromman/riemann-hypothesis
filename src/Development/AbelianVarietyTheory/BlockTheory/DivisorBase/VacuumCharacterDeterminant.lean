module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

variable {D : D7}

abbrev Fam (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ

section Forms

variable (S T : HSp D)

def hAt (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  Matrix.trace ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x)

def efR (x y : Fam D T.rank S.rank) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * hAt S T τ (x τ) (y τ)).re

end Forms

section Canon

variable (S T : HSp D) (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
  (Γ : Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E))

end Canon

section Chars

def detPos {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  (k * ((1 / 2 : ℂ) • (1 + s)) + (1 / 2 : ℂ) • (1 - s)).det

def detNeg {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ := detPos (-s) k

def vacChar (θ : InfFam D) (T : HSp D) (sT : Fam D T.rank T.rank) (n : ℕ) (a : D.what₂.Tau → ℤ) (k : GA D T) : ℂ :=
  ∏ τ, detPos (sT τ) (compAt θ τ (mt T k)) ^ (a τ + ((n / 2 : ℕ) : ℤ)) *
    detNeg (sT τ) (compAt θ τ (mt T k)) ^ (a τ - ((n / 2 : ℕ) : ℤ))

end Chars

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

end
