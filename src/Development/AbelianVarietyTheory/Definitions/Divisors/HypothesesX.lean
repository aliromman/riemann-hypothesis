module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight
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

namespace GlobalTheory.CovTop

structure HypothesesX : Prop where

  ks : GlobalTheory.Published.ToroidalForFanKS

  lie : GlobalTheory.Published.SemiAbelianLieSeminegative

  green : GlobalTheory.Published.GreenCuspidal

  sep : GlobalTheory.Published.PointSeparationPair

  fsch : GlobalTheory.Published.FubiniStudyChowHeight

end GlobalTheory.CovTop
