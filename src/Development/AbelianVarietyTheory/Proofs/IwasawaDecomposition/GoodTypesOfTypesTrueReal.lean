module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Host Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain

namespace GlobalTheory.HeightCounting

theorem goodTypes_of_typesTrue_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hL h => GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hL h

end GlobalTheory.HeightCounting
