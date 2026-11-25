module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  first | exact @GlobalTheory.GoodRowsLevel.eeat_sub_principal
