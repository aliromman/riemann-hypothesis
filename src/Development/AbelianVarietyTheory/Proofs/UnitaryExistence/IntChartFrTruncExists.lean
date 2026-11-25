module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPointStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartsCompleteDvrStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntChartFrTrunc
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

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem GlobalTheory.IntChartTrunc.intChart_frTrunc_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT :=
  fun E _ _ _ H Dw l Xo c _ hstar T io y =>
    GlobalTheory.IntChartTrunc.exists_intChart_frTrunc GlobalTheory.T.integral_charts_complete_dvr E H Dw l Xo c hstar (GlobalTheory.T.integralChart_transport_to_framedPoint E H Dw l Xo c) T io y
