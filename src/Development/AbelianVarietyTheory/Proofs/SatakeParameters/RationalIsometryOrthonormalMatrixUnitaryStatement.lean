module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  first | exact @GlobalTheory.TwV.ratIsometry_unitary
