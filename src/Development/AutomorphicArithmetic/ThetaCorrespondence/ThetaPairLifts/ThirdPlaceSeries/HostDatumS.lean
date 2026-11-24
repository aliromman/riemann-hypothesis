module

public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
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



section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
namespace Host
end Host
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure HostDatumWithTies {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) where
  d3b : Host.PlacesOverCommonPrime D.host
  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i
  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ u, ¬ Host.OverP D.host (D.mem u).A.T v
  clsK : Host.ClsRepK D.host
  clsK_Tu : ∀ c u, IsCoprime (clsK.rep c : Ideal (𝓞 D.host.K)) (Host.idK (H := D.host) (D.mem u).A.T)
  clsK_Qw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ c,
    Host.PrimeToPl (H := D.host) (clsK.rep c : Ideal (𝓞 D.host.K)) v
  LLgal : IsGalois ℚ T.host.LLQ
  HE : Fld
  HE_fd : FiniteDimensional ℚ HE
  HE_hilb : Host.IsHilbertCFE (hL := HE_fd) D.host HE
  HE_le : HE ≤ Rows.KsQ D T.host T.n.cf T.what₂.O.pieces
def HostDatumSelfDual {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) : Prop := Nonempty (_root_.Formalism.L2.HostDatumWithTies T)
end
end Formalism.L2
end
end
