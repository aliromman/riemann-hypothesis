module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
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

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.rational_isometry_extends_local_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (p : PlF D), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃ g, Ext p γ g ∧ LocNG.IsUnitary (locH Z p) g ∧ (∀ g', Ext p γ g' → g' = g) ∧ (∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap γ Λ)) ∧ ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), γ ∈ Formalism.L2.SG.NGData.NRat F → g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  first | exact @GlobalTheory.LocExt.ext_isometry
