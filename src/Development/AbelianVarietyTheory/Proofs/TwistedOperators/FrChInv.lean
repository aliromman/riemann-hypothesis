module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped Matrix

noncomputable section

namespace GlobalTheory.AvgCol

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frRel (W : G.Weil) {U : Set T} (N : Std G U) (X : Node) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  (W.onb X τ)⁻¹ * N.frC X τ

def frCh (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => frRel W N (.top (j + 1)) τ) (fun τ => ((frRel W N (.top j) τ)⁻¹)ᵀ)

def frChInv (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => (frRel W N (.top (j + 1)) τ)⁻¹) (fun τ => (frRel W N (.top j) τ)ᵀ)

end GlobalTheory.AvgCol

end
