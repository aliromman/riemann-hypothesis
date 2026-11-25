module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.BotMove

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7} {T : Type} {A A' WW : HSp D}

def moveTri (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ) : Tri T A A' WW where
  rA := ⟨ΛA, Lev.finE A g * Y.rA.β, Y.rA.s, Y.rA.B⟩
  rA' := ⟨ΛA', Lev.finE A' g' * Y.rA'.β, Y.rA'.s, Y.rA'.B⟩
  rW := ⟨ΛW, Lev.finE WW h * Y.rW.β, Y.rW.s, Y.rW.B⟩
  ω := Y.ω
  ω' := Y.ω'
  vac := Y.ω t₀ (g, h) Y.vac
  vac' := Y.ω' t₀ (g', h) Y.vac'
  e := Y.e
  c := Y.c
  f t := (r t)⁻¹ • Y.ω t (g, h) (Y.f t)
  f' t := (r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)
  m := Y.m.map (fun x => x * g⁻¹)
  fd := (fun x => x * g) ⁻¹' Y.fd
  m' := Y.m'.map (fun x => x * g'⁻¹)
  fd' := (fun x => x * g') ⁻¹' Y.fd'

variable (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
  (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
  (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ)

end GlobalTheory.BotMove

end
