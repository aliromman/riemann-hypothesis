module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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

open NumberField GlobalTheory.BCT GlobalTheory.CuspRep Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def mulMat (a : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)).map e

def gram (β : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  Matrix.of fun i j => e (B.herm β (b i) (b j))

def dlt (β : B.A) : GLw m w :=
  if h : IsUnit (gram e b β) then invT m _ h.unit * (PhiU m _)⁻¹ else 1

def lat (g : GLw m w) : Submodule K.O B.A :=
  Submodule.span K.O (Set.range fun j => ∑ i, e.symm (g.val i j) • b i)

end GlobalTheory.TwLat
