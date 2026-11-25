module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pFEtInj :
    GalClosD → FEtInj.{u} := by
  intro hGC B R _ T hT Z W p r c hc d hd hfet
  obtain ⟨V, e, G, _, _, a, σ, hgal, hspl⟩ := hGC c d hfet
  have h0 : σ ⟨0, hd⟩ ≫ c = e := hspl.1 _
  subst h0
  have hinj := hT.inj p ((σ ⟨0, hd⟩ ≫ c) ≫ p) (σ ⟨0, hd⟩ ≫ c) rfl G a hgal
  have hσr : σ ⟨0, hd⟩ ≫ r = (σ ⟨0, hd⟩ ≫ c) ≫ p := by
    rw [← hc, Category.assoc]
  have hcomp := T.pull_comp (σ ⟨0, hd⟩) c hσr hc rfl
  intro x y hxy
  apply hinj
  rw [hcomp x, hcomp y, hxy]
