module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def liftHom {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

instance {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ)).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).isRightAdjoint

def coind {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : Shv R ⥤ Shv S :=
  sheafCompose _ (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ))

end GlobalTheory.EtC

end
