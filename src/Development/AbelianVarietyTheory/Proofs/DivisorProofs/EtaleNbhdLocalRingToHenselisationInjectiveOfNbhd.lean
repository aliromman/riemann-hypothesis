module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjecti
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNbhdTransitionMapDirectedSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
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

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem Hens.of_injective_of_nbhd (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    Function.Injective (Hens.of i) := by
  have : IsDirected (EtNbhd R) (· ≤ ·) := _root_.GlobalTheory.Henselisation.etNbhd_isDirected R
  have : DirectedSystem (fun j : EtNbhd R => j.B) (fun _ _ h => ⇑(EtNbhd.trans h)) :=
    ⟨fun j x => (_root_.GlobalTheory.Henselisation.trans_system R).1 j x,
      fun k j l hlj hjk x => (_root_.GlobalTheory.Henselisation.trans_system R).2 l j k hlj hjk x⟩
  exact Ring.DirectLimit.of_injective (G := fun j : EtNbhd R => j.B) (fun _ _ h => EtNbhd.trans h)
    (fun _ _ h => (_root_.GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective R _ _ h).2) i

end GlobalTheory.Henselisation
