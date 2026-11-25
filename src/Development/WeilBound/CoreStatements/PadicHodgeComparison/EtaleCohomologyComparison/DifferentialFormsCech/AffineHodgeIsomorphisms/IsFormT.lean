module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Om.L2

open CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inTop (T : Thick (smFun X q)) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ T := by
  intro x _
  trivial

structure LiftsT where
  v : ∀ T : Thick (smFun X q), Γ(X, ⊤) → T.B
  hv : ∀ T g, Ideal.Quotient.mk T.J (v T g) =
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g

variable {q}

def LiftsT.form (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤))
    (s : ComposableArrows (Thick (smFun X q)) a) : (s.obj (Fin.last a)).B :=
  Λ.v _ g₀ * ∏ k : Fin a, ((s.map (homOfLE (Fin.le_last k.succ))).φ (Λ.v _ (g k)) -
    (s.map (homOfLE (Fin.le_last k.castSucc))).φ (Λ.v _ (g k)))

variable (q)

def IsFormT {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : Hdg q a a) : Prop :=
  ∀ Λ : LiftsT q, Rep (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) (Λ.form g₀ g)
    (show CH.H (grT (smFun X q) a) a from c)

abbrev gForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) : GlobalTheory.CechDR.OmU q ⊤ a :=
  CrystallineSemistableComparison.Onto.form K (A := GlobalTheory.CechDR.Sec q ⊤) g₀ g

def IsOmT (a : ℕ) (e : Hdg q a a ≃ₗ[K] GlobalTheory.CechDR.OmU q ⊤ a) : Prop :=
  ∀ (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)), IsFormT q g₀ g (e.symm (gForm q g₀ g))

end CrystallineSemistableComparison.Om.L2
