module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

noncomputable section

namespace GlobalTheory.RamValCheck

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem g_coprime (D : Formalism.BasicNotions.D7) (k : Fin 2) (p : ℕ)
    (hp : p ∈ D.host.condN.primeFactors) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hdvd : p ∣ D.host.QS * D.host.q * D.host.d := Nat.dvd_of_mem_primeFactors hp
  refine Nat.Coprime.coprime_dvd_right hdvd ?_
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

end GlobalTheory.RamValCheck
