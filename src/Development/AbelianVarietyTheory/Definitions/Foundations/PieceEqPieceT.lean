module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def rowT (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val + (p : ℤ) ^ n * w.1,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * w.2)

def pieceT (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

def pieceTRaw (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

end GlobalTheory.KummerEisensteinGalois
