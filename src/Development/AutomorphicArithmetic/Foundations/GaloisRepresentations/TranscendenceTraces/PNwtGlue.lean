module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normSpec_of :
    SplitCover → CountEx → CountWt → MultPt → PtEx → PtLift → GenBasic → NormSpec := by
  intro hS hCE hCW hMP hPE hPL _
  unfold NormSpec
  intro A B _ _ _ _ _ _
  set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp
  haveI : IsFinite p := by
    rw [hp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨T, π, ι, σ, c, hπi, hπs, hι, hσ, hsym, hgen⟩ := hS A B
  haveI := hπi
  haveI := hπs
  haveI := hι
  have hk : ∀ s : ↥(Spec (CommRingCat.of B)), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (y : gp Ω ⟶ Spec (CommRingCat.of B)), pt y = s := fun s => hPE _ s
  choose Ωk fk ak yk hyk using hk
  let key : ↥(Spec (CommRingCat.of B)) → ℤ := fun s => letI := fk s; letI := ak s; mult p (Ωk s) (yk s)
  let m : ι → ℤ := fun j => key (c j)
  have hm : ∀ j (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Spec (CommRingCat.of B)),
      c j = pt z → m j = mult p Ω z := by
    intro j Ω _ _ z hz
    letI := fk (c j)
    letI := ak (c j)
    exact hMP p (Ωk (c j)) Ω (yk (c j)) z ((hyk (c j)).trans hz)
  have hSy : UpperTheory.Gal.TranscendenceTraces.Sym π σ m := by
    unfold UpperTheory.Gal.TranscendenceTraces.Sym
    intro Ω _ _ x x' hxx'
    obtain ⟨e, he⟩ := hsym Ω x x' hxx'
    exact ⟨e, fun j => ⟨(he j).1, congrArg key (he j).2⟩⟩
  obtain ⟨w, hw⟩ := hCE p π σ m hSy
  refine ⟨w, hCW p π σ m w hσ hw, ?_⟩
  intro Ω _ _ z hz
  obtain ⟨v, hv⟩ := π.surjective (pt (z ≫ p))
  obtain ⟨x, hx, -⟩ := hPL π Ω (z ≫ p) v hv
  have hcount := hw Ω x z hx.symm
  have hbot : (pt (x ≫ π)).asIdeal = ⊥ := by
    rw [hx]
    unfold GenPt at hz
    have h0 := hz (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
    rw [← h0]
  obtain ⟨⟨j0, hj0, huniq⟩, hcj⟩ := hgen Ω x z hx.symm hbot
  have hset : {j | x ≫ σ j = z} = {j0} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact huniq j
    · rintro rfl
      exact hj0
  rw [hcount, hset, finsum_mem_singleton]
  exact hm j0 Ω z (hcj j0 hj0)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtAgree_of :
    NwtOpen → WtUnique → GenBasic → MultBC → NwtAgree := by
  intro hOpen hUniq hGen _ Z S p _ A B _ _ w w' hw hw' Ω _ _ z z' hz
  have hc : pullback.fst A.u B.u ≫ A.u = pullback.snd A.u B.u ≫ B.u := pullback.condition
  have hP : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.fst A.u B.u ≫ A.u) :=
    IsPullback.of_hasPullback _ _
  have hP' : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.snd A.u B.u ≫ B.u) := by
    rw [← hc]
    exact hP
  have eA : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.fst A.u B.u) ≫ A.u := by
    rw [Category.assoc]
    exact hP.w
  have eB : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.snd A.u B.u) ≫ B.u := by
    rw [Category.assoc]
    exact hP'.w
  let C : Sq A.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.fst A.u B.u,
    A.pb.lift _ _ eA, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [A.pb.lift_fst]; exact hP) (A.pb.lift_snd _ _ _) A.pb⟩
  let C' : Sq B.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.snd A.u B.u,
    B.pb.lift _ _ eB, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [B.pb.lift_fst]; exact hP') (B.pb.lift_snd _ _ _) B.pb⟩
  haveI : IsOpenImmersion C.u := inferInstanceAs (IsOpenImmersion (pullback.fst A.u B.u))
  haveI : IsOpenImmersion C'.u := inferInstanceAs (IsOpenImmersion (pullback.snd A.u B.u))
  have h1 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w.comap C.v) := hOpen A.r w C hw
  have h2 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w'.comap C'.v) := hOpen B.r w' C' hw'
  haveI : IsFinite (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) := MorphismProperty.of_isPullback hP ‹_›
  have hE : w.comap C.v = w'.comap C'.v :=
    hUniq _ _ _ h1.1 h2.1 {s | GenPt s} (hGen.1 _) fun Ω _ _ y hy => by
      rw [h1.2 Ω y hy, h2.2 Ω y hy]
  have e1 : (z ≫ A.r) ≫ A.u = (z' ≫ B.r) ≫ B.u := by
    rw [Category.assoc, Category.assoc, ← A.pb.w, ← B.pb.w, ← Category.assoc, ← Category.assoc, hz]
  have e2 : (z ≫ A.v) ≫ p = pullback.lift (z ≫ A.r) (z' ≫ B.r) e1 ≫ pullback.fst A.u B.u ≫ A.u := by
    rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, A.pb.w]
  let z0 : gp Ω ⟶ pullback p (pullback.fst A.u B.u ≫ A.u) :=
    pullback.lift (z ≫ A.v) (pullback.lift (z ≫ A.r) (z' ≫ B.r) e1) e2
  have hz0 : z0 ≫ C.v = z := by
    apply A.pb.hom_ext
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.v = _
      rw [Category.assoc, A.pb.lift_fst]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.r = _
      rw [Category.assoc, A.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
  have hz0' : z0 ≫ C'.v = z' := by
    apply B.pb.hom_ext
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.v = _
      rw [Category.assoc, B.pb.lift_fst, ← hz]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.r = _
      rw [Category.assoc, B.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  have := congrFun (congrFun (congrFun (congrFun hE Ω) ‹_›) ‹_›) z0
  simpa only [Wt.comap, hz0, hz0'] using this
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem lift_ex {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) [IsOpenImmersion A.u] {Ω : Type} [Field Ω]
    (z : gp Ω ⟶ Z) (hz : pt (z ≫ p) ∈ Set.range A.u) : ∃ l : gp Ω ⟶ A.V, l ≫ A.v = z := by
  have hr : Set.range (z ≫ p) ⊆ Set.range A.u := by
    rintro _ ⟨t, rfl⟩
    rw [pt_eq]
    exact hz
  exact ⟨A.pb.lift z (IsOpenImmersion.lift A.u (z ≫ p) hr) (IsOpenImmersion.lift_fac _ _ _).symm,
    A.pb.lift_fst _ _ _⟩

theorem UpperTheory.Gal.TranscendenceTraces.nwtGlue_of :
    NwtAgree → WtLocal → MultBC → GenBasic → NwtGlue := by
  intro hAg hLoc hBC hGen Z S p _ h
  choose A w hopen hmem hw using h
  have hl : ∀ (Ω : Type) [Field Ω] (z : gp Ω ⟶ Z), ∃ l : gp Ω ⟶ (A (pt (z ≫ p))).V, l ≫ (A (pt (z ≫ p))).v = z := by
    intro Ω _ z
    haveI := hopen (pt (z ≫ p))
    exact lift_ex _ z (hmem _)
  choose l hlv using hl
  let W : Wt Z := fun Ω _ _ z => w (pt (z ≫ p)) Ω (l Ω z)
  have hcomap : ∀ t, W.comap (A t).v = w t := by
    intro t
    funext Ω _ _ z
    haveI := hopen t
    haveI := hopen (pt ((z ≫ (A t).v) ≫ p))
    exact hAg p (A _) (A t) (w _) (w t) (hw _) (hw t) Ω (l Ω (z ≫ (A t).v)) z (hlv Ω _)
  refine ⟨W, hLoc p W fun s => ⟨A s, hopen s, hmem s, ?_⟩, ?_⟩
  · rw [hcomap s]
    exact (hw s).1
  · intro Ω _ _ z hz
    set s := pt (z ≫ p) with hs
    haveI := hopen s
    have hz' : GenPt (pt (l Ω z ≫ (A s).r)) := by
      rw [← hGen.2.1 (A s).u, ← pt_comp, Category.assoc, ← (A s).pb.w, ← Category.assoc, hlv Ω z]
      exact hz
    have h1 := (hw s).2 Ω (l Ω z) hz'
    have h2 := hBC (A s).v (A s).r p (A s).u (A s).pb
    change w s Ω (l Ω z) = _
    rw [h1, h2]
    change mult p Ω (l Ω z ≫ (A s).v) = _
    rw [hlv Ω z]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue =====
