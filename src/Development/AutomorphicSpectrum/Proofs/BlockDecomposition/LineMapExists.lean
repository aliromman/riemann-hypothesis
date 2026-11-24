module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EtNatProof

def resHom {R : Type} [CommRing R] (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec G U →+ Sec G V :=
  (G.obj.map g.op).hom.toAddMonoidHom

theorem res_res {R : Type} [CommRing R] (G : Shv R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec G U) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {G G' : Shv R} (φ : G ⟶ G') {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom a) h).symm

theorem kap_zero (hKap : KapSpec) (hTw : TwZero) (hGen : InGen) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (ζ ξ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) : kap 0 ζ f = kap 0 ξ f := by
  refine ((hKap q 0 U ζ f).2.1 _ ?_).symm
  intro V g a hv
  rw [(hKap q 0 U ξ f).1 V g a hv, hTw hGen q V (primRes g ξ) (primRes g ζ)]

def resMor {q : ℕ} {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (P : Probe C q) (P' : Probe C' q)
    (m : Mor P.L P'.L (RingHom.id ℤ)) (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (i : ℤ)
    (hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f)) :
    ResMor (P.res i) (P'.res i) m where
  τ s c := resHom _ (g c)
  nat s {c c'} φ x := by
    change Sec.res (g c') (Sec.res (P.S.map (m.G.map φ)).unop x) = Sec.res (P'.S.map φ).unop (Sec.res (g c) x)
    rw [res_res, res_res, hg φ]
  ι c x := by
    change Sec.res (g c) (Sec.map (resι _ (tw q i)) (kap i (P.ζ (m.G.obj c)) x)) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [res_map, hι]
  dv s c x := by
    change Sec.res (g c) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) x)
    exact res_map _ _ _

theorem etNat : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.TwZero → CrystallineSemistableComparison.E.EtNat := by
  intro hEt hEM hRep hKap hTw hGen q _ C C' _ _ P P' X X' Y Y' u m g hg hτ hy i hi j x
  obtain ⟨a, ha⟩ := (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).1 x
  have hE := (hEt hGen q C P X Y i j x).1 a ha
  have hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f) := by
    intro c f
    rw [(hKap q i _ (P.ζ (m.G.obj c)) f).2.2 _ (g c), hτ c f]
    rcases hi with rfl | hi
    · exact kap_zero hKap hTw hGen q _ _ _
    · rw [hi c]
  let n := resMor P P' m g hg i hι
  have hE' := hEM ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m n j _ _ hE
  have hglob : n.pullC j 0 (Y.glob i j a) = Y'.glob i j (Sec.res u a) := by
    funext t
    change Sec.res (g (t.obj (Fin.last 0))) (Sec.res (Y.y (m.G.obj (t.obj (Fin.last 0)))) a) =
      Sec.res (Y'.y (t.obj (Fin.last 0))) (Sec.res u a)
    rw [res_res, res_res, hy]
  rw [hglob] at hE'
  have hR : Rep (pull _ (sch.map u) _ j x) (Sec.res u a) :=
    (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.2.2.2 X' u x a ha
  exact (hEt hGen q C' P' X' Y' i j _).2 _ ⟨_, hR, hE'⟩

end GlobalTheory.CompanionTheory.EtNatProof

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechLine

variable {X : Scheme.{0}} (D : LineData X)

theorem u_self {V : Scheme.{0}} (a : V ⟶ D.Y) (h : a ≫ D.f = a ≫ D.f) : D.u a a h = 1 := by
  have h2 : D.u a a h * D.u a a h = D.u a a h * 1 := by
    rw [mul_one]
    exact D.coc a a a h h
  exact mul_left_cancel h2

theorem u_congr {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha
  subst hb
  rfl

def lineFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ D.Y)) (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) :
    ComposableArrows (SingleObj (GL (Fin 1) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j))
  map_id i := by rw [u_self]; exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    refine Eq.trans ?_ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _)
    rw [mul_comm, D.coc]

variable {D}

theorem exists_pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ D.Y), ∃ x h, z = cechPt D.f k x y h := by
  obtain ⟨x, y, h, hz⟩ := (hC D.Y X D.f k U).1 z
  exact ⟨y, x, h, hz⟩

def pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) : Fin (k + 1) → (U ⟶ D.Y) :=
  (exists_pts hC z).choose

theorem pts_spec (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ x h, z = cechPt D.f k x (pts hC z) h := by
  exact (exists_pts hC z).choose_spec

theorem pts_eq (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) (i j : Fin (k + 1)) :
    pts hC z i ≫ D.f = pts hC z j ≫ D.f := by
  obtain ⟨x, h, -⟩ := pts_spec hC z
  exact (h i).trans (h j).symm

theorem pts_cechPt (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ D.Y))
    (h : ∀ i, y i ≫ D.f = x) : pts hC (cechPt D.f k x y h) = y := by
  obtain ⟨x', h', hz⟩ := pts_spec hC (cechPt D.f k x y h)
  exact ((hC D.Y X D.f k U).2.1 _ _ _ _ _ _ hz).symm

theorem pts_res (hC : CechPt) {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech D.f) k U) (i : Fin (k + 1)) :
    pts hC (Sx.res g z) i = g ≫ pts hC z i := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.1 V g
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem pts_along (hC : CechPt) {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts hC (Sx.along z θ) i = pts hC z (θ.toOrderHom i) := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.2 p θ
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem scalar_map {A B : CommRingCat.{0}} (f : A ⟶ B) (u : (A : Type)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map f.hom.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (D) in
theorem lineFun_res {U V : Scheme.{0}} {k : ℕ} (g : V ⟶ U) (y : Fin (k + 1) → (U ⟶ D.Y))
    (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) (y' : Fin (k + 1) → (V ⟶ D.Y))
    (hy' : ∀ i j, y' i ≫ D.f = y' j ≫ D.f) (e : ∀ i, y' i = g ≫ y i) :
    lineFun D y' hy' = (show Fin (k + 1) ⥤ (glCat 1).obj Γ(U, ⊤) from lineFun D y hy) ⋙
      ((glCat 1).map (Scheme.Γ.map g.op)).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j _ => ?_)
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y' i) (y' j) (hy' i j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.op).hom
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j)))
  rw [← scalar_map]
  congr 1
  rw [u_congr D (e i) (e j) (hy' i j) (by rw [Category.assoc, Category.assoc, hy i j]),
    D.nat g (y i) (y j) (hy i j)]
  rfl


variable (D) in
def lineMap (hC : CechPt) : cech D.f ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
      naturality := fun U U' g => by
        ext z
        exact lineFun_res D g.unop _ (pts_eq hC _) _ (pts_eq hC _) (fun i => pts_res hC g.unop _ i) }
  naturality n m θ := by
    ext U z
    change lineFun D (pts hC (Sx.along (show Sx (cech D.f) n.unop.len U.unop from z) θ.unop)) (pts_eq hC _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1))
      (u_congr D (pts_along hC _ θ.unop i) (pts_along hC _ θ.unop j) _ _)

theorem lineMap_exists : CrystallineSemistableComparison.E.CechPt → CrystallineSemistableComparison.E.LineMap := by
  intro hC X D
  refine ⟨lineMap D hC, ?_⟩
  unfold CrystallineSemistableComparison.E.LineData.IsMap
  intro V x a h
  have hp := pts_cechPt (D := D) hC x a h
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (D.u (pts hC (cechPt D.f 1 x a h) 0) (pts hC (cechPt D.f 1 x a h) 1) (pts_eq hC _ 0 1))) = _
  rw [u_congr D (congrFun hp 0) (congrFun hp 1) _ ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end GlobalTheory.CompanionTheory.CechLine
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists =====
