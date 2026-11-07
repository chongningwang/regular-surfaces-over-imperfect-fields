import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Group.Units.Hom
import Red61.AlgebraicGeometry.Modules

/-! # Mu-five torsors on all scheme-valued points

The acting group at a test scheme is the group of units of its global sections whose
fifth power is one. Testing every scheme, with pullback compatibility, retains the
nonreduced group scheme; restricting to field-valued points would lose it.
-/

namespace SurfaceLib.MuFive

open AlgebraicGeometry CategoryTheory
noncomputable section

def group (T : Scheme) : Subgroup (Γ(T, ⊤))ˣ := (powMonoidHom 5).ker

def pullGroup {T U : Scheme} (h : U ⟶ T) : group T →* group U where
  toFun a := ⟨Units.map h.appTop.hom.toMonoidHom (a : (Γ(T, ⊤))ˣ), by
    change (Units.map h.appTop.hom.toMonoidHom (a : (Γ(T, ⊤))ˣ)) ^ 5 = 1
    have ha : (a : (Γ(T, ⊤))ˣ) ^ 5 = 1 := a.property
    simpa only [map_pow, map_one] using
      congrArg (Units.map h.appTop.hom.toMonoidHom) ha⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

variable {S Y : Scheme} (ρ : S ⟶ Y)

def PointOver {T : Scheme} (g : T ⟶ Y) := {s : T ⟶ S // s ≫ ρ = g}

def pullPoint {T U : Scheme} (h : U ⟶ T) (g : T ⟶ Y) (s : PointOver ρ g) :
    PointOver ρ (h ≫ g) :=
  ⟨h ≫ s.val, by rw [Category.assoc, s.property]⟩

/-- Concrete finite flat mu-five torsor data. The principal-homogeneous condition is
required on all test schemes, not just on geometric or rational points. The fiber
dimension condition records rank five using the actual scheme-theoretic fibers. -/
structure Torsor where
  finite : IsFinite ρ
  flat : Flat ρ
  surjective : Surjective ρ
  act : ∀ (T : Scheme) (g : T ⟶ Y), group T → PointOver ρ g → PointOver ρ g
  one_act : ∀ (T : Scheme) (g : T ⟶ Y) (s : PointOver ρ g), act T g 1 s = s
  mul_act : ∀ (T : Scheme) (g : T ⟶ Y) (a b : group T) (s : PointOver ρ g),
    act T g (a * b) s = act T g a (act T g b s)
  natural : ∀ {T U : Scheme} (h : U ⟶ T) (g : T ⟶ Y)
    (a : group T) (s : PointOver ρ g),
    pullPoint ρ h g (act T g a s) = act U (h ≫ g) (pullGroup h a) (pullPoint ρ h g s)
  principal : ∀ (T : Scheme) (g : T ⟶ Y) (s t : PointOver ρ g),
    ∃! a : group T, act T g a s = t
  rankFive : ∀ y : Y,
    letI := (Red61.globalScalarMap (Y.residueField y)
      (ρ.fiberToSpecResidueField y)).toAlgebra
    Module.finrank (Y.residueField y) Γ(ρ.fiber y, ⊤) = 5

end
end SurfaceLib.MuFive
