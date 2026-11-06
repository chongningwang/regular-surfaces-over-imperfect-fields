import Red61.Canonical.InvariantCoordinates

/-! # Differential coordinates transported to stalks

Formerly the modules `AwayDifferentialCoordinates`, `AtlasStalkCoordinates`, `StalkCoordinateTransport`.
-/

/-! Coordinate-preserving differential bases after an open localization
and localization at a prime. The coordinate map is part of the result. -/

namespace Red61

open Module
noncomputable section

theorem differentialCoordinatesAtPrime_of_away
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    [Algebra A B] (d : A) [IsLocalization.Away d B]
    (p : PrimeSpectrum A) (hd : d ∉ p.asIdeal)
    (b : Basis ι B (KaehlerDifferential ℤ B)) (v : ι → B)
    (hv : ∀ i, b i = KaehlerDifferential.D ℤ B (v i)) :
    ∃ (f : B →+* Localization.AtPrime p.asIdeal)
      (b' : Basis ι (Localization.AtPrime p.asIdeal)
        (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))),
      (∀ a, f (algebraMap A B a) = algebraMap A (Localization.AtPrime p.asIdeal) a) ∧
        ∀ i, b' i = KaehlerDifferential.D ℤ (Localization.AtPrime p.asIdeal) (f (v i)) := by
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B d]
    exact hd
  obtain ⟨q, rfl⟩ := hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers d) (Localization.AtPrime q.asIdeal) q.asIdeal
  let e := IsLocalization.algEquiv (q.asIdeal.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime (q.asIdeal.comap (algebraMap A B)))
  let bq := absoluteDifferentialBasisAtPrime B ι q b
  have hbq (i : ι) : bq i = KaehlerDifferential.D ℤ (Localization.AtPrime q.asIdeal)
      (algebraMap B (Localization.AtPrime q.asIdeal) (v i)) := by
    change absoluteDifferentialBasisAtPrime B ι q b i = _
    rw [absoluteDifferentialBasisAtPrime, differentialBasisOfLocalization_apply, hv,
      KaehlerDifferential.map_D]
  refine ⟨e.toRingHom.comp (algebraMap B (Localization.AtPrime q.asIdeal)),
    absoluteDifferentialBasisOfRingEquiv e.toRingEquiv bq, ?_, ?_⟩
  · intro a
    change e (algebraMap B (Localization.AtPrime q.asIdeal) (algebraMap A B a)) = _
    rw [← IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal), e.commutes]
    rfl
  · exact absoluteDifferentialBasisOfRingEquiv_apply_D e.toRingEquiv bq _ hbq

theorem differentialCoordinatesAtPrime_transport
    {A B R F ι : Type*} [CommRing A] [CommRing B] [CommRing R] [CommRing F]
    [Algebra ℤ A] [Algebra ℤ B] [Algebra ℤ R] [Algebra A B]
    (d : A) [IsLocalization.Away d B] (p : PrimeSpectrum A) (hd : d ∉ p.asIdeal)
    (b : Basis ι B (KaehlerDifferential ℤ B)) (v : ι → B)
    (hv : ∀ i, b i = KaehlerDifferential.D ℤ B (v i))
    (e : Localization.AtPrime p.asIdeal ≃+* R) (g : R →+* F) (h : B →+* F)
    (hA : ∀ a, g (e (algebraMap A (Localization.AtPrime p.asIdeal) a)) = h (algebraMap A B a)) :
    ∃ (f : B →+* R) (b' : Basis ι R (KaehlerDifferential ℤ R)),
      (∀ i, b' i = KaehlerDifferential.D ℤ R (f (v i))) ∧ ∀ a, g (f a) = h a := by
  obtain ⟨f, b₀, hf, hb₀⟩ := differentialCoordinatesAtPrime_of_away d p hd b v hv
  let f' := e.toRingHom.comp f
  have hh : g.comp f' = h := by
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    apply RingHom.ext
    intro a
    change g (e (f (algebraMap A B a))) = _
    rw [hf]
    exact hA a
  exact ⟨f', absoluteDifferentialBasisOfRingEquiv e b₀,
    absoluteDifferentialBasisOfRingEquiv_apply_D e b₀ _ hb₀, RingHom.congr_fun hh⟩

end
end Red61

/-! Actual chart-to-stalk coordinate maps, their differential bases and
their compatibility with a specified function-field identification. -/

namespace Red61.AffineGluing.PrincipalAtlas

open AlgebraicGeometry Module
noncomputable section

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) [Nonempty D.Index]

def chartToStalkAt (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) :
    D.ring i →+* D.glued.presheaf.stalk y := by
  subst y
  exact (D.chartStalkEquiv i p).symm.toRingHom.comp
    (algebraMap (D.ring i) (Localization.AtPrime p.asIdeal))

def chartLocalizationEquivAt (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) :
    Localization.AtPrime p.asIdeal ≃+* D.glued.presheaf.stalk y := by
  subst y
  exact (D.chartStalkEquiv i p).symm

theorem chartToStalkAt_embedding (i : D.Index) [IsFractionRing (D.ring i) F]
    (p : PrimeSpectrum (D.ring i)) (y : D.glued) (hy : y = D.chartInclusion i p)
    (e : D.glued.functionField ≃+* F)
    (he : (D.functionFieldChartEquiv i).trans
      (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F) = e)
    (a : D.ring i) :
    e (algebraMap (D.glued.presheaf.stalk y) D.glued.functionField
      (D.chartToStalkAt i p y hy a)) = algebraMap (D.ring i) F a := by
  subst y
  rw [← he]
  change affineFunctionFieldEquiv _ F
    (D.functionFieldChartEquiv i (algebraMap _ D.glued.functionField _)) = _
  rw [D.functionFieldEquiv_stalk]
  simp [chartToStalkAt]

end
end Red61.AffineGluing.PrincipalAtlas

/-! Coordinate-preserving differential bases through prime localization
and a specified stalk ring isomorphism, with field embeddings checked on
the original ring. -/

namespace Red61

open Module
noncomputable section

def primeLocalizationRingEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (p : PrimeSpectrum B) :
    Localization.AtPrime (p.asIdeal.comap e.toRingHom) ≃+* Localization.AtPrime p.asIdeal :=
  IsLocalization.ringEquivOfRingEquiv
    (M := (p.asIdeal.comap e.toRingHom).primeCompl) (T := p.asIdeal.primeCompl)
    (Localization.AtPrime (p.asIdeal.comap e.toRingHom)) (Localization.AtPrime p.asIdeal)
    e (e.map_primeCompl_comap_eq p.asIdeal)

theorem primeLocalizationRingEquiv_algebraMap
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (p : PrimeSpectrum B) (a : A) :
    primeLocalizationRingEquiv e p
      (algebraMap A (Localization.AtPrime (p.asIdeal.comap e.toRingHom)) a) =
        algebraMap B (Localization.AtPrime p.asIdeal) (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (S := Localization.AtPrime (p.asIdeal.comap e.toRingHom))
    (Q := Localization.AtPrime p.asIdeal)
    (M := (p.asIdeal.comap e.toRingHom).primeCompl) (T := p.asIdeal.primeCompl)
    (j := e) _ a

theorem differentialCoordinatesAtPrime_transport_direct
    {A R F ι : Type*} [CommRing A] [CommRing R] [CommRing F]
    [Algebra ℤ A] [Algebra ℤ R]
    (p : PrimeSpectrum A) (b : Basis ι A (KaehlerDifferential ℤ A)) (v : ι → A)
    (hb : ∀ i, b i = KaehlerDifferential.D ℤ A (v i))
    (e : Localization.AtPrime p.asIdeal ≃+* R) (g : R →+* F) (h : A →+* F)
    (hA : ∀ a, g (e (algebraMap A (Localization.AtPrime p.asIdeal) a)) = h a) :
    ∃ (f : A →+* R) (b' : Basis ι R (KaehlerDifferential ℤ R)),
      (∀ i, b' i = KaehlerDifferential.D ℤ R (f (v i))) ∧ ∀ a, g (f a) = h a := by
  let bp := absoluteDifferentialBasisAtPrime A ι p b
  have hbp (i : ι) : bp i = KaehlerDifferential.D ℤ (Localization.AtPrime p.asIdeal)
      (algebraMap A (Localization.AtPrime p.asIdeal) (v i)) := by
    change absoluteDifferentialBasisAtPrime A ι p b i = _
    rw [absoluteDifferentialBasisAtPrime, differentialBasisOfLocalization_apply, hb,
      KaehlerDifferential.map_D]
  exact ⟨e.toRingHom.comp (algebraMap A (Localization.AtPrime p.asIdeal)),
    absoluteDifferentialBasisOfRingEquiv e bp,
    absoluteDifferentialBasisOfRingEquiv_apply_D e bp _ hbp, hA⟩

end
end Red61

namespace Red61.AffineGluing.PrincipalAtlas

open AlgebraicGeometry
noncomputable section

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) [Nonempty D.Index]

omit [Nonempty D.Index] in
theorem chartLocalizationEquivAt_algebraMap (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) (a : D.ring i) :
    D.chartLocalizationEquivAt i p y hy
      (algebraMap (D.ring i) (Localization.AtPrime p.asIdeal) a) =
        D.chartToStalkAt i p y hy a := by
  subst y
  rfl

end
end Red61.AffineGluing.PrincipalAtlas
