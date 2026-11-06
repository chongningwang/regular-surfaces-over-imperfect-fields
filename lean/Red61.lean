import Red61.LinearAlgebra.ExteriorPower
import Red61.RingTheory.FieldSubalgebra
import Red61.RingTheory.Localization
import Red61.RingTheory.Regular
import Red61.RingTheory.Kaehler
import Red61.RingTheory.PolynomialModels
import Red61.RingTheory.Valuation
import Red61.Foliation
import Red61.AlgebraicGeometry.Differentials.Basic
import Red61.AlgebraicGeometry.Modules
import Red61.AlgebraicGeometry.Atlas
import Red61.AlgebraicGeometry.Differentials.Stalks
import Red61.AlgebraicGeometry.RationalForms.Lattices
import Red61.Surface.Field
import Red61.Surface.Charts
import Red61.Surface.Cone
import Red61.Surface.SixChartModel
import Red61.Surface.ContractionCharts
import Red61.Surface.GeometricNonreduced
import Red61.Surface.ConeStalk
import Red61.Surface.Quotient
import Red61.Surface.Projective
import Red61.Surface.Contraction
import Red61.Surface.ResolvedProperness
import Red61.Surface.Properties
import Red61.Surface.SpecialPointStalk
import Red61.Canonical.InvariantCoordinates
import Red61.Canonical.LocalBases
import Red61.AlgebraicGeometry.StalkCoordinates
import Red61.AlgebraicGeometry.RationalForms.IntegralForms
import Red61.AlgebraicGeometry.ExteriorPower
import Red61.AlgebraicGeometry.RationalForms.ExteriorLattice
import Red61.Surface.BaseDifferentials
import Red61.Canonical.StalkCoordinates
import Red61.Canonical.Volume
import Red61.Canonical.Neighborhoods
import Red61.Canonical.Adjunction
import Red61.Canonical.CINeighborhoods
import Red61.CurveNumericalTriviality
import Red61.Omega
import Red61.Canonical.OmegaTrivialization
import Red61.Theorem61



/-! `Red61.Contraction.exists_theorem61_omega_rationalBase`
(`Red61/Theorem61.lean`) constructs, without geometric inputs, a proper integral
Noetherian regular surface of dimension two over `F₅(s₁,s₂)` with the prescribed
constants, not geometrically reduced. Its sheaf `omega` is defined as the Hom from the
pulled-back base differential determinant to the absolute fourth exterior differential
sheaf. It is isomorphic to the structure sheaf and has Euler degree zero on every proper
integral curve. This library is exactly the import closure of the main theorem.
See README.md. -/
