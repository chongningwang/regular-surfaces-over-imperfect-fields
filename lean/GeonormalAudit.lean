import Geonormal
import SurfaceLib
import Lean.Util.CollectAxioms

#print axioms Geonormal.x_projective
#print axioms Geonormal.x_proper
#print axioms Geonormal.x_globalScalarMap_bijective
#print axioms Geonormal.x_stalk_regular
#print axioms Geonormal.x_dimension
#print axioms Geonormal.x_not_smooth
#print axioms Geonormal.x_differentials_locallyFree
#print axioms Geonormal.xRationalVolume_generates
#print axioms Geonormal.xVolumeIso
#print axioms Geonormal.xOmegaIsoStructureSheaf
#print axioms Geonormal.canonicalSheaf_trivial
#print axioms SurfaceLib.Canonical.GeneralClassicalAdjunction.toClassicalAdjunction
#print axioms Geonormal.p19_example
#print axioms Geonormal.p19_canonical
#print axioms Geonormal.P11.x_projective
#print axioms Geonormal.P11.x_proper
#print axioms Geonormal.P11.x_globalScalarMap_bijective
#print axioms Geonormal.P11.x_stalk_regular
#print axioms Geonormal.P11.x_dimension
#print axioms Geonormal.P11.x_not_geometrically_normal
#print axioms Geonormal.P11.x_differentials_locallyFree
#print axioms Geonormal.P11.xRationalVolume_generates
#print axioms Geonormal.P11.xVolumeIso
#print axioms Geonormal.P11.xOmegaIsoStructureSheaf
#print axioms Geonormal.P11.canonicalSheaf_trivial
#print axioms Geonormal.P11.p11_example
#print axioms Geonormal.P11.p11_canonical

#check Geonormal.p19_example
#check @Geonormal.p19_canonical
#check @SurfaceLib.Canonical.GeneralClassicalAdjunction.toClassicalAdjunction
#check Geonormal.P11.p11_example
#check @Geonormal.P11.p11_canonical

-- The surface: chart rings inside the function field F = k(x, t)[y] / (y² - g).
#print Geonormal.k
#print Geonormal.c
#print Geonormal.gPoly
#print Geonormal.quad
#print Geonormal.F
#print Geonormal.monoF
#print Geonormal.first
#print Geonormal.second
#print Geonormal.yScale
#print Geonormal.yc
#print Geonormal.chartRing
#print Geonormal.atlas
#print Geonormal.X19
#print Geonormal.xToBase
#print Geonormal.xOmega
#print SurfaceLib.Canonical.omegaR
#print SurfaceLib.Projective.IsProjectiveOver

-- Proposition prop:p11: chart rings inside the function field L = F₁₁(a, b, σ), over
-- k = F₁₁(c) with c = 6(ab³ - 3a⁴b - σ¹¹).
#print Geonormal.P11.k
#print Geonormal.P11.c
#print Geonormal.P11.L
#print Geonormal.P11.cL
#print Geonormal.P11.algebraKL
#print Geonormal.P11.θE
#print Geonormal.P11.ξ
#print Geonormal.P11.chartA
#print Geonormal.P11.chartB
#print Geonormal.P11.chartD
#print Geonormal.P11.chartP
#print Geonormal.P11.chartRing
#print Geonormal.P11.atlas
#print Geonormal.P11.X11
#print Geonormal.P11.xToBase
#print Geonormal.P11.xOmega
#print SurfaceLib.IsNormalScheme

-- Parameters do not appear in logical dependency reports: export their actual checked types.
open Lean Elab Command in
run_elab do
  let fields := #[`SurfaceLib.Canonical.GeneralClassicalAdjunction.normalizedDuality,
    `SurfaceLib.Canonical.TopDuality.finitePresentation,
    `SurfaceLib.Canonical.TopDuality.trace, `SurfaceLib.Canonical.TopDuality.perfect,
    `SurfaceLib.Canonical.tracePairing, `SurfaceLib.Canonical.Cohomology]
  let entries ← fields.mapM fun name => do
    let ty ← Meta.ppExpr (← getConstInfo name).type
    pure <| Json.mkObj [("declaration", toJson name.toString), ("type", toJson ty.pretty)]
  logInfo m!"Classical input interface: {(Json.arr entries).compress}"

namespace GeonormalAudit

-- Audit every declaration owned by a project module, including auxiliary definitions.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let mod ← env.header.moduleNames[idx.toNat]?
    if (`Red61).isPrefixOf mod || (`Geonormal).isPrefixOf mod ||
        (`SurfaceLib).isPrefixOf mod then some name else none
  let mut count : Nat := 0
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected logical dependency in {name}: {ax}"
    count := count + 1
  logInfo m!"All project declarations audited: {count}."

-- Fingerprint of the main statement, by content. It covers every project constant reachable
-- from the statement through types and definition bodies. References to theorems are erased
-- (proof irrelevance). Private, auxiliary and instance constants are replaced by the hash of
-- their own content, since their names change when declarations move between files; all
-- other constants keep their names. verify_geonormal.py compares the pinned values.
open Lean Elab Command

/-- Project constants whose names carry no meaning: private, auxiliary or instances. -/
def isAnonymous (env : Environment) (c : Name) : Bool :=
  (privateToUserName? c).isSome || Meta.isInstanceCore env c ||
    c.components.any fun s =>
      let t := s.toString
      t.startsWith "_" || t.startsWith "match_" || t.startsWith "proof_"

def inProject (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i =>
    let mod := env.header.moduleNames[i.toNat]!
    (`Red61).isPrefixOf mod || (`Geonormal).isPrefixOf mod || (`SurfaceLib).isPrefixOf mod
  | none => false

/-- Content hash: theorems are erased (proof irrelevance), anonymous project constants are
replaced by the content hash of their own type and body, all other constants keep their name. -/
partial def contentHash (env : Environment) (c : Name) :
    StateM (Std.HashMap Name UInt64) UInt64 := do
  if let some h := (← get)[c]? then return h
  let some ci := env.find? c | return hash c
  let norm (e : Expr) : StateM (Std.HashMap Name UInt64) UInt64 := do
    let mut sub : Std.HashMap Name Expr := {}
    for d in e.getUsedConstants do
      match env.find? d with
      | some (.thmInfo _) => sub := sub.insert d (.const `proof [])
      | _ =>
        if inProject env d && isAnonymous env d then
          let h ← contentHash env d
          sub := sub.insert d (.lit (.natVal h.toNat))
    return (e.replace fun
      | .const d _ => sub[d]?
      | _ => none).hash
  let t ← norm ci.type
  let v ← match ci with
    | .defnInfo d => norm d.value
    | _ => pure 0
  let h := mixHash t v
  modify (·.insert c h)
  return h

def auditStatement (root : Name) (label : String) : TermElabM Unit := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : Array Name := #[root]
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.defnInfo d) =>
      for c in d.type.getUsedConstants ++ d.value.getUsedConstants do
        unless seen.contains c do work := work.push c
    | some (.inductInfo i) =>
      for c in i.type.getUsedConstants ++ i.ctors.toArray do
        unless seen.contains c do work := work.push c
    | some info =>
      for c in info.type.getUsedConstants do
        unless seen.contains c do work := work.push c
    | none => pure ()
  let named := seen.toList.filter fun n => inProject env n && !isAnonymous env n
  let sorted := named.toArray.qsort (fun a b => a.toString < b.toString)
  let (rows, _) := (sorted.mapM fun n => do return (n, ← contentHash env n)).run {}
  let fp := rows.foldl (fun acc r => mixHash acc (mixHash (hash r.1) r.2)) 7
  logInfo m!"{label} statement fingerprint: {rows.size} constants, {fp}."

run_elab do
  auditStatement `Geonormal.p19_example "Example"
  auditStatement `Geonormal.p19_canonical "Final"
  auditStatement `Geonormal.P11.p11_example "P11Example"
  auditStatement `Geonormal.P11.p11_canonical "P11Final"

end GeonormalAudit
