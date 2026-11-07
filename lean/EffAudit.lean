import Eff
import SurfaceLib
import Lean.Util.CollectAxioms

#print axioms Eff.quotient_properties
#print axioms Eff.Canonical.canonicalSheaf_trivial
#print axioms Eff.Canonical.exists_trivial_canonicalSheaf
#print axioms SurfaceLib.Canonical.comparisonIso
#print axioms SurfaceLib.Canonical.comparisonHom_trans
#print axioms Eff.invariant_chart_unit_constant
#print axioms Eff.euler_fifth
#print axioms Eff.euler_bracket_delta
#print axioms SurfaceLib.WeightFive.exists_weight_decomposition
#print axioms SurfaceLib.WeightFive.weight_decomposition_unique
#print axioms Eff.GeometricObstruction.parametrization_equation
#print axioms Eff.GeometricObstruction.parametrization_zPartial
#print axioms SurfaceLib.span_top_of_fifth_power_lifts
#print axioms Eff.sChartEuler_overlap_left
#print axioms Eff.sChartEuler_overlap_right
#print axioms Eff.certificate_span_top
#print axioms Eff.sChartEuler_nowhereVanishing
#print axioms Eff.rho_is_muFiveTorsor
#print axioms Eff.rho_has_gradedTorsor
#print axioms Eff.rho_action_weights
#print axioms Eff.rho_flat
#print axioms Eff.rho_rankFive
#print axioms Eff.y_stalk_regular
#print axioms Eff.yAbsoluteDifferentials_isLocallyFreeOfRank
#print axioms Eff.y_lattice
#print axioms SurfaceLib.LineBundle.generators_of_trivial
#print axioms SurfaceLib.LineBundle.trivial_of_generators
#print axioms Eff.tensorPower_trivial_iff
#print axioms Eff.omega_tensorPower_trivial_iff
#print axioms Eff.canonicalSheaf_tensorPower_trivial_iff
#print axioms Eff.canonicalSheaf_order_five
#print axioms Eff.y_not_geometrically_normal
#print axioms SurfaceLib.Projective.AtlasModel.iso
#print axioms Eff.y_projective
#print axioms SurfaceLib.Abelian.isParaAbelianVariety_id
#print axioms Eff.y_albanese_is_base
#print axioms Eff.y_example
#print axioms Eff.case_C_p5

#check Eff.quotient_properties
#check Eff.Canonical.canonicalSheaf_trivial
#check @Eff.Canonical.exists_trivial_canonicalSheaf
#check Eff.sChartEuler_nowhereVanishing
#check Eff.rho_is_muFiveTorsor
#check Eff.y_stalk_regular
#check Eff.omega_tensorPower_trivial_iff
#check @Eff.canonicalSheaf_tensorPower_trivial_iff
#check @Eff.canonicalSheaf_order_five
#check Eff.y_not_geometrically_normal
#check Eff.y_projective
#check @Eff.y_albanese_is_base
#check Eff.y_example
#check @Eff.case_C_p5

-- The definitions these statements rely on, printed in full.
#print Eff.IsNormalScheme
#print SurfaceLib.Projective.IsProjectiveOver
#print SurfaceLib.Abelian.IsParaAbelianVariety
#print SurfaceLib.Abelian.IsAlbaneseMorphism
#print SurfaceLib.LineBundle.tensorPower

-- Parameters do not appear in logical dependency reports: export their actual checked types.
open Lean Elab Command in
run_elab do
  let fields := #[`SurfaceLib.Abelian.ClassicalRationalRigidity.constant,
    `SurfaceLib.Canonical.ClassicalAdjunction.normalizedDuality,
    `SurfaceLib.Canonical.TopDuality.finitePresentation,
    `SurfaceLib.Canonical.TopDuality.trace, `SurfaceLib.Canonical.TopDuality.perfect,
    `SurfaceLib.Canonical.tracePairing, `SurfaceLib.Canonical.Cohomology,
    `SurfaceLib.MuFive.ClassicalDiagonalizableQuotient.torsor,
    `SurfaceLib.MuFive.HomogeneousCover.size, `SurfaceLib.MuFive.HomogeneousCover.value,
    `SurfaceLib.MuFive.HomogeneousCover.weight, `SurfaceLib.MuFive.HomogeneousCover.eigen,
    `SurfaceLib.MuFive.HomogeneousCover.nonzero, `SurfaceLib.MuFive.HomogeneousCover.spans,
    `SurfaceLib.MuFive.group, `SurfaceLib.MuFive.pullGroup,
    `SurfaceLib.MuFive.PointOver, `SurfaceLib.MuFive.pullPoint,
    `SurfaceLib.MuFive.Torsor.finite, `SurfaceLib.MuFive.Torsor.flat,
    `SurfaceLib.MuFive.Torsor.surjective, `SurfaceLib.MuFive.Torsor.act,
    `SurfaceLib.MuFive.Torsor.one_act, `SurfaceLib.MuFive.Torsor.mul_act,
    `SurfaceLib.MuFive.Torsor.natural, `SurfaceLib.MuFive.Torsor.principal,
    `SurfaceLib.MuFive.Torsor.rankFive, `SurfaceLib.MuFive.chartSection,
    `SurfaceLib.MuFive.GradedTorsor.toTorsor, `SurfaceLib.MuFive.GradedTorsor.weights]
  let entries ← fields.mapM fun name => do
    let ty ← Meta.ppExpr (← getConstInfo name).type
    pure <| Json.mkObj [("declaration", toJson name.toString), ("type", toJson ty.pretty)]
  logInfo m!"Classical input interface: {(Json.arr entries).compress}"

namespace EffAudit

-- Audit every declaration owned by a project module, including auxiliary definitions.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let mod ← env.header.moduleNames[idx.toNat]?
    if (`Red61).isPrefixOf mod || (`Eff).isPrefixOf mod ||
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
-- other constants keep their names. verify_eff.py compares the pinned values.
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
    (`Red61).isPrefixOf mod || (`Eff).isPrefixOf mod || (`SurfaceLib).isPrefixOf mod
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
  auditStatement `Eff.quotient_properties "Eff"
  auditStatement `Eff.Canonical.canonicalSheaf_trivial "Canonical"
  auditStatement `Eff.sChartEuler_nowhereVanishing "Freeness"
  auditStatement `Eff.rho_is_muFiveTorsor "Torsor"
  auditStatement `Eff.y_stalk_regular "Regularity"
  auditStatement `Eff.omega_tensorPower_trivial_iff "Order"
  auditStatement `Eff.canonicalSheaf_order_five "CanonicalOrder"
  auditStatement `Eff.y_not_geometrically_normal "Nonnormal"
  auditStatement `Eff.y_projective "Projective"
  auditStatement `Eff.y_albanese_is_base "Albanese"
  auditStatement `Eff.y_example "Example"
  auditStatement `Eff.case_C_p5 "Final"

end EffAudit
