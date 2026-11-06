import Red61
import Lean.Util.CollectAxioms

#print axioms Red61.Contraction.exists_theorem61_omega_rationalBase

-- Audit every declaration owned by a project module, including auxiliary definitions.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let mod ← env.header.moduleNames[idx.toNat]?
    if mod == `Red61 || (`Red61).isPrefixOf mod then some name else none
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
-- other constants keep their names. verify.py compares it with the pinned value.
open Lean Elab Command

/-- Project constants whose names carry no meaning: private, auxiliary or instances. -/
def isAnonymous (env : Environment) (c : Name) : Bool :=
  (privateToUserName? c).isSome || Meta.isInstanceCore env c ||
    c.components.any fun s =>
      let t := s.toString
      t.startsWith "_" || t.startsWith "match_" || t.startsWith "proof_"

def inProject (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => (`Red61).isPrefixOf env.header.moduleNames[i.toNat]!
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

run_elab do
  let env ← getEnv
  let root := `Red61.Contraction.exists_theorem61_omega_rationalBase
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
  logInfo m!"Statement fingerprint: {rows.size} constants, {fp}."
