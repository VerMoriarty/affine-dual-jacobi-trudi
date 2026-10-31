import Lean

/-!
Read the compiled environment, including private declarations and theorem bodies.
This is tooling, not a mathematical assumption.  The checker hashes the raw
output before adding SHA-256 hashes of the printed types.  Run via
`lake env lean --run FidelityLean/Export.lean OUTPUT MODULE ...`.
-/
open Lean Meta

namespace FidelityExport

def namesJson (xs : Array Name) : Json :=
  toJson ((xs.qsort Name.lt).map Name.toString)

def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def isProject (m : Name) : Bool :=
  m == `AffineDualJT || (`AffineDualJT).isPrefixOf m ||
    m == `FidelityLean || (`FidelityLean).isPrefixOf m ||
    m == `Fidelity || (`Fidelity).isPrefixOf m

def declaration (env : Environment) (moduleName name : Name) (c : ConstantInfo) :
    MetaM Json := do
  let ty := (← ppExpr c.type).pretty
  let readableType ← withOptions (fun opts => opts.setBool `pp.all false
    |>.setBool `pp.explicit false |>.setBool `pp.universes false
    |>.setBool `pp.fullNames true) do
      return (← ppExpr c.type).pretty
  let val? := c.value? true
  let vc := val?.map Expr.getUsedConstants |>.getD #[]
  let body ← match c with
    | .defnInfo v => pure <| Json.str (← ppExpr v.value).pretty
    | .opaqueInfo v => pure <| Json.str (← ppExpr v.value).pretty
    | _ => pure Json.null
  let axioms ← collectAxioms name
  pure <| Json.mkObj [
    ("name", toJson name.toString),
    ("module", toJson moduleName.toString),
    ("kind", toJson (kind c)),
    ("level_parameters", toJson (c.levelParams.map Name.toString)),
    ("type", toJson ty),
    ("readable_type", toJson readableType),
    ("type_expression_hash_diagnostic", toJson (toString (hash c.type))),
    ("type_constants", namesJson c.type.getUsedConstants),
    ("value_constants", namesJson vc),
    ("value_available", toJson val?.isSome),
    ("definition", body),
    ("axioms", namesJson axioms),
    ("origin_found", toJson ((env.getModuleIdxFor? name).isSome))]

def exportEnvironment : MetaM Json := do
  let env ← getEnv
  let entries := env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1)
  let mut decls := #[]
  for (name, c) in entries do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if isProject moduleName then
        decls := decls.push (← declaration env moduleName name c)
  pure <| Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("producer", toJson "Lean compiled Environment; private import level; full pretty printer"),
    ("lean_version", toJson Lean.versionString),
    ("imported_modules", toJson (env.header.moduleNames.map Name.toString)),
    ("decls", Json.arr decls)]

end FidelityExport

unsafe def main (args : List String) : IO UInt32 := do
  let output :: modules := args | throw <| IO.userError "usage: Export.lean OUTPUT MODULE ..."
  if modules.isEmpty then
    throw <| IO.userError "explicit compiled module list required"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let options := ({} : Options).setBool `pp.all true |>.set `pp.width (120 : Nat)
    |>.set `maxHeartbeats (0 : Nat) |>.set `maxRecDepth (8192 : Nat)
  let imports := modules.toArray.map (fun n => ({ module := n.toName, importAll := true } : Import))
  let env ← importModules imports options (trustLevel := 0) (loadExts := true)
  let data ← (FidelityExport.exportEnvironment.run').toIO'
    { fileName := "FidelityLean/Export.lean", fileMap := FileMap.ofString "", options := options,
      maxRecDepth := 8192, maxHeartbeats := 0 }
    { env := env }
  IO.FS.writeFile output (data.compress ++ "\n")
  IO.println s!"Exported compiled declarations to {output}"
  return 0
