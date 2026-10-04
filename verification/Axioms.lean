import ComplexCSP
import Lean
import Lean.Util.CollectAxioms

/-! Audit every declaration originating in the production libraries, including
private declarations, together with its transitive proof dependencies. -/
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

elab "#audit_production_axioms" : command => do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (name, _) => do
    let index ← env.getModuleIdxFor? name
    let origin := env.header.moduleNames[index.toNat]!.toString
    if origin == "ComplexCSP" || origin.startsWith "ComplexCSP." ||
        origin.startsWith "PlanarHom." then some name else none
  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for axiomName in state.axioms do
    unless allowed.contains axiomName do
      throwError "Unpermitted production axiom: {axiomName}"
  logInfo m!"Audited {roots.length} production declarations; axiom dependencies: {state.axioms}"

#audit_production_axioms

namespace VerificationAudit
structure DeclarationEntry where
  name : String
  file : String
  deriving FromJson
structure PaperItem where
  declarations : Array DeclarationEntry
  deriving FromJson
structure PaperMap where
  statements : Array PaperItem
  deriving FromJson
end VerificationAudit

elab "#audit_paper_declarations" : command => do
  let env ← getEnv
  let source ← liftIO <| IO.FS.readFile "verification/paper.json"
  let json ← liftIO <| IO.ofExcept <| Json.parse source
  let mapping : VerificationAudit.PaperMap ← liftIO <| IO.ofExcept <| fromJson? json
  let mut count := 0
  for item in mapping.statements do
    for entry in item.declarations do
      let name := entry.name.toName
      unless env.contains name do
        throwError "Missing mapped declaration: {name}"
      let some index := env.getModuleIdxFor? name |
        throwError "Mapped declaration has no source module: {name}"
      let moduleName := env.header.moduleNames[index.toNat]!.toString
      let file := moduleName.replace "." "/" ++ ".lean"
      unless file == entry.file do
        throwError "Incorrect source for {name}: map says {entry.file}, actual source is {file}"
      count := count + 1
  logInfo m!"Paper map checked against {count} actual declaration entries."

#audit_paper_declarations
