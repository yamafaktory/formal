import Lean

open Lean Elab Command

namespace FormalAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def foreignAxioms (env : Environment) (locals : NameSet) (name : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := [name]
  let mut foreign : Array Name := #[]
  repeat
    match todo with
    | [] => break
    | used :: rest =>
      todo := rest
      unless seen.contains used do
        seen := seen.insert used
        match env.find? used with
        | some (.axiomInfo _) =>
          unless standardAxioms.contains used do
            foreign := foreign.push used
        | some info =>
          if locals.contains used then
            todo := info.getUsedConstantsAsSet.toList ++ todo
        | none => pure ()
  return foreign

def copyName (name : Name) : Name :=
  .num (name.str "formal") 0

def renamed (names : NameSet) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => if names.contains n then some (.const (copyName n) ls) else none
    | _ => none

def copy (env : Environment) (info : ConstantInfo) : Option Declaration :=
  match info with
  | .thmInfo v => some (.thmDecl { v with name := copyName v.name, all := [copyName v.name] })
  | .defnInfo v =>
    if v.safety == .safe then
      some (.defnDecl { v with name := copyName v.name, all := [copyName v.name] })
    else none
  | .opaqueInfo v =>
    if v.isUnsafe then none
    else some (.opaqueDecl { v with name := copyName v.name, all := [copyName v.name] })
  | .inductInfo v =>
    if v.isUnsafe || v.all.head? != some v.name then none
    else
      let names := v.all.foldl (fun names n =>
        let ctors := match env.find? n with
          | some (.inductInfo iv) => iv.ctors
          | _ => []
        ctors.foldl NameSet.insert (names.insert n)) {}
      let types := v.all.filterMap fun n =>
        match env.find? n with
        | some (.inductInfo iv) =>
          some {
            name := copyName n
            type := renamed names iv.type
            ctors := iv.ctors.filterMap fun c =>
              (env.find? c).map fun ci => { name := copyName c, type := renamed names ci.type }
          }
        | _ => none
      some (.inductDecl v.levelParams v.numParams types false)
  | _ => none

def kernelRejects (env : Environment) (info : ConstantInfo) : IO (Option String) := do
  let some decl := copy env info | return none
  match env.toKernelEnv.addDeclCore 0 0 decl none with
  | .ok _ => return none
  | .error ex => return some (← (ex.toMessageData {}).toString)

partial def lineOf (name : Name) : CommandElabM Json := do
  match ← findDeclarationRanges? name with
  | some ranges => return .num ranges.range.pos.line
  | none => if name.getPrefix.isAnonymous then return .null else lineOf name.getPrefix

def finding (env : Environment) (localNames : NameSet) (name : Name) (info : ConstantInfo)
    (line : Json) : IO (Option Json) := do
  let foreign := foreignAxioms env localNames name
  let rejected ← kernelRejects env info
  if foreign.isEmpty && rejected.isNone then return none
  return some <| Json.mkObj [
    ("name", .str name.toString),
    ("line", line),
    ("axioms", .arr (foreign.map fun ax => .str ax.toString)),
    ("kernel", match rejected with | some why => .str why | none => .null)]

def auditDiscarded : Linter where
  run := fun _ => do
    let kept ← getEnv
    let mut seen : NameSet := {}
    let mut found : Array Json := #[]
    for tree in (← getInfoTrees) do
      for env in tree.foldInfo (init := #[]) fun ctx _ envs => envs.push ctx.env do
        let locals := env.constants.map₂
        let localNames := locals.foldl (fun names name _ => names.insert name) ({} : NameSet)
        for (name, info) in locals.toList do
          unless kept.contains name || seen.contains name do
            seen := seen.insert name
            if let some report ← finding env localNames name info .null then
              found := found.push report
    unless found.isEmpty do
      logInfo m!"formal-audit-discarded {(Json.arr found).compress}"

initialize addLinter auditDiscarded

elab "#formal_audit " nonce:str : command => do
  let env ← getEnv
  let locals := env.constants.map₂
  let localNames := locals.foldl (fun names name _ => names.insert name) ({} : NameSet)
  let mut found : Array Json := #[]
  for (name, info) in locals.toList do
    if let some report ← finding env localNames name info (← lineOf name) then
      found := found.push report
  logInfo m!"formal-audit {nonce.getString} {(Json.arr found).compress}"

elab "#formal_holds " target:str : command => do
  let name := target.getString.toName
  let stated ← getConstInfo name
  let info ← getConstInfo (name.str "holds")
  unless info.levelParams.length == stated.levelParams.length &&
      info.type == mkConst name (info.levelParams.map mkLevelParam) do
    throwError m!"`{name}.holds` does not state `{name}`"

end FormalAudit
