import Lean

/-!
Print the public `QuarticQuery` projection of the dependency closure from the
named headline theorems. Traverse available types and bodies of intervening
constants in every namespace, including private wrappers and generated helpers,
before filtering the display. `hidden_paths` retains one witness for each edge
through hidden constants; it does not enumerate every possible path. Unresolved
constants are reported explicitly. Run from `lean/` with
`lake env lean --run scripts/Reach.lean <root theorem>...`. Proof bodies are read
from the compiled environment, so this reports what the kernel checked rather than
what a source file mentions.
-/

open Lean

def inProject (n : Name) : Bool :=
  (`QuarticQuery).isPrefixOf n && !n.isInternal

def bodyOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

structure ClosureInspection where
  publicNames : Array Name := #[]
  edges : Array (Name × Array Name) := #[]
  hiddenPaths : Array (Name × Array (Name × Array Name)) := #[]
  unresolved : Array Name := #[]
  traversedConstants : Nat := 0

def inspectClosure (env : Environment) (roots : Array Name) : ClosureInspection := Id.run do
  -- Visit each available constant once, retaining reverse edges for projection.
  -- In particular, do not repeatedly walk Mathlib's common closure for every
  -- public project declaration. External nodes with no path back to a project
  -- declaration are never revisited during the projection below.
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut reverse : Std.HashMap Name (Array Name) := {}
  let mut publicNames : Array Name := #[]
  let mut unresolved : Array Name := #[]
  let mut traversed := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    traversed := traversed + 1
    let some info := env.find? n | unresolved := unresolved.push n; continue
    if inProject n then publicNames := publicNames.push n
    let children := info.type.getUsedConstants ++
      ((bodyOf info).map (·.getUsedConstants)).getD #[]
    for child in children do
      reverse := reverse.insert child ((reverse[child]?).getD #[] |>.push n)
    todo := todo ++ children
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut paths : Std.HashMap Name (Array (Name × Array Name)) := {}
  for target in publicNames do
    let mut visited : NameSet := {}
    let mut pending := ((reverse[target]?).getD #[]).map fun n => (n, (#[] : Array Name))
    while !pending.isEmpty do
      let (n, via) := pending.back!
      pending := pending.pop
      if visited.contains n then continue
      visited := visited.insert n
      if inProject n then
        edges := edges.insert n ((edges[n]?).getD #[] |>.push target)
        if !via.isEmpty then
          paths := paths.insert n ((paths[n]?).getD #[] |>.push (target, via))
      else
        pending := pending ++ ((reverse[n]?).getD #[]).map fun parent => (parent, #[n] ++ via)
  return { publicNames, edges := publicNames.map fun n => (n, (edges[n]?).getD #[]),
           hiddenPaths := publicNames.map fun n => (n, (paths[n]?).getD #[]),
           unresolved, traversedConstants := traversed }

def main (roots : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `QuarticQuery, importAll := true }] {}
    (loadExts := false) (level := .private)
  let env := env.setExporting false
  let inspection := inspectClosure env (roots.toArray.map String.toName)
  let declared := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if inProject n then acc.push n else acc
  let encode (names : Array Name) : Json := toJson (names.map toString |>.qsort (· < ·))
  let edgeJson := Json.mkObj (inspection.edges.toList.map fun (n, deps) => (toString n, encode deps))
  let hiddenJson := Json.mkObj (inspection.hiddenPaths.toList.filterMap fun (n, paths) =>
    if paths.isEmpty then none else some (toString n, toJson (paths.map fun (target, via) =>
      Json.mkObj [("to", toJson (toString target)), ("via", toJson (via.map toString))])))
  IO.println <| (Json.mkObj [("roots", toJson roots), ("reached", encode inspection.publicNames),
    ("declared", encode declared), ("edges", edgeJson), ("hidden_paths", hiddenJson),
    ("unresolved_constants", encode inspection.unresolved),
    ("traversed_constants", toJson inspection.traversedConstants),
    ("traversal_scope", toJson "Available constant types and bodies in all namespaces; public QuarticQuery projection")]).compress
