/-
Copyright (c) 2026 lean-exposition contributors.
Released under Apache 2.0; see LICENSE.

This template is appended to an import header by verification.py. It reads
elaborated expressions; it does not certify manuscript correspondence.
The traversal follows Lean's public FoldConsts and CollectAxioms APIs and
the structural cases used by leanprover/comparator's runForUsedConsts.
Structural cases adapted from Comparator/Util.lean, Copyright (c) 2025
Lean FRO, LLC, author Henrik Böving, released under Apache 2.0.
Source: https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Comparator/Util.lean
-/

open Lean
namespace LeanExpositionExtraction

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient_primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

private def structuralDependencies : ConstantInfo → Array Name
  | .inductInfo v => v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => #[v.induct]
  | .recInfo v => v.rules.foldl (init := #[]) fun acc r =>
      acc.push r.ctor ++ r.rhs.getUsedConstants
  | _ => #[]

private def namesJson (ns : Array Name) : Json :=
  toJson (ns.map Name.toString)

private def inspect : CoreM Json := do
  let roots : Array Name := __LEAN_EXPOSITION_ROOTS__
  let prefixes : Array Name := __LEAN_EXPOSITION_PREFIXES__
  let limit : Nat := __LEAN_EXPOSITION_LIMIT__
  let env := (← getEnv).setExporting false
  for root in roots do
    unless (env.find? root).isSome do
      throwError "requested declaration not found: {root}"
  let mut todo := roots.toList
  let mut visited : NameSet := {}
  let mut declarations : Array Json := #[]
  let mut externals : Array Json := #[]
  let mut missing : Array Name := #[]
  let mut unexpanded : Array Name := #[]
  let mut unavailableBodies : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n
      | missing := missing.push n; continue
    let mod := moduleOf env n
    let inScope := roots.contains n || prefixes.any (·.isPrefixOf mod)
    unless inScope do
      externals := externals.push <| Json.mkObj [
        ("name", toJson n.toString), ("module", toJson mod.toString),
        ("kind", toJson (declarationKind ci)),
        ("reason", toJson "outside_module_prefixes")]
      continue
    if declarations.size >= limit then
      unexpanded := unexpanded.push n
      continue
    let typeDeps := ci.type.getUsedConstants
    let value? := ci.value? (allowOpaque := true)
    let bodyExpected := match ci with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
      | _ => false
    if bodyExpected && value?.isNone then
      unavailableBodies := unavailableBodies.push n
    let valueDeps := value?.map Expr.getUsedConstants |>.getD #[]
    let structuralDeps := structuralDependencies ci
    let deps := typeDeps ++ valueDeps ++ structuralDeps
    todo := deps.toList ++ todo
    let ty := toString ci.type
    let axioms ← collectAxioms n
    let ranges? ← findDeclarationRanges? n
    let source := Json.mkObj [
      ("module", toJson mod.toString),
      ("line", ranges?.map (fun r => toJson r.range.pos.line) |>.getD Json.null),
      ("column", ranges?.map (fun r => toJson r.range.pos.column) |>.getD Json.null),
      ("end_line", ranges?.map (fun r => toJson r.range.endPos.line) |>.getD Json.null)]
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson n.toString), ("kind", toJson (declarationKind ci)),
      ("type", toJson ty), ("type_dependencies", namesJson typeDeps),
      ("value_dependencies", namesJson valueDeps),
      ("structural_dependencies", namesJson structuralDeps),
      ("axioms", namesJson axioms),
      ("has_sorry", toJson (axioms.contains ``sorryAx)),
      ("body_available", toJson value?.isSome), ("source", source)]
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("module", toJson __LEAN_EXPOSITION_MODULE__),
    ("roots", namesJson roots), ("module_prefixes", namesJson prefixes),
    ("declarations", toJson declarations), ("external_dependencies", toJson externals),
    ("missing_declarations", namesJson missing),
    ("unexpanded_declarations", namesJson unexpanded),
    ("unavailable_bodies", namesJson unavailableBodies),
    ("scope_complete", toJson (missing.isEmpty && unexpanded.isEmpty && unavailableBodies.isEmpty)),
    ("type_rendering", toJson "Lean.Expr.dbgToString"),
    ("evidence_kind", toJson "elaborated_expression_dependencies")]

end LeanExpositionExtraction

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := __LEAN_EXPOSITION_TARGET__ }] {}
    (loadExts := true) (level := .private)
  let report ← Lean.Core.CoreM.toIO' LeanExpositionExtraction.inspect
    { fileName := "<extractor>", fileMap := Lean.FileMap.ofString "" } { env := env }
  IO.println ("LEAN_EXPOSITION_JSON:" ++ report.compress)
