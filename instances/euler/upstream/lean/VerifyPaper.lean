import TorusEuler
import Lean.Util.CollectAxioms

/-! Checks the frozen paper's assertion inventory against the aggregate
Lean import. The Markdown ledger records the clause correspondence. -/

open Lean Elab Command

namespace PaperCoverage

private structure Row where
  result : String
  anchor : String
  sourcePath : String
  sourceLine : Nat
  status : String
  decls : List String

-- This inventory follows theorem numbering in the frozen main and auxiliary TeX.
private def expected : List (String × String) :=
  [
    ("Theorem 1.1", "cc:target:unforced"),
    ("Remark 1.2", "unlabeled-remark-1.2"),
    ("Lemma 1.3", "cc:uf:tower:lem:slow-orders"),
    ("Lemma 2.1", "cc:lem:wave"),
    ("Lemma 2.2", "cc:lem:frame"),
    ("Lemma 2.3", "cc:uf:exact:lem:additive"),
    ("Lemma 2.4", "cc:lem:model"),
    ("Lemma 2.5", "cc:lem:finite-comparison"),
    ("Proposition 2.6", "cc:prop:finite-return"),
    ("Lemma 3.1", "cc:uf:exact:lem:profile"),
    ("Lemma 4.1", "cc:uf:mean:hardy"),
    ("Theorem 4.2", "cc:uf:mean:inverse"),
    ("Proposition 5.1", "cc:uf:trunc:prop:parent"),
    ("Proposition 5.2", "cc:uf:mean:columns"),
    ("Lemma 5.3", "cc:uf:tower:lem:inverse"),
    ("Proposition 5.4", "cc:uf:hier:prop:identity"),
    ("Lemma 5.5", "cc:uf:hier:lem:relay"),
    ("Theorem 5.6", "cc:uf:hier:thm:depth"),
    ("Lemma 5.7", "cc:uf:hier:lem:physical"),
    ("Lemma 5.8", "cc:uf:step:lem:approximate"),
    ("Lemma 5.9", "cc:uf:step:lem:pressure-center"),
    ("Lemma 5.10", "cc:uf:step:lem:flow-bounds"),
    ("Proposition 5.11", "cc:uf:step:thm:step"),
    ("Lemma 6.1", "cc:uf:base:lem:first"),
    ("Theorem 7.1", "cc:uf:tower:thm:finite"),
    ("Proposition 8.1", "cc:uf:terminal:agreement"),
    ("Proposition 8.2", "cc:uf:terminal:velocity-curl"),
    ("Corollary 8.3", "cc:uf:terminal:time"),
    ("Proposition 8.4", "cc:uf:terminal:off-origin"),
    ("Theorem A.1", "cc:holder:linear"),
    ("Lemma A.2", "cc:holder:freezing"),
    ("Lemma B.1", "cc:uf:trunc:lem:cutoff"),
    ("Lemma D.1", "cc:uf:trunc:lem:fields"),
    ("Lemma D.2", "cc:uf:trunc:lem:coefficients"),
    ("Lemma D.3", "cc:uf:trunc:lem:lifting"),
    ("Auxiliary Theorem 1.1", "aux:terminal:smooth"),
    ("Auxiliary Lemma 1.2", "aux:terminal:mixed"),
    ("Auxiliary Lemma 1.3", "aux:terminal:time")
  ]

private def trim (s : String) : String := s.trimAscii.toString

private def quoted (s : String) : List String :=
  (s.splitOn "`").zipIdx.filterMap fun (value, index) =>
    if index % 2 = 1 then some value else none

private def parseRow (line : String) : Except String (Option Row) := do
  if !line.startsWith "| " then return none
  match (line.splitOn "|").map trim with
  | ["", result, source, status, declarations, _note, ""] =>
    if result == "Result" || result == "---" then return none
    let [anchor] := quoted source | throw s!"Expected one TeX anchor in {result}"
    let [_, link] := source.splitOn "](" | throw s!"Expected a TeX source link in {result}"
    let [target, ""] := link.splitOn ")" | throw s!"Malformed TeX source link in {result}"
    let [sourcePath, lineText] := target.splitOn "#L" |
      throw s!"Expected a TeX source line number in {result}"
    let some (sourceLine + 1) := lineText.toNat? |
      throw s!"Expected a positive TeX source line number in {result}"
    unless ["Verified", "Partial", "Pending"].contains status do
      throw s!"Unknown coverage status for {result}: {status}"
    return some ⟨result, anchor, sourcePath, sourceLine + 1, status, quoted declarations⟩
  | _ => throw s!"Malformed paper coverage row: {line}"

private def checkSource (row : Row) : CommandElabM Unit := do
  let frozenPath := "frozen/torus-rewrite/src/paper/craik_criminale_rewrite/"
  if row.result.startsWith "Auxiliary " then
    unless row.sourcePath == frozenPath ++ "auxiliary/terminal_smoothness.tex" do
      throwError "Expected the frozen auxiliary source for {row.result}"
  else
    let sections := frozenPath ++ "sections/"
    let ["", file] := row.sourcePath.splitOn sections |
      throwError "Expected a frozen main-paper section for {row.result}"
    unless !file.contains '/' && file.endsWith ".tex" do
      throwError "Malformed frozen section path for {row.result}"
  let kind ← match row.result.splitOn " " with
    | [kind, _] | ["Auxiliary", kind, _] => pure kind.toLower
    | _ => throwError "Malformed result number {row.result}"
  let source ← IO.FS.readFile ("../" ++ row.sourcePath)
  let some line := (source.splitOn "\n")[row.sourceLine - 1]? |
    throwError "Missing source line {row.sourceLine} for {row.result}"
  let environment := "\\begin{" ++ kind ++ "}"
  let location := s!"{row.sourcePath}#L{row.sourceLine}"
  unless (trim line).startsWith environment do
    throwError "{row.result} must start a {kind} environment at {location}"
  let labels := line.splitOn "\\label{"
  if row.anchor == "unlabeled-remark-1.2" then
    unless labels.length == 1 do
      throwError "Expected the unlabeled remark at {location}"
  else
    let [_, actual] := labels | throwError "Expected exactly one TeX label at {location}"
    unless actual.startsWith (row.anchor ++ "}") do
      throwError "Expected the TeX label {row.anchor} at {location}"

private def declName (s : String) : Name :=
  (s.splitOn ".").foldl Name.str .anonymous

private def checkTheorem (env : Environment) (anchor label : String) : CommandElabM Unit := do
  let name := declName label
  unless s!"{name}".startsWith "TorusEuler." do
    throwError "{anchor} must name a TorusEuler theorem, got {name}"
  let some (.thmInfo _) := env.find? name |
    throwError "{anchor} requires the imported theorem {name}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms name do
    unless allowed.contains axiomName do
      throwError "{anchor} theorem {name} depends on an unexpected axiom {axiomName}"

private def checkEndpoint (env : Environment) (proof proposition : Name) : CommandElabM Unit := do
  let some (.thmInfo info) := env.find? proof |
    throwError "Expected the unconditional proof {proof}"
  unless info.type == mkConst proposition do
    throwError "Expected {proof} to have the exact type {proposition}"

run_cmd do
  let ledger ← IO.FS.readFile "../paper-coverage.md"
  let mut rows : Array Row := #[]
  for line in ledger.splitOn "\n" do
    match parseRow line with
    | .error error => throwError "{error}"
    | .ok none => pure ()
    | .ok (some row) => rows := rows.push row
  for (result, anchor) in expected do
    let hits := rows.filter fun row => row.anchor == anchor
    unless hits.size == 1 do
      throwError "Expected exactly one row for {result} ({anchor}), found {hits.size}"
    let some row := hits[0]? | throwError "Missing row for {anchor}"
    unless row.result == result do
      throwError "The number or environment in {anchor} must be {result}"
    checkSource row
  unless rows.size == expected.length do
    throwError "Expected {expected.length} rows in the frozen inventory, found {rows.size}"
  let env ← getEnv
  let mut verified : Nat := 0
  let mut openRows : Array String := #[]
  for row in rows do
    if row.status == "Verified" then
      if row.decls.isEmpty then
        throwError "Verified result {row.anchor} requires at least one Lean theorem"
      for name in row.decls do
        checkTheorem env row.anchor name
      if row.anchor == "cc:target:unforced" then
        unless row.decls.contains "TorusEuler.theorem11" do
          throwError "The main theorem row must include TorusEuler.theorem11"
        checkEndpoint env `TorusEuler.theorem11 `TorusEuler.Theorem11
      if ["unlabeled-remark-1.2", "aux:terminal:smooth"].contains row.anchor then
        unless row.decls.contains "TorusEuler.auxiliaryTerminalSmoothness" do
          throwError "The terminal extension row must include TorusEuler.auxiliaryTerminalSmoothness"
        checkEndpoint env `TorusEuler.auxiliaryTerminalSmoothness `TorusEuler.AuxiliaryTerminalSmoothness
      verified := verified + 1
    else
      openRows := openRows.push row.result
  if (← IO.getEnv "TORUS_PAPER_REQUIRE_COMPLETE") == some "1" && !openRows.isEmpty then
    throwError "Unverified frozen statements: {String.intercalate ", " openRows.toList}"
  logInfo m!"Checked {verified} verified paper assertions out of {rows.size}"
  unless openRows.isEmpty do
    logInfo m!"Unverified paper assertions: {String.intercalate ", " openRows.toList}"

end PaperCoverage
