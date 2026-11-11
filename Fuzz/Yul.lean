import Lean.Data.Json
import Fuzz.YulGen
import YulSemnaticsZoo.Yul.WellFormed
import YulSemnaticsZoo.Yul.EVM

/-!
# Fuzzing the Yul parser against solc

For a random object `o` (`Fuzz.Yul.object`) and random text for it (`Fuzz.Yul.text`):
- our parser parses the text to `o`;
- solc accepts the text, and our parser parses the printout of solc (the `ir` output of
  `solc --standard-json`, which solc prints from its AST before any change to it) to `o`.

Then for the text with one character changed (`mutate`): if the parser of solc rejects it, ours
does; if only the analysis of solc rejects it, ours accepts it; if solc accepts it, ours parses it
to the AST of the solc printout (`checkMutation`, `solc`). Errors of solc about builtins (its
parser knows the dialect, ours does not), internal errors of solc, and object names that are not
UTF-8 (solc parses them, ours does not) tell nothing about our parser, so these cases are
skipped.

For `o`, for the text with one character changed that we parse, and for `o` with one change to
its AST (`mutateObject`): solc accepts the object if and only if it is well-formed in the EVM
dialect (`Object.WellFormed`, `checkWellFormed`). Objects that call builtins of solc that are
not builtins of the EVM dialect (`otherBuiltins`) tell nothing about `Object.WellFormed`, so
these cases are skipped. solc accepts some functions in init blocks, which the docs forbid
(`functionInInit`), so these cases are skipped too.

Two valid ASTs are equal if their printouts are equal, since `Object.parse_print` makes printing
injective on valid ASTs.
-/

namespace Fuzz.Yul
open Lean _root_.Yul

/-- what solc does with a text -/
inductive Solc where
  /-- solc accepts the text; its output for the source -/
  | accepted (contracts : Json)
  /-- the parser of solc rejects the text -/
  | parseError (message : String)
  /-- solc parses the text, but its analysis rejects it -/
  | analysisError (message : String)
  /-- solc rejects the text for its use of builtins: this can be in its parser, which knows the
  dialect -/
  | builtinError (message : String)
  /-- the analysis of solc accepts the text, but a later step fails (an internal error, or an error
  of the code generator), so there is no printout -/
  | assemblyFailed (message : String)
  /-- solc fails (an internal error), so it tells nothing about the text -/
  | failed (message : String)

/-- solc on `text`, with the optimizer off and the `ir` output -/
def solc (text : String) : IO Solc := do
  let input := Json.mkObj [
    ("language", "Yul"),
    ("sources", Json.mkObj [("s.yul", Json.mkObj [("content", text)])]),
    ("settings", Json.mkObj [
      ("optimizer", Json.mkObj [("enabled", false)]),
      ("outputSelection", Json.mkObj [("*", Json.mkObj [("*", Json.arr #["ir"])])])])]
  let (h, path) ← IO.FS.createTempFile
  h.putStr input.compress
  h.flush
  let out ← IO.Process.output { cmd := "solc", args := #["--standard-json", path.toString] }
  IO.FS.removeFile path
  let .ok json := Json.parse out.stdout | return .failed s!"{out.stdout}{out.stderr}"
  let errors := ((json.getObjValD "errors").getArr?.toOption.getD #[]).toList.filter fun e =>
    e.getObjValD "severity" == Json.str "error"
  let message := String.intercalate "\n" (errors.map fun e =>
    (e.getObjValD "formattedMessage").getStr?.toOption.getD e.compress)
  let has (e : Json) (s : String) : Bool :=
    ((e.getObjValD "message").getStr?.toOption.getD "" |>.splitOn s).length > 1
  let typed (e : Json) (t : String) : Bool := e.getObjValD "type" == Json.str t
  -- an internal error of solc, or an error about builtins: the parser of solc knows the dialect
  -- and ours does not, and after an error about a builtin (one that is not called, or a builtin
  -- name as an identifier) its parser recovers, so solc tells nothing about the rest
  let analysis (e : Json) :=
    ["ParserError", "SyntaxError", "DeclarationError", "TypeError"].any (typed e)
  -- the errors of the steps after the analysis: solc assembles the code only after the analysis
  -- accepts it
  let assembly (e : Json) :=
    ["InternalCompilerError", "CodeGenerationError", "CompilerError", "YulException"].any (typed e)
  if !errors.isEmpty && errors.all assembly then return .assemblyFailed message
  -- other errors, as `JSONError` for a message that is not UTF-8
  if errors.any (!analysis ·) then return .failed message
  if errors.any (has · "uiltin function") then return .builtinError message
  -- a parser error, or a declared name that ends with `.`; the other syntax errors of solc are
  -- about scope (`break` outside a loop, …), which our parser does not check
  let parseFailed := errors.any fun e =>
    typed e "ParserError" || (typed e "SyntaxError" && has e "is not a valid identifier")
  if parseFailed then return .parseError message
  if !errors.isEmpty then return .analysisError message
  return .accepted ((json.getObjValD "contracts").getObjValD "s.yul")

/-- the solc printout of the object `name` -/
def ir (contracts : Json) (name : String) : Option String :=
  ((contracts.getObjValD name).getObjValD "ir").getStr?.toOption

/-- our parse of the solc printout of `o` is `o` -/
def sameAsSolc (o : Object) (contracts : Json) (text : String) : Option String :=
  match ir contracts o.name with
  | none => some s!"solc has no printout of {o.name} for\n{text}"
  | some ir =>
    match Object.parse ir with
    | .error e => some s!"we do not parse the solc printout\n{ir}\n{e}"
    | .ok theirs =>
      if theirs.print != o.print then
        some s!"solc parses\n{text}\nas\n{theirs.print}\nnot\n{o.print}"
      else none

/-- the names in the code of an object and its sub-objects, each with whether it is the name of
a call -/
partial def allNames (o : Object) : List (Identifier × Bool) :=
  blockNames o.code ++ o.objects.flatMap allNames

/-- the object calls a builtin of solc that is not a builtin of the EVM dialect: solc can accept
it -/
def otherBuiltins (o : Object) : Bool :=
  (allNames o).any fun (x, call) => call && EVM.reserved x && (EVM.builtin x).isNone

/-- the object has a function in the init block of a loop: the docs forbid it anywhere there, but
solc accepts it in the body or post block of a loop in the init block -/
partial def functionInInit (o : Object) : Bool :=
  block false o.code || o.objects.any functionInInit
where
  block (init : Bool) : Block → Bool
    | ⟨ss⟩ => ss.any (stmt init)
  stmt (init : Bool) : Statement → Bool
    | .FunctionDefinition _ _ _ b => init || block init b
    | .Block b | .If _ b => block init b
    | .ForLoop i _ p b => block true i || block init p || block init b
    | _ => false

/-- a difference between solc and `Object.WellFormed` on `o` and its text, if solc accepts it
(`accepted`) or not -/
def wellFormedAsSolc (o : Object) (text : String) (accepted : Bool) : Option String :=
  if otherBuiltins o || (accepted && functionInInit o) ||
    decide (o.WellFormed EVM.dialect) == accepted then none
  else if accepted then some s!"solc accepts\n{text}\nbut it is not well-formed"
  else some s!"solc does not accept\n{text}\nbut it is well-formed"

/-- a difference between solc and `Object.WellFormed` on the printout of `o` -/
def checkWellFormed (o : Object) : IO (Option String) := do
  let text := o.print
  match ← solc text with
  | .accepted _ | .assemblyFailed _ => return wellFormedAsSolc o text true
  | .analysisError e | .builtinError e => return (wellFormedAsSolc o text false).map (· ++ s!"\n{e}")
  | .parseError e => return some s!"the parser of solc rejects the printout\n{text}\n{e}"
  | .failed _ => return none

/-- a difference between solc and us on `o` and its text -/
def check (o : Object) (text : String) : IO (Option String) := do
  match Object.parse text with
  | .error e => return some s!"we do not parse\n{text}\n{e}"
  | .ok ours =>
    if ours.print != o.print then
      return some s!"we parse\n{text}\nas\n{ours.print}\nnot\n{o.print}"
    match ← solc text with
    | .accepted contracts => return wellFormedAsSolc o text true <|> sameAsSolc o contracts text
    | .assemblyFailed _ => return wellFormedAsSolc o text true
    | .parseError e | .analysisError e | .builtinError e | .failed e =>
      return some s!"solc does not accept\n{text}\n{e}"

/-- characters to insert in a text -/
def mutationChars : List Char :=
  ['{', '}', '(', ')', ',', ':', '=', '-', '>', '"', '\\', '/', '*', '\n', ' ', 'x', '0', '1',
   'a', '$', '.', '_', '\'', 'h']

/-- the text with one character deleted, inserted or replaced -/
def mutate (text : String) : Gen String := do
  let cs := text.toList
  let i ← nat 0 (cs.length - 1)
  let c ← pick mutationChars ' '
  return String.ofList <| match ← nat 0 2 with
    | 0 => cs.take i ++ cs.drop (i + 1)
    | 1 => cs.take i ++ c :: cs.drop i
    | _ => cs.take i ++ c :: cs.drop (i + 1)

/-- a difference between solc and us on a text that is not printed from an object: if solc
accepts it, we parse it to a well-formed AST, the AST of the solc printout; if only the analysis
of solc rejects it, we parse it to an AST that is not well-formed; if the parser of solc rejects
it, we do not parse it -/
def checkMutation (text : String) : IO (Option String) := do
  -- our parser rejects object names that are not UTF-8, which solc parses
  if let .error e := Object.parse text then
    if e == utf8NameError then return none
  match Object.parse text, ← solc text with
  | .ok ours, .accepted contracts =>
    return wellFormedAsSolc ours text true <|> sameAsSolc ours contracts text
  | .ok ours, .assemblyFailed _ => return wellFormedAsSolc ours text true
  | .error e, .assemblyFailed a =>
    return some s!"solc analyses, we do not parse\n{text}\n{e}\nsolc: {a}"
  | .ok ours, .analysisError e | .ok ours, .builtinError e =>
    return wellFormedAsSolc ours text false |>.map (· ++ s!"\n{e}")
  | .error _, .parseError _ | .error _, .builtinError _ | _, .failed _ => return none
  | .ok ours, .parseError e =>
    return some s!"we parse\n{text}\nas\n{ours.print}\nsolc does not\n{e}"
  | .error e, .accepted _ => return some s!"solc accepts, we do not parse\n{text}\n{e}"
  | .error e, .analysisError a =>
    return some s!"solc parses, we do not parse\n{text}\n{e}\nsolc: {a}"

/-- check `k` cases from `g`: the first difference and the number of its case, or the number of
changed ASTs that are well-formed -/
def run (g : StdGen) (i wf : Nat) : Nat → IO (Except (Nat × String) Nat)
  | 0 => return .ok wf
  | k + 1 => do
    let ((o, text, mutated, changed), g) := Id.run do
      let ((o, _), g) := (object 1 |>.run 0).run g
      let (text, g) := (Yul.text (tokens (o.pieces 0))).run g
      let (mutated, g) := (mutate text).run g
      let (changed, g) := (mutateObject o).run g
      return ((o, text, mutated, changed), g)
    let wf := wf + if decide (changed.WellFormed EVM.dialect) then 1 else 0
    match ← check o text with
    | some err => return .error (i, err)
    | none =>
      match ← checkMutation mutated with
      | some err => return .error (i, err)
      | none =>
        match ← checkWellFormed changed with
        | some err => return .error (i, err)
        | none => run g (i + 1) wf k

/-- `[cases] [seed]`: check `cases` cases (100 if not given) from `seed` (the clock if not
given); 0 if there are no differences -/
def fuzz (args : List String) : IO UInt32 := do
  let cases := (args[0]? >>= String.toNat?).getD 100
  let seed ← match args[1]? >>= String.toNat? with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 2 ^ 32)
  IO.println s!"yul fuzz seed {seed}: {cases} cases"
  (← IO.getStdout).flush
  match ← run (mkStdGen seed) 0 0 cases with
  | .error (i, err) => IO.eprintln s!"case {i}: {err}"; return 1
  | .ok wf =>
    IO.println s!"no differences ({wf} of {cases} changed ASTs are well-formed)"; return 0


end Fuzz.Yul
