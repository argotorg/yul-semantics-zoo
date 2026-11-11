import Lean.Data.Json
import Fuzz.YulGen
import YulSemnaticsZoo.Yul.Parser

/-!
# Fuzzing the Yul parser against solc

For a random object `o` (`Fuzz.Yul.object`) and random text for it (`Fuzz.Yul.text`):
- our parser parses the text to `o`;
- solc accepts the text, and our parser parses the printout of solc (the `ir` output of
  `solc --standard-json`, which solc prints from its AST before any change to it) to `o`.

Then for the text with one character changed (`mutate`): if the parser of solc rejects it, ours
does; if only the analysis of solc rejects it, ours accepts it; if solc accepts it, ours parses it
to the AST of the solc printout (`checkMutation`, `solc`). Errors of solc about builtins (its
parser knows the dialect, ours does not), internal errors of solc, and names that solc does not
print back (`plainNames`) tell nothing about our parser, so these cases are skipped.

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
  let json ← IO.ofExcept (Json.parse out.stdout)
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
  let internal := errors.any fun e =>
    !["ParserError", "SyntaxError", "DeclarationError", "TypeError"].any (typed e)
  if internal || errors.any (has · "uiltin function") then return .failed message
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

/-- the names of objects and data are printable ASCII without `\` and `"`: solc prints names
without escapes (and fails on other names, see `Solc.failed`), so only these come back the same
in its printout -/
partial def plainNames (o : Object) : Bool :=
  let plain (s : String) := s.toList.all fun c => ' ' ≤ c && c ≤ '~' && c != '\\' && c != '"'
  plain o.name && o.data.all (plain ·.name) && o.objects.all plainNames

/-- our parse of the solc printout of `o` is `o` -/
def sameAsSolc (o : Object) (contracts : Json) (text : String) : Option String :=
  if !plainNames o then none else
  match ir contracts o.name with
  | none => some s!"solc has no printout of {o.name} for\n{text}"
  | some ir =>
    match Object.parse ir with
    | .error e => some s!"we do not parse the solc printout\n{ir}\n{e}"
    | .ok theirs =>
      if theirs.print != o.print then
        some s!"solc parses\n{text}\nas\n{theirs.print}\nnot\n{o.print}"
      else none

/-- a difference between solc and us on `o` and its text -/
def check (o : Object) (text : String) : IO (Option String) := do
  match Object.parse text with
  | .error e => return some s!"we do not parse\n{text}\n{e}"
  | .ok ours =>
    if ours.print != o.print then
      return some s!"we parse\n{text}\nas\n{ours.print}\nnot\n{o.print}"
    match ← solc text with
    | .accepted contracts => return sameAsSolc o contracts text
    | .parseError e | .analysisError e | .failed e =>
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
accepts it, we parse it to the AST of the solc printout; if only the analysis of solc rejects
it, we parse it; if the parser of solc rejects it, we do not parse it -/
def checkMutation (text : String) : IO (Option String) := do
  -- solc parses its printout again, which has names without escapes, so it reads names that
  -- are not plain in other ways
  if let .ok o := Object.parse text then
    if !plainNames o then return none
  match Object.parse text, ← solc text with
  | .ok ours, .accepted contracts => return sameAsSolc ours contracts text
  | .ok _, .analysisError _ | .error _, .parseError _ | _, .failed _ => return none
  | .ok ours, .parseError e =>
    return some s!"we parse\n{text}\nas\n{ours.print}\nsolc does not\n{e}"
  | .error e, .accepted _ => return some s!"solc accepts, we do not parse\n{text}\n{e}"
  | .error e, .analysisError a =>
    return some s!"solc parses, we do not parse\n{text}\n{e}\nsolc: {a}"

/-- check `k` cases from `g`: the first difference, and the number of its case -/
def run (g : StdGen) (i : Nat) : Nat → IO (Option (Nat × String))
  | 0 => return none
  | k + 1 => do
    let ((o, text, mutated), g) := Id.run do
      let ((o, _), g) := (object 1 |>.run 0).run g
      let (text, g) := (Yul.text (tokens (o.pieces 0))).run g
      let (mutated, g) := (mutate text).run g
      return ((o, text, mutated), g)
    match ← check o text with
    | some err => return some (i, err)
    | none =>
      match ← checkMutation mutated with
      | some err => return some (i, err)
      | none => run g (i + 1) k

/-- `[cases] [seed]`: check `cases` cases (100 if not given) from `seed` (the clock if not
given); 0 if there are no differences -/
def fuzz (args : List String) : IO UInt32 := do
  let cases := (args[0]? >>= String.toNat?).getD 100
  let seed ← match args[1]? >>= String.toNat? with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 2 ^ 32)
  IO.println s!"yul fuzz seed {seed}: {cases} cases"
  (← IO.getStdout).flush
  match ← run (mkStdGen seed) 0 cases with
  | some (i, err) => IO.eprintln s!"case {i}: {err}"; return 1
  | none => IO.println "no differences"; return 0

end Fuzz.Yul
