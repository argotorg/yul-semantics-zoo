import Fuzz.Gen
import YulSemnaticsZoo.Yul.Printer

/-!
# Random Yul objects, and random text for them

`object` makes objects that the analysis of solc accepts in the EVM dialect: each name is in
scope and new, each call has the right number of arguments and results, `break` and
`continue` are in a loop body, `leave` is in a function. `text` prints the tokens of an
object with random spellings that the printer does not use: comments, white space, hex
numbers, escapes and hex literals.
-/

namespace Fuzz.Yul
open Fuzz _root_.Yul

/-- a random generator with a counter for new names -/
abbrev YGen := StateT Nat Gen

def fresh (p : String) : YGen String := modifyGet fun k => (p ++ toString k, k + 1)

/-- builtins of the solc EVM dialect with one result: name and number of arguments -/
def builtins1 : List (String × Nat) :=
  [("add", 2), ("sub", 2), ("mul", 2), ("div", 2), ("eq", 2), ("lt", 2), ("gt", 2),
   ("iszero", 1), ("not", 1), ("and", 2), ("or", 2), ("xor", 2), ("mload", 1), ("sload", 1),
   ("gas", 0), ("address", 0), ("caller", 0), ("keccak256", 2)]

/-- builtins of the solc EVM dialect with no result -/
def builtins0 : List (String × Nat) :=
  [("mstore", 2), ("mstore8", 2), ("sstore", 2), ("pop", 1), ("log0", 2), ("revert", 2),
   ("return", 2), ("stop", 0)]

structure Env where
  /-- the variables in scope -/
  vars : List Identifier := []
  /-- the functions in scope: name, number of arguments, number of results -/
  funs : List (Identifier × Nat × Nat) := []
  inLoop : Bool := false
  inFun : Bool := false

instance : Inhabited Env := ⟨{}⟩
instance : Inhabited Block := ⟨⟨[]⟩⟩
instance : Inhabited Statement := ⟨.Break⟩
instance : Inhabited Object := ⟨{ name := "", code := ⟨[]⟩, objects := [], data := [] }⟩

def literal : Gen Literal := do
  match ← nat 0 5 with
  | 0 => return .NumberLiteral (← nat 0 255)
  | 1 => return .NumberLiteral (← nat 0 (2 ^ 256 - 1))
  | 2 => return .NumberLiteral (2 ^ 256 - 1)
  | 3 => return .StringLiteral (← list (← nat 0 32) byte)
  | 4 => return .TrueLiteral
  | _ => return .FalseLiteral

/-- an expression with one value -/
def expr (env : Env) : Nat → Gen Expression
  | 0 => leaf
  | d + 1 => do
    match ← nat 0 3 with
    | 0 => leaf
    | 1 =>
      let (f, k) ← pick builtins1 ("gas", 0)
      return .FunctionCall f (← list k (expr env d))
    | 2 =>
      match env.funs.filter (·.2.2 == 1) with
      | [] => leaf
      | fs =>
        let (f, k, _) ← pick fs ("", 0, 0)
        return .FunctionCall f (← list k (expr env d))
    | _ => leaf
where
  leaf : Gen Expression := do
    if !env.vars.isEmpty && (← coin) then return .Identifier (← pick env.vars "")
    else return .Literal (← literal)

/-- a call with no value -/
def callStmt (env : Env) (d : Nat) : Gen Statement := do
  match env.funs.filter (·.2.2 == 0) with
  | fs@(_ :: _) =>
    if ← coin then
      let (f, k, _) ← pick fs ("", 0, 0)
      return .Expression (.FunctionCall f (← list k (expr env d)))
    else builtin
  | [] => builtin
where
  builtin : Gen Statement := do
    let (f, k) ← pick builtins0 ("stop", 0)
    return .Expression (.FunctionCall f (← list k (expr env d)))

mutual

/-- a block; `funs` allows function definitions in it -/
partial def block (env : Env) (funs : Bool) (d : Nat) : YGen Block := do
  let decls ← if funs && d > 0 then
      (List.range (← nat 0 2)).mapM fun _ => do return (← fresh "f", ← nat 0 3, ← nat 0 2)
    else pure []
  let env := { env with funs := env.funs ++ decls }
  let defs ← decls.mapM fun (f, np, nr) => do
    let ps ← (List.range np).mapM fun _ => fresh "p"
    let rs ← (List.range nr).mapM fun _ => fresh "r"
    let body ← block { vars := ps ++ rs, funs := env.funs, inFun := true } true (d - 1)
    return Statement.FunctionDefinition f ps rs body
  let (ss, _) ← stmts env funs (← nat 0 4) d
  -- the functions of a block are in scope in all of it, so they can be anywhere in it
  let at_ ← nat 0 ss.length
  return ⟨ss.take at_ ++ defs ++ ss.drop at_⟩

/-- `k` statements, and the scope after them -/
partial def stmts (env : Env) (funs : Bool) : Nat → Nat → YGen (List Statement × Env)
  | 0, _ => return ([], env)
  | k + 1, d => do
    let (s, env) ← stmt env funs d
    let (ss, env) ← stmts env funs k d
    return (s :: ss, env)

/-- a statement, and the scope after it -/
partial def stmt (env : Env) (funs : Bool) (d : Nat) : YGen (Statement × Env) := do
  let e := fun (_ : Unit) => (expr env (min d 2) : Gen Expression)
  let multi := env.funs.filter (·.2.2 ≥ 2)
  match ← nat 0 (if d = 0 then 3 else 9) with
  | 0 =>
    let x ← fresh "v"
    if ← coin then
      return (.VariableDeclaration [x] (some (← e ())), { env with vars := x :: env.vars })
    else return (.VariableDeclaration [x] none, { env with vars := x :: env.vars })
  | 1 =>
    match env.vars with
    | [] => return (← callStmt env (min d 2), env)
    | vs => return (.Assignment [← pick vs ""] (← e ()), env)
  | 2 =>
    match multi with
    | [] => return (← callStmt env (min d 2), env)
    | fs =>
      let (f, k, n) ← pick fs ("", 0, 0)
      let call := Expression.FunctionCall f (← list k (expr env (min d 2)))
      let xs ← (List.range n).mapM fun _ => fresh "v"
      if (← coin) && env.vars.length ≥ n then
        return (.Assignment (env.vars.take n) call, env)
      return (.VariableDeclaration xs (some call), { env with vars := xs ++ env.vars })
  | 3 => return (← callStmt env (min d 2), env)
  | 4 => return (.If (← e ()) (← block env funs (d - 1)), env)
  | 5 =>
    let (init, env') ← stmts { env with inLoop := false } false (← nat 0 2) (d - 1)
    let env' := { env' with inLoop := env.inLoop }
    let cond ← expr env' (min d 2)
    let post ← block { env' with inLoop := false } false (d - 1)
    let body ← block { env' with inLoop := true } funs (d - 1)
    return (.ForLoop ⟨init⟩ cond post body, env)
  | 6 => return (.Block (← block env funs (d - 1)), env)
  | 7 =>
    if env.inLoop then return (if ← coin then .Break else .Continue, env)
    else return (← callStmt env (min d 2), env)
  | 8 =>
    if env.inFun then return (.Leave, env) else return (← callStmt env (min d 2), env)
  | _ => return (← callStmt env (min d 2), env)

end

partial def object (d : Nat) : YGen Object := do
  let name ← fresh "O"
  let code ← block {} true 3
  let objects ← if d = 0 then pure [] else (List.range (← nat 0 2)).mapM fun _ => object (d - 1)
  let data ← (List.range (← nat 0 2)).mapM fun _ => do
    return ({ name := ← fresh "D", value := ← list (← nat 0 8) byte } : Data)
  return { name, code, objects, data }

/-! ## Text -/

def hexDigitCase (k : Nat) : Gen Char := do
  let c := hexDigit k
  return if (← coin) then c.toUpper else c

def hexText (k : Nat) : Gen String := do
  let ds := Nat.toDigits 16 k
  return String.ofList (← ds.mapM fun d => do return if (← coin) then d.toUpper else d)

/-- a byte in a string literal, with one of the spellings that mean it -/
def byteText (b : UInt8) : Gen String := do
  let x := s!"\\x{String.ofList [← hexDigitCase (b.toNat / 16), ← hexDigitCase (b.toNat % 16)]}"
  let u := s!"\\u00{String.ofList [← hexDigitCase (b.toNat / 16), ← hexDigitCase (b.toNat % 16)]}"
  let c := Char.ofNat b.toNat
  let spellings :=
    if b = 0x22 then ["\\\""]
    else if b = 0x5c then ["\\\\"]
    else if b = 0x27 then ["'", "\\'", x, u]
    else if b = 0x0a then ["\\n", x, u]
    else if b = 0x0d then ["\\r", x, u]
    else if b = 0x09 then ["\\t", x, u]
    else if 0x20 ≤ b ∧ b < 0x7f then [c.toString, x, u]
    else if b < 0x80 then [x, u]
    else [x]
  pick spellings x

/-- a string literal; a hex literal if `hex` -/
def strText (bs : List UInt8) (hex : Bool) : Gen String := do
  if hex then
    let ds ← bs.mapM fun b => do
      return String.ofList [← hexDigitCase (b.toNat / 16), ← hexDigitCase (b.toNat % 16)]
    -- one `_` can be between two pairs of digits
    let ds ← ds.mapIdxM fun i d => do return if i > 0 && (← coin) then "_" ++ d else d
    return "hex\"" ++ String.join ds ++ "\""
  else
    -- a backslash before a new line is no character
    let parts ← bs.mapM fun b => do
      let cont ← pick ["", "", "", "", "", "\\\n", "\\\r\n", "\\\r"] ""
      return cont ++ (← byteText b)
    return "\"" ++ String.join parts ++ "\""

def tokenText (prev : Option Token) : Token → Gen String
  | .Word s => return s
  | .Number n => do if ← coin then return toString n else return "0x" ++ (← hexText n)
  | .Str bs => do
    -- the name of an object or data is a string literal; a value can be a hex literal
    let name := prev == some (.Word "object") || prev == some (.Word "data")
    strText bs (!name && (← coin))
  | t => return String.ofList t.chars

def wordish : Token → Bool
  | .Word _ | .Number _ => true
  | _ => false

/-- text between two tokens; it must separate a word or number from a word, a number or a
string, which can be a hex literal -/
def gapText (needed : Bool) : Gen String :=
  pick ([" ", "\n", "\t ", "   ", " /* c */ ", " // c\n"] ++ if needed then [] else ["", "/**/"])
    " "

/-- `hist`: the tokens before, the last first; `params`: in the parameters of a function, which
can end with a comma -/
def text (ts : List Token) : Gen String := go [] false ts
where
  go (hist : List Token) (params : Bool) : List Token → Gen String
    | [] => return ""
    | t :: ts => do
      let params' := match t, hist with
        | .Sym .LParen, .Word _ :: .Word "function" :: _ => true
        | .Sym .RParen, _ => false
        | _, _ => params
      let comma ← if t == .Sym .RParen && params && (hist.head? matches some (.Word _)) then
          pick ["", ","] ""
        else pure ""
      let g ← match ts with
        | u :: _ => gapText (wordish t && (wordish u || u matches .Str _))
        | [] => pure ""
      return comma ++ (← tokenText hist.head? t) ++ g ++ (← go (t :: hist) params' ts)

end Fuzz.Yul
