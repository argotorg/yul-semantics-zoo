import YulSemnaticsZoo.Yul.Lexer

set_option doc.verso true

/-!
# Yul: parser

Tokens to a Yul AST, by recursive descent. Each function takes fuel, which each nested call
makes smaller. A call takes a token, or calls a function that takes one, at most two calls
lower: {lit}`parseStatements`, {lit}`parseStatement`, {lit}`parseBlock`. So {lit}`3 * tokens + 1` is
enough fuel.

After a word, the next token tells the statement: {lit}`(` starts a function call, {lit}`,` or
{lit}`:=` an assignment.

Where the grammar and solc 0.8.38 differ, it parses as solc: only a call is an expression
statement, a declared name does not end with {lit}`.` and has no {lit}`..`, and function parameters
can end with a comma. But an object or data name must be UTF-8, since it is a {name}`String`.
-/

namespace Yul

def keywords : List String :=
  ["function", "let", "if", "switch", "case", "default", "for", "break", "continue", "leave",
   "true", "false", "hex"]

/-- an identifier: a word that is not a keyword -/
def validIdent (s : String) : Bool := isWord s && !keywords.contains s

/-- a name that a declaration declares: an identifier that does not end with {lit}`.` and has no
{lit}`..` (as in solc) -/
def validName (s : String) : Bool :=
  validIdent s && (s.toList.getLast? != some '.' && (s.splitOn "..").length == 1)

def describe : List Token → String
  | t :: _ => s!"unexpected {repr t}"
  | [] => "unexpected end"

def expect (t : Token) : List Token → Except String (List Token)
  | u :: r => if u = t then .ok r else .error s!"expected {repr t}, {describe (u :: r)}"
  | [] => .error s!"expected {repr t}, {describe []}"

/-- a declared name -/
def parseName : List Token → Except String (Identifier × List Token)
  | .Word s :: r => if validName s then .ok (s, r) else .error s!"{s} is not a name"
  | ts => .error s!"expected a name, {describe ts}"

/-- identifiers separated by commas, each satisfying {name}`ok` -/
def parseIdents (ok : String → Bool) : List Token → Except String (List Identifier × List Token)
  | .Word s :: r =>
    if ok s then match r with
      | .Sym .Comma :: r => (parseIdents ok r).map fun (xs, r) => (s :: xs, r)
      | _ => .ok ([s], r)
    else .error s!"{s} is not an identifier"
  | ts => .error s!"expected an identifier, {describe ts}"

/-- identifiers separated by commas, maybe with a comma after the last (as in solc), and the
{lit}`)` after them -/
def parseParamList : List Token → Except String (List Identifier × List Token)
  | .Word s :: r =>
    if validName s then match r with
      | .Sym .Comma :: .Sym .RParen :: r => .ok ([s], r)
      | .Sym .Comma :: r => (parseParamList r).map fun (xs, r) => (s :: xs, r)
      | .Sym .RParen :: r => .ok ([s], r)
      | ts => .error s!"expected , or ), {describe ts}"
    else .error s!"{s} is not an identifier"
  | ts => .error s!"expected an identifier, {describe ts}"

/-- the parameters of a function after its {lit}`(`, and its {lit}`)` -/
def parseParams : List Token → Except String (List Identifier × List Token)
  | .Sym .RParen :: r => .ok ([], r)
  | ts => parseParamList ts

/-- an expression statement, which must be a call (as in solc) -/
def exprStatement : Expression × List Token → Except String (Statement × List Token)
  | (.FunctionCall f args, r) => .ok (.Expression (.FunctionCall f args), r)
  | _ => .error "expected a call or an assignment"

/-- the return variables of a function: none, or {lit}`->` and identifiers -/
def parseRets : List Token → Except String (List Identifier × List Token)
  | .Sym .Arrow :: r => parseIdents validName r
  | ts => .ok ([], ts)

mutual

def parseExpr : Nat → List Token → Except String (Expression × List Token)
  | 0, _ => .error "out of fuel"
  | _ + 1, [] => .error "expected an expression, unexpected end"
  | n + 1, t :: r => match t with
    | .Number k => .ok (.Literal (.NumberLiteral k), r)
    | .Str bs => .ok (.Literal (.StringLiteral bs), r)
    | .Word s =>
      if s = "true" then .ok (.Literal .TrueLiteral, r)
      else if s = "false" then .ok (.Literal .FalseLiteral, r)
      else if validIdent s then match r with
        | .Sym .LParen :: r => (parseArgs n r).map fun (args, r) => (.FunctionCall s args, r)
        | _ => .ok (.Identifier s, r)
      else .error s!"{s} is not an identifier"
    | .Sym _ => .error s!"expected an expression, {describe (t :: r)}"

/-- the arguments of a call after its {lit}`(`, and its {lit}`)` -/
def parseArgs : Nat → List Token → Except String (List Expression × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, ts => match ts with
    | .Sym .RParen :: r => .ok ([], r)
    | _ => do
      let (e, r) ← parseExpr n ts
      let (es, r) ← parseMoreArgs n r
      return (e :: es, r)

/-- the arguments of a call after its first argument, and its {lit}`)` -/
def parseMoreArgs : Nat → List Token → Except String (List Expression × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, ts => match ts with
    | .Sym .RParen :: r => .ok ([], r)
    | .Sym .Comma :: r => do
      let (e, r) ← parseExpr n r
      let (es, r) ← parseMoreArgs n r
      return (e :: es, r)
    | _ => .error s!"expected , or ), {describe ts}"

end

mutual

def parseBlock : Nat → List Token → Except String (Block × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, .Sym .LBrace :: r => (parseStatements n r).map fun (ss, r) => (⟨ss⟩, r)
  | _ + 1, ts => .error s!"expected a block, {describe ts}"

/-- the statements of a block after its {lit}`{`, and its {lit}`}` -/
def parseStatements : Nat → List Token → Except String (List Statement × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, ts => match ts with
    | .Sym .RBrace :: r => .ok ([], r)
    | _ => do
      let (s, r) ← parseStatement n ts
      let (ss, r) ← parseStatements n r
      return (s :: ss, r)

def parseStatement : Nat → List Token → Except String (Statement × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, ts => match ts with
    | .Sym .LBrace :: _ => (parseBlock n ts).map fun (b, r) => (.Block b, r)
    | .Word s :: r =>
      if s = "function" then do
        let (f, r) ← parseName r
        let r ← expect (.Sym .LParen) r
        let (ps, r) ← parseParams r
        let (rs, r) ← parseRets r
        let (b, r) ← parseBlock n r
        return (.FunctionDefinition f ps rs b, r)
      else if s = "let" then do
        let (vs, r) ← parseIdents validName r
        match r with
        | .Sym .Assign :: r =>
          let (e, r) ← parseExpr n r
          return (.VariableDeclaration vs (some e), r)
        | _ => return (.VariableDeclaration vs none, r)
      else if s = "if" then do
        let (c, r) ← parseExpr n r
        let (b, r) ← parseBlock n r
        return (.If c b, r)
      else if s = "for" then do
        let (i, r) ← parseBlock n r
        let (c, r) ← parseExpr n r
        let (p, r) ← parseBlock n r
        let (b, r) ← parseBlock n r
        return (.ForLoop i c p b, r)
      else if s = "break" then .ok (.Break, r)
      else if s = "continue" then .ok (.Continue, r)
      else if s = "leave" then .ok (.Leave, r)
      else match r with
        | .Sym .Comma :: _ | .Sym .Assign :: _ => do
          let (vs, r) ← parseIdents validIdent ts
          let r ← expect (.Sym .Assign) r
          let (e, r) ← parseExpr n r
          return (.Assignment vs e, r)
        | _ => (parseExpr n ts).bind exprStatement
    | _ => (parseExpr n ts).bind exprStatement

end

def utf8NameError : String := "an object or data name must be UTF-8"

/-- the string of the bytes of a string literal, which must be UTF-8 -/
def utf8Name (bs : List UInt8) : Except String String :=
  match String.fromUTF8? ⟨bs.toArray⟩ with
  | some s => .ok s
  | none => .error utf8NameError

/-- the first error in the names of an object, as in solc: a name is empty, a child (an object or
data in it) has the name of the object, or two children have one name -/
def namesError (name : String) (objects : List Object) (data : List Data) : Option String :=
  let children := objects.map (·.name) ++ data.map (·.name)
  if name.isEmpty || children.any (·.isEmpty) then some "an object or data name cannot be empty"
  else if children.contains name then some s!"a child of object {name} has its name"
  else if !decide children.Nodup then some s!"two children of object {name} have one name"
  else none

mutual

def parseObject : Nat → List Token → Except String (Object × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, .Word "object" :: .Str name :: .Sym .LBrace :: .Word "code" :: r => do
    let name ← utf8Name name
    let (code, r) ← parseBlock n r
    let ((objects, data), r) ← parseItems n r
    match namesError name objects data with
    | some e => .error e
    | none => return (⟨name, code, objects, data⟩, r)
  | _ + 1, ts => .error s!"expected object \"name\" \{ code, {describe ts}"

/-- the objects and data of an object after its code, and its {lit}`}` -/
def parseItems : Nat → List Token → Except String ((List Object × List Data) × List Token)
  | 0, _ => .error "out of fuel"
  | n + 1, ts => match ts with
    | .Sym .RBrace :: r => .ok (([], []), r)
    | .Word "data" :: .Str name :: .Str value :: r => do
      let name ← utf8Name name
      let ((os, ds), r) ← parseItems n r
      return ((os, ⟨name, value⟩ :: ds), r)
    | _ => do
      let (o, r) ← parseObject n ts
      let ((os, ds), r) ← parseItems n r
      return ((o :: os, ds), r)

end

/-- parse all of {name}`s` with {name}`p` -/
def parseAll (p : Nat → List Token → Except String (α × List Token)) (s : String) :
    Except String α := do
  let ts ← lex s.toList
  let (a, r) ← p (3 * ts.length + 1) ts
  match r with
  | [] => return a
  | _ => .error (describe r)

def Expression.parse : String → Except String Expression := parseAll parseExpr
def Statement.parse : String → Except String Statement := parseAll parseStatement
def Block.parse : String → Except String Block := parseAll parseBlock
def Object.parse : String → Except String Object := parseAll parseObject

end Yul
