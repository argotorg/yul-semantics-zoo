import YulSemnaticsZoo.Yul.Syntax

/-!
# Yul: lexer

Text to tokens, for the grammar in the "Specification of Yul" and "Specification of Yul Object"
sections of the solidity docs. The lexer also reads comments, `0x` numbers, `hex"…"` literals and
the escapes `\\ \" \' \n \r \t \xNN \uNNNN` in strings.
-/

namespace Yul

inductive Symbol where
  | LBrace
  | RBrace
  | LParen
  | RParen
  | Comma
  /-- `:=` -/
  | Assign
  /-- `->` -/
  | Arrow
  deriving DecidableEq, Repr

inductive Token where
  /-- an identifier or a keyword -/
  | Word (s : String)
  | Number (n : Nat)
  /-- a string literal or a hex literal: its bytes -/
  | Str (bytes : List UInt8)
  | Sym (s : Symbol)
  deriving DecidableEq, Repr

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'

def isIdentChar (c : Char) : Bool := isIdentStart c || c.isDigit || c == '.'

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- a word that the lexer reads as one word -/
def isWord (s : String) : Bool :=
  match s.toList with
  | c :: cs => isIdentStart c && cs.all isIdentChar
  | [] => false

/-- the longest start of `cs` whose characters satisfy `p`, and the characters after it -/
def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then ((span p cs).1.cons c, (span p cs).2) else ([], c :: cs)

/-- the value of a hex digit -/
def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- the value of digits in base `base` -/
def digitsValue (base : Nat) (ds : List Char) : Option Nat :=
  ds.foldlM (fun v d => (hexValue d).bind fun k => if k < base then some (base * v + k) else none) 0

/-- the UTF-8 bytes of the code point of four hex digits -/
def codePoint (ds : List Char) : Option (List UInt8) :=
  (digitsValue 16 ds).bind fun k =>
    if k.isValidChar then some (String.utf8EncodeChar (Char.ofNat k)) else none

/-- the bytes of a string literal after its opening `"`, and the characters after its closing
`"` -/
def lexString : List Char → Except String (List UInt8 × List Char)
  | [] => .error "a string literal has no end"
  | c :: cs =>
    if c = '"' then .ok ([], cs)
    else if c = '\n' ∨ c = '\r' then .error "a new line in a string literal"
    else if c = '\\' then
      match cs with
      | 'x' :: a :: b :: cs => match digitsValue 16 [a, b] with
        | some k => (lexString cs).map fun (bs, r) => (k.toUInt8 :: bs, r)
        | none => .error "\\x needs two hex digits"
      | 'u' :: a :: b :: d :: e :: cs => match codePoint [a, b, d, e] with
        | some u => (lexString cs).map fun (bs, r) => (u ++ bs, r)
        | none => .error "\\u needs four hex digits of a character"
      | e :: cs =>
        let byte := if e = '\\' then some 0x5c else if e = '"' then some 0x22
          else if e = '\'' then some 0x27 else if e = 'n' then some 0x0a
          else if e = 'r' then some 0x0d else if e = 't' then some 0x09 else none
        match byte with
        | some k => (lexString cs).map fun (bs, r) => (k :: bs, r)
        | none => .error s!"unknown escape \\{e}"
      | [] => .error "a string literal has no end"
    else (lexString cs).map fun (bs, r) => (String.utf8EncodeChar c ++ bs, r)

/-- the bytes of a hex literal after its opening quote `q`, and the characters after its
closing quote -/
def lexHex (q : Char) : List Char → Except String (List UInt8 × List Char)
  | c :: cs => if c = q then .ok ([], cs) else match cs with
    | d :: cs => match digitsValue 16 [c, d] with
      | some k => (lexHex q cs).map fun (bs, r) => (k.toUInt8 :: bs, r)
      | none => .error "a hex literal needs pairs of hex digits"
    | [] => .error "a hex literal has no end"
  | [] => .error "a hex literal has no end"

/-- `t` if the characters `r` after it do not continue it -/
def ended (t : Token) (r : List Char) : Except String (Token × List Char) :=
  match r with
  | c :: _ => if isIdentChar c then .error s!"unexpected character {c}" else .ok (t, r)
  | [] => .ok (t, r)

/-- the token at the start of `c :: cs`, and the characters after it -/
def lexToken (c : Char) (cs : List Char) : Except String (Token × List Char) :=
  if isIdentStart c then
    let (w, r) := span isIdentChar (c :: cs)
    match w, r with
    | ['h', 'e', 'x'], q :: r =>
      if q = '"' ∨ q = '\'' then (lexHex q r).map fun (bs, r) => (.Str bs, r)
      else .ok (.Word "hex", q :: r)
    | w, r => .ok (.Word (String.ofList w), r)
  else if c.isDigit then
    match c, cs with
    | '0', 'x' :: cs =>
      let (ds, r) := span (fun d => (hexValue d).isSome) cs
      match ds, digitsValue 16 ds with
      | _ :: _, some k => ended (.Number k) r
      | _, _ => .error "0x needs hex digits"
    | _, _ =>
      let (ds, r) := span Char.isDigit (c :: cs)
      match digitsValue 10 ds with
      | some k => ended (.Number k) r
      | none => .error "a number needs digits"
  else if c = '"' then (lexString cs).map fun (bs, r) => (.Str bs, r)
  else if c = '{' then .ok (.Sym .LBrace, cs)
  else if c = '}' then .ok (.Sym .RBrace, cs)
  else if c = '(' then .ok (.Sym .LParen, cs)
  else if c = ')' then .ok (.Sym .RParen, cs)
  else if c = ',' then .ok (.Sym .Comma, cs)
  else if c = ':' then match cs with
    | '=' :: cs => .ok (.Sym .Assign, cs)
    | _ => .error "expected := (there are no types)"
  else if c = '-' then match cs with
    | '>' :: cs => .ok (.Sym .Arrow, cs)
    | _ => .error "expected ->"
  else .error s!"unexpected character {c}"

/-- the characters after the end `*/` of a block comment -/
def dropBlockComment : List Char → Option (List Char)
  | '*' :: '/' :: cs => some cs
  | _ :: cs => dropBlockComment cs
  | [] => none

/-- the tokens of `cs`; each step takes at least one character, so `fuel = cs.length` is
enough -/
def lexWith : Nat → List Char → Except String (List Token)
  | _, [] => .ok []
  | 0, _ :: _ => .error "out of fuel"
  | fuel + 1, c :: cs =>
    if isSpace c then lexWith fuel cs
    else if c = '/' then match cs with
      | '/' :: cs => lexWith fuel (cs.dropWhile (· ≠ '\n'))
      | '*' :: cs => match dropBlockComment cs with
        | some cs => lexWith fuel cs
        | none => .error "a comment has no end"
      | _ => .error "unexpected character /"
    else do
      let (t, cs) ← lexToken c cs
      return t :: (← lexWith fuel cs)

def lex (cs : List Char) : Except String (List Token) := lexWith cs.length cs

end Yul
