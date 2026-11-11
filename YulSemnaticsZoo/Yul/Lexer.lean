import YulSemnaticsZoo.Yul.Syntax

set_option doc.verso true

/-!
# Yul: lexer

Text to tokens, for the grammar in the "Specification of Yul" and "Specification of Yul Object"
sections of the solidity docs. The lexer also reads comments, `0x` numbers, `hex"…"` literals and
the escapes `\\ \" \' \n \r \t \xNN \uNNNN` in strings.

Where the grammar and solc 0.8.33 differ, it reads as solc: a backslash before a new line in a
string is no character, a hex literal can have one {lit}`_` between two pairs of digits, and a
decimal number does not start with {lit}`0`.
-/

namespace Yul

inductive Symbol where
  | LBrace
  | RBrace
  | LParen
  | RParen
  | Comma
  /-- {lit}`Assign`: {lit}`:=` -/
  | Assign
  /-- {lit}`Arrow`: {lit}`->` -/
  | Arrow
  deriving DecidableEq, Repr

inductive Token where
  /-- {lit}`Word`: an identifier or a keyword -/
  | Word (s : String)
  | Number (n : Nat)
  /-- {lit}`Str`: a string literal or a hex literal: its bytes -/
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

/-- the longest start of {lit}`cs` whose characters satisfy {name}`p`, and the characters after it
  -/
def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then ((span p cs).1.cons c, (span p cs).2) else ([], c :: cs)

/-- the value of a hex digit -/
def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- the value of digits in base {name}`base` -/
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
      -- a backslash before a new line is no character (as in solc)
      | '\r' :: '\n' :: cs => lexString cs
      | '\n' :: cs | '\r' :: cs => lexString cs
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

/-- the bytes of a hex literal after its opening quote {name}`q`, and the characters after its
closing quote; {name}`sep`: one {lit}`_` can come next, since a pair of digits is before it (as in
solc) -/
def lexHex (q : Char) (sep : Bool) : List Char → Except String (List UInt8 × List Char)
  | c :: cs =>
    if c = q then .ok ([], cs)
    else if c = '_' ∧ sep then match cs with
      | d :: _ =>
        if d = q ∨ d = '_' then .error "a _ in a hex literal must be between two pairs of digits"
        else lexHex q false cs
      | [] => .error "a hex literal has no end"
    else match cs with
      | d :: cs => match digitsValue 16 [c, d] with
        | some k => (lexHex q true cs).map fun (bs, r) => (k.toUInt8 :: bs, r)
        | none => .error "a hex literal needs pairs of hex digits"
      | [] => .error "a hex literal has no end"
  | [] => .error "a hex literal has no end"

/-- {name}`t` if the characters {name}`r` after it do not continue it -/
def ended (t : Token) (r : List Char) : Except String (Token × List Char) :=
  match r with
  | c :: _ => if isIdentChar c then .error s!"unexpected character {c}" else .ok (t, r)
  | [] => .ok (t, r)

/-- the token at the start of {lit}`c :: cs`, and the characters after it -/
def lexToken (c : Char) (cs : List Char) : Except String (Token × List Char) :=
  if isIdentStart c then
    let (w, r) := span isIdentChar (c :: cs)
    match w, r with
    | ['h', 'e', 'x'], q :: r =>
      if q = '"' ∨ q = '\'' then (lexHex q false r).map fun (bs, r) => (.Str bs, r)
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
      match ds, digitsValue 10 ds with
      | '0' :: _ :: _, _ =>
        .error "a decimal number cannot start with 0 (octal numbers are not allowed)"
      | _, some k => ended (.Number k) r
      | _, none => .error "a number needs digits"
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

/-- the tokens of {lit}`cs`; each step takes at least one character, so {lit}`fuel = cs.length` is
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
