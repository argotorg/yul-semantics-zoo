import YulSemnaticsZoo.Yul.Lexer

/-!
# Yul: printer

The text of a Yul AST. The printer makes a list of tokens and new lines (`Piece`s); `render`
puts a space between two tokens where the lexer could read them as one token (two words, or a
word and a number), and also where it makes the text easier to read.
-/

namespace Yul

/-- the digits of `n` in base 10 -/
def decimal (n : Nat) : List Char :=
  if n < 10 then [Char.ofNat (48 + n)] else decimal (n / 10) ++ [Char.ofNat (48 + n % 10)]

/-- the lower case hex digit of `k < 16` -/
def hexDigit (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)

/-- a byte in a string literal: printable ASCII as is, other bytes as `\xNN` -/
def escape (b : UInt8) : List Char :=
  if b = 0x22 then ['\\', '"']
  else if b = 0x5c then ['\\', '\\']
  else if 0x20 ≤ b ∧ b < 0x7f then [Char.ofNat b.toNat]
  else ['\\', 'x', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def Token.chars : Token → List Char
  | .Word s => s.toList
  | .Number n => decimal n
  | .Str bs => '"' :: bs.flatMap escape ++ ['"']
  | .Sym .LBrace => ['{']
  | .Sym .RBrace => ['}']
  | .Sym .LParen => ['(']
  | .Sym .RParen => [')']
  | .Sym .Comma => [',']
  | .Sym .Assign => [':', '=']
  | .Sym .Arrow => ['-', '>']

inductive Piece where
  | tok (t : Token)
  /-- a new line, then `k` spaces -/
  | line (k : Nat)

/-- a space between the tokens `t` and `u`: not after `(`, and not before `(`, `)` or `,` -/
def gap : Token → Token → Bool
  | .Sym .LParen, _ => false
  | _, .Sym .LParen => false
  | _, .Sym .RParen => false
  | _, .Sym .Comma => false
  | _, _ => true

/-- the characters between the token `t` and the pieces `ps` after it -/
def sepBefore (t : Token) : List Piece → List Char
  | .tok u :: _ => if gap t u then [' '] else []
  | _ => []

def render : List Piece → List Char
  | [] => []
  | .line k :: ps => '\n' :: List.replicate k ' ' ++ render ps
  | .tok t :: ps => t.chars ++ sepBefore t ps ++ render ps

/-- the tokens of pieces, without the new lines -/
def tokens (ps : List Piece) : List Token :=
  ps.filterMap fun p => match p with
    | .tok t => some t
    | .line _ => none

def word (s : String) : Piece := .tok (.Word s)
def sym (s : Symbol) : Piece := .tok (.Sym s)

/-- the bytes of an ASCII string -/
def ascii (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

def Literal.token : Literal → Token
  | .NumberLiteral n => .Number n
  | .StringLiteral bs => .Str bs
  | .TrueLiteral => .Word "true"
  | .FalseLiteral => .Word "false"

/-- identifiers separated by commas -/
def identsPieces : List Identifier → List Piece
  | [] => []
  | x :: xs => word x :: xs.flatMap fun x => [sym .Comma, word x]

mutual

def Expression.pieces : Expression → List Piece
  | .FunctionCall f args => word f :: sym .LParen :: argsPieces args ++ [sym .RParen]
  | .Identifier x => [word x]
  | .Literal l => [.tok l.token]

/-- expressions separated by commas -/
def argsPieces : List Expression → List Piece
  | [] => []
  | e :: es => e.pieces ++ moreArgsPieces es

/-- expressions, each after a comma -/
def moreArgsPieces : List Expression → List Piece
  | [] => []
  | e :: es => sym .Comma :: e.pieces ++ moreArgsPieces es

end

mutual

/-- a block whose `}` is at indent `k` -/
def Block.pieces (k : Nat) : Block → List Piece
  | ⟨[]⟩ => [sym .LBrace, sym .RBrace]
  | ⟨s :: ss⟩ => sym .LBrace :: stmtsPieces (k + 2) (s :: ss) ++ [.line k, sym .RBrace]

/-- statements, each on a new line at indent `k` -/
def stmtsPieces (k : Nat) : List Statement → List Piece
  | [] => []
  | s :: ss => .line k :: s.pieces k ++ stmtsPieces k ss

/-- a statement at indent `k` -/
def Statement.pieces (k : Nat) : Statement → List Piece
  | .Block b => b.pieces k
  | .FunctionDefinition f ps rs b =>
    word "function" :: word f :: sym .LParen :: identsPieces ps ++ sym .RParen ::
      (if rs.isEmpty then [] else sym .Arrow :: identsPieces rs) ++ b.pieces k
  | .VariableDeclaration vs v =>
    word "let" :: identsPieces vs ++ (match v with | some e => sym .Assign :: e.pieces | none => [])
  | .Assignment vs e => identsPieces vs ++ sym .Assign :: e.pieces
  | .If c b => word "if" :: c.pieces ++ b.pieces k
  | .Expression e => e.pieces
  | .ForLoop i c p b => word "for" :: i.pieces k ++ c.pieces ++ p.pieces k ++ b.pieces k
  | .Break => [word "break"]
  | .Continue => [word "continue"]
  | .Leave => [word "leave"]

end

def Data.pieces (k : Nat) (d : Data) : List Piece :=
  [.line k, word "data", .tok (.Str (ascii d.name)), .tok (.Str d.value)]

mutual

/-- an object whose `}` is at indent `k` -/
def Object.pieces (k : Nat) : Object → List Piece
  | ⟨name, code, objects, data⟩ =>
    word "object" :: .tok (.Str (ascii name)) :: sym .LBrace :: .line (k + 2) :: word "code" ::
      code.pieces (k + 2) ++ objectsPieces (k + 2) objects ++ data.flatMap (Data.pieces (k + 2)) ++
      [.line k, sym .RBrace]

/-- objects, each on a new line at indent `k` -/
def objectsPieces (k : Nat) : List Object → List Piece
  | [] => []
  | o :: os => .line k :: o.pieces k ++ objectsPieces k os

end

def Expression.print (e : Expression) : String := String.ofList (render e.pieces)
def Statement.print (s : Statement) : String := String.ofList (render (s.pieces 0))
def Block.print (b : Block) : String := String.ofList (render (b.pieces 0))
def Object.print (o : Object) : String := String.ofList (render (o.pieces 0))

end Yul
