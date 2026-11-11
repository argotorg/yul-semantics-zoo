import YulSemnaticsZoo.Yul.Parser

/-!
# Yul: valid ASTs

The ASTs that the grammar can express: each identifier is an identifier of the grammar and not a
keyword, a `let` or an assignment has variables, and each object and data name is ASCII. For
these, parsing the printed text gives the AST (`Yul.Object.parse_print`).
-/

namespace Yul


mutual

def Expression.valid : Expression → Bool
  | .FunctionCall f args => validIdent f && argsValid args
  | .Identifier x => validIdent x
  | .Literal _ => true

def argsValid : List Expression → Bool
  | [] => true
  | e :: es => e.valid && argsValid es

end

mutual

def Block.valid : Block → Bool
  | ⟨ss⟩ => stmtsValid ss

def stmtsValid : List Statement → Bool
  | [] => true
  | s :: ss => s.valid && stmtsValid ss

def Statement.valid : Statement → Bool
  | .Block b => b.valid
  | .FunctionDefinition f ps rs b =>
    validIdent f && ps.all validIdent && rs.all validIdent && b.valid
  | .VariableDeclaration vs v =>
    !vs.isEmpty && vs.all validIdent && (match v with | some e => e.valid | none => true)
  | .Assignment vs e => !vs.isEmpty && vs.all validIdent && e.valid
  | .If c b => c.valid && b.valid
  | .Expression e => e.valid
  | .ForLoop i c p b => i.valid && c.valid && p.valid && b.valid
  | .Break | .Continue | .Leave => true

end

def isAscii (s : String) : Bool := s.toList.all (·.toNat < 128)

mutual

def Object.valid : Object → Bool
  | ⟨name, code, objects, data⟩ =>
    isAscii name && code.valid && objectsValid objects && data.all (isAscii ·.name)

def objectsValid : List Object → Bool
  | [] => true
  | o :: os => o.valid && objectsValid os

end

end Yul
