import YulSemnaticsZoo.Yul.Lemmas.Parser
import YulSemnaticsZoo.Yul.Lemmas.Lexable

set_option doc.verso true

/-!
# Yul: theorems

Parsing printed text gives the AST, for each valid AST (see {lit}`YulSemnaticsZoo/Yul/Valid.lean`).

The proofs have two steps: lexing the printed text gives the printed tokens ({lit}`lex_print`), and
parsing the tokens gives the AST ({lit}`parseObject_pieces` and the lemmas before it).
-/

namespace Yul

/-- parsing a printed expression gives the expression -/
theorem Expression.parse_print (e : Expression) (h : e.valid = true) :
    Expression.parse e.print = .ok e := by
  have hp := parseExpr_pieces e h [] (by simp) (3 * (tokens e.pieces).length + 1) (by omega)
  rw [List.append_nil] at hp
  simp only [Expression.parse, Expression.print, parseAll, lex_print (expr_lexable e h)]
  bind_simp
  rw [hp]

/-- parsing a printed statement gives the statement -/
theorem Statement.parse_print (s : Statement) (h : s.valid = true) :
    Statement.parse s.print = .ok s := by
  have hp := parseStatement_pieces s h 0 [] (by simp [stmtFollow])
    (3 * (tokens (s.pieces 0)).length + 1) (Nat.le_refl _)
  rw [List.append_nil] at hp
  simp only [Statement.parse, Statement.print, parseAll, lex_print (stmt_lexable s h 0)]
  bind_simp
  rw [hp]

/-- parsing a printed block gives the block -/
theorem Block.parse_print (b : Block) (h : b.valid = true) : Block.parse b.print = .ok b := by
  have hp := parseBlock_pieces b h 0 [] (3 * (tokens (b.pieces 0)).length + 1) (by omega)
  rw [List.append_nil] at hp
  simp only [Block.parse, Block.print, parseAll, lex_print (block_lexable b h 0)]
  bind_simp
  rw [hp]

/-- parsing a printed object gives the object -/
theorem Object.parse_print (o : Object) (h : o.valid = true) : Object.parse o.print = .ok o := by
  have hp := parseObject_pieces o h 0 [] (3 * (tokens (o.pieces 0)).length + 1) (by omega)
  rw [List.append_nil] at hp
  simp only [Object.parse, Object.print, parseAll, lex_print (object_lexable o h 0)]
  bind_simp
  rw [hp]

end Yul
