import YulSemnaticsZoo.Yul.Lemmas.Lexer
import YulSemnaticsZoo.Yul.Valid

/-!
# Yul: the printed words of a valid AST are words

Each word in the printed tokens of a valid AST is a word that the lexer reads as one word.
-/

namespace Yul


theorem validIdent_word {s : String} (h : validIdent s = true) : isWord s = true := by
  simp only [validIdent, Bool.and_eq_true] at h; exact h.1

@[simp] theorem lexable_word (s : String) : (Token.Word s).lexable = isWord s := rfl
@[simp] theorem lexable_number (n : Nat) : (Token.Number n).lexable = true := rfl
@[simp] theorem lexable_str (bs : List UInt8) : (Token.Str bs).lexable = true := rfl
@[simp] theorem lexable_sym (s : Symbol) : (Token.Sym s).lexable = true := rfl

/-- the keywords that the printer prints are words -/
@[simp] theorem isWord_printed :
    isWord "function" = true ∧ isWord "let" = true ∧ isWord "if" = true ∧ isWord "for" = true ∧
    isWord "break" = true ∧ isWord "continue" = true ∧ isWord "leave" = true ∧
    isWord "true" = true ∧ isWord "false" = true ∧ isWord "object" = true ∧
    isWord "code" = true ∧ isWord "data" = true := by decide

macro "lexable_simp" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [word_eq, sym_eq, tokens_tok, tokens_line, tokens_append, tokens_nil,
    List.all_cons, List.all_append, List.all_nil, lexable_word, lexable_sym, lexable_number,
    lexable_str, isWord_printed, Bool.and_true, Bool.true_and, $ls,*])

theorem idents_lexable (xs : List Identifier) (h : xs.all validIdent = true) :
    (tokens (identsPieces xs)).all Token.lexable = true := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    lexable_simp [identsPieces, validIdent_word h.1]
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      lexable_simp [List.flatMap_cons, validIdent_word h.2.1, ih ⟨h.1, h.2.2⟩]

mutual

theorem expr_lexable : ∀ (e : Expression), e.valid = true →
    (tokens e.pieces).all Token.lexable = true
  | .FunctionCall f args, hv => by
    simp only [Expression.valid, Bool.and_eq_true] at hv
    lexable_simp [Expression.pieces, validIdent_word hv.1, args_lexable args hv.2]
  | .Identifier x, hv => by
    simp only [Expression.valid] at hv
    lexable_simp [Expression.pieces, validIdent_word hv]
  | .Literal l, _ => by cases l <;> rfl

theorem args_lexable : ∀ (es : List Expression), argsValid es = true →
    (tokens (argsPieces es)).all Token.lexable = true
  | [], _ => rfl
  | e :: es, hv => by
    simp only [argsValid, Bool.and_eq_true] at hv
    lexable_simp [argsPieces, expr_lexable e hv.1, moreArgs_lexable es hv.2]

theorem moreArgs_lexable : ∀ (es : List Expression), argsValid es = true →
    (tokens (moreArgsPieces es)).all Token.lexable = true
  | [], _ => rfl
  | e :: es, hv => by
    simp only [argsValid, Bool.and_eq_true] at hv
    lexable_simp [moreArgsPieces, expr_lexable e hv.1, moreArgs_lexable es hv.2]

end

theorem rets_lexable (rs : List Identifier) (h : rs.all validIdent = true) :
    (tokens (if rs.isEmpty then [] else sym .Arrow :: identsPieces rs)).all Token.lexable =
      true := by
  split
  · rfl
  · lexable_simp [idents_lexable rs h]

mutual

theorem block_lexable : ∀ (b : Block), b.valid = true → ∀ k,
    (tokens (b.pieces k)).all Token.lexable = true
  | ⟨[]⟩, _, _ => rfl
  | ⟨s :: ss⟩, hv, k => by
    simp only [Block.valid] at hv
    lexable_simp [Block.pieces, stmts_lexable (s :: ss) hv (k + 2)]

theorem stmts_lexable : ∀ (ss : List Statement), stmtsValid ss = true → ∀ k,
    (tokens (stmtsPieces k ss)).all Token.lexable = true
  | [], _, _ => rfl
  | s :: ss, hv, k => by
    simp only [stmtsValid, Bool.and_eq_true] at hv
    lexable_simp [stmtsPieces, stmt_lexable s hv.1 k, stmts_lexable ss hv.2 k]

theorem stmt_lexable : ∀ (s : Statement), s.valid = true → ∀ k,
    (tokens (s.pieces k)).all Token.lexable = true
  | .Block b, hv, k => by
    simp only [Statement.valid] at hv
    lexable_simp [Statement.pieces, block_lexable b hv k]
  | .FunctionDefinition f ps rs b, hv, k => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hf, hps⟩, hrs⟩, hb⟩ := hv
    have hr := rets_lexable rs hrs
    simp only [sym_eq] at hr
    lexable_simp [Statement.pieces, validIdent_word hf, idents_lexable ps hps, hr,
      block_lexable b hb k]
  | .VariableDeclaration vs v, hv, k => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    obtain ⟨⟨_, hvs⟩, he⟩ := hv
    cases v with
    | some e =>
      simp only at he
      lexable_simp [Statement.pieces, idents_lexable vs hvs, expr_lexable e he]
    | none => lexable_simp [Statement.pieces, idents_lexable vs hvs]
  | .Assignment vs e, hv, k => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    lexable_simp [Statement.pieces, idents_lexable vs hv.1.2, expr_lexable e hv.2]
  | .If c b, hv, k => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    lexable_simp [Statement.pieces, expr_lexable c hv.1, block_lexable b hv.2 k]
  | .Expression e, hv, k => by
    simp only [Statement.valid] at hv
    lexable_simp [Statement.pieces, expr_lexable e hv]
  | .ForLoop i c p b, hv, k => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hi, hc⟩, hp⟩, hb⟩ := hv
    lexable_simp [Statement.pieces, block_lexable i hi k, expr_lexable c hc,
      block_lexable p hp k, block_lexable b hb k]
  | .Break, _, _ => rfl
  | .Continue, _, _ => rfl
  | .Leave, _, _ => rfl

end

theorem data_lexable (ds : List Data) (k : Nat) :
    (tokens (ds.flatMap (Data.pieces k))).all Token.lexable = true := by
  induction ds with
  | nil => rfl
  | cons d ds ih => lexable_simp [List.flatMap_cons, Data.pieces, ih]

mutual

theorem object_lexable : ∀ (o : Object), o.valid = true → ∀ k,
    (tokens (o.pieces k)).all Token.lexable = true
  | ⟨name, code, objects, data⟩, hv, k => by
    simp only [Object.valid, Bool.and_eq_true] at hv
    lexable_simp [Object.pieces, block_lexable code hv.1.1.2 (k + 2),
      objects_lexable objects hv.1.2 (k + 2), data_lexable data (k + 2)]

theorem objects_lexable : ∀ (os : List Object), objectsValid os = true → ∀ k,
    (tokens (objectsPieces k os)).all Token.lexable = true
  | [], _, _ => rfl
  | o :: os, hv, k => by
    simp only [objectsValid, Bool.and_eq_true] at hv
    lexable_simp [objectsPieces, object_lexable o hv.1 k, objects_lexable os hv.2 k]

end

end Yul
