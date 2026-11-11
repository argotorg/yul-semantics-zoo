import YulSemnaticsZoo.Yul.Lemmas.Lexer
import YulSemnaticsZoo.Yul.Valid

/-!
# Yul: parsing printed tokens gives the AST

For each part of a valid AST, parsing its printed tokens, then tokens `r` that do not continue
it, gives the part and `r`, if the fuel is at least 3 for each token.
-/

namespace Yul

theorem validName_ident {s : String} (h : validName s = true) : validIdent s = true := by
  simp only [validName, Bool.and_eq_true] at h; exact h.1

theorem validIdent_ne {s : String} (h : validIdent s = true) :
    s ≠ "function" ∧ s ≠ "let" ∧ s ≠ "if" ∧ s ≠ "for" ∧ s ≠ "break" ∧ s ≠ "continue" ∧
      s ≠ "leave" ∧ s ≠ "true" ∧ s ≠ "false" := by
  simp only [validIdent, Bool.and_eq_true, Bool.not_eq_true'] at h
  have h := h.2
  simp only [keywords, List.contains_eq_any_beq, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem identsPieces_cons_cons (x y : Identifier) (ys : List Identifier) :
    identsPieces (x :: y :: ys) = word x :: sym .Comma :: identsPieces (y :: ys) := by
  simp [identsPieces]

theorem parseIdents_pieces (ok : String → Bool) (xs : List Identifier) (hne : xs ≠ [])
    (hv : xs.all ok = true)
    (r : List Token) (hr : ∀ t ∈ r.head?, t ≠ .Sym .Comma) :
    parseIdents ok (tokens (identsPieces xs) ++ r) = .ok (xs, r) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hv
    cases xs with
    | nil =>
      simp only [identsPieces, List.flatMap_nil, tokens_tok, tokens_nil, List.cons_append,
        List.nil_append, word_eq]
      rw [parseIdents.eq_def]
      simp only [hv.1, ite_true]
      split
      · simp at hr
      · rfl
    | cons y ys =>
      rw [identsPieces_cons_cons]
      simp only [tokens_tok, word_eq, sym_eq, List.cons_append]
      rw [parseIdents.eq_def]
      simp [hv.1, ih (by simp) hv.2, Except.map]

theorem parseParamList_pieces (xs : List Identifier) (hne : xs ≠ [])
    (hv : xs.all validName = true) (r : List Token) :
    parseParamList (tokens (identsPieces xs) ++ .Sym .RParen :: r) = .ok (xs, r) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hv
    cases xs with
    | nil =>
      simp only [identsPieces, List.flatMap_nil, tokens_tok, tokens_nil, List.cons_append,
        List.nil_append, word_eq]
      rw [parseParamList.eq_def]
      simp [hv.1]
    | cons y ys =>
      rw [identsPieces_cons_cons]
      simp only [tokens_tok, word_eq, sym_eq, List.cons_append]
      have hy : tokens (identsPieces (y :: ys)) =
          .Word y :: tokens (ys.flatMap fun x => [sym .Comma, word x]) := rfl
      rw [parseParamList.eq_def]
      simp only [hv.1, ite_true]
      rw [hy] at ih ⊢
      have h := ih (by simp) hv.2
      simp only [sym_eq, word_eq, List.cons_append] at h
      simp [h, Except.map]

theorem parseParams_pieces (ps : List Identifier) (hv : ps.all validName = true)
    (r : List Token) :
    parseParams (tokens (identsPieces ps) ++ .Sym .RParen :: r) = .ok (ps, r) := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    have hhead : tokens (identsPieces (p :: ps)) =
        .Word p :: tokens (ps.flatMap fun x => [sym .Comma, word x]) := rfl
    have h := parseParamList_pieces (p :: ps) (by simp) hv r
    rw [hhead] at h ⊢
    rw [parseParams.eq_def]
    simpa using h

theorem parseRets_pieces (rs : List Identifier) (hv : rs.all validName = true) (r : List Token) :
    parseRets (tokens (if rs.isEmpty then [] else sym .Arrow :: identsPieces rs) ++
      .Sym .LBrace :: r) = .ok (rs, .Sym .LBrace :: r) := by
  cases rs with
  | nil => rfl
  | cons x xs =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, sym_eq, tokens_tok,
      List.cons_append]
    rw [parseRets.eq_def]
    exact parseIdents_pieces validName (x :: xs) (by simp) hv _ (by simp)

/-- the first printed token of an expression is not a symbol -/
theorem expr_head (e : Expression) : ∃ t ts, tokens e.pieces = t :: ts ∧ ∀ s, t ≠ .Sym s := by
  cases e with
  | FunctionCall f args => exact ⟨_, _, rfl, by simp⟩
  | Identifier x => exact ⟨_, _, rfl, by simp⟩
  | Literal l => cases l <;> exact ⟨_, _, rfl, by simp [Literal.token]⟩

mutual

theorem parseExpr_pieces : ∀ (e : Expression), e.valid = true → ∀ (r : List Token),
    (∀ t ∈ r.head?, t ≠ .Sym .LParen) → ∀ n, 3 * (tokens e.pieces).length ≤ n →
    parseExpr n (tokens e.pieces ++ r) = .ok (e, r)
  | .FunctionCall f args, hv, r, _, n, hn => by
    simp only [Expression.valid, Bool.and_eq_true] at hv
    have hne := validIdent_ne hv.1
    simp only [Expression.pieces, word_eq, sym_eq, tokens_tok, tokens_append, tokens_nil,
      List.cons_append, List.append_assoc, List.nil_append, List.length_cons,
      List.length_append, List.length_nil] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseExpr.eq_def]
    simp only [hne, ite_false, hv.1, ite_true]
    rw [parseArgs_pieces args hv.2 r m (by omega)]
    rfl
  | .Identifier x, hv, r, hr, n, hn => by
    simp only [Expression.valid] at hv
    have hne := validIdent_ne hv
    simp only [Expression.pieces, word_eq, tokens_tok, tokens_nil, List.cons_append,
      List.nil_append, List.length_cons, List.length_nil] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseExpr.eq_def]
    simp only [hne, ite_false, hv, ite_true]
    split
    · simp at hr
    · rfl
  | .Literal l, _, r, _, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
      cases l <;> simp [Expression.pieces, Literal.token] at hn <;> omega⟩
    cases l <;> simp [Expression.pieces, Literal.token, parseExpr.eq_def]

theorem parseArgs_pieces : ∀ (es : List Expression), argsValid es = true → ∀ (r : List Token) n,
    3 * ((tokens (argsPieces es)).length + 1) ≤ n →
    parseArgs n (tokens (argsPieces es) ++ .Sym .RParen :: r) = .ok (es, r)
  | [], _, r, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  | e :: es, hv, r, n, hn => by
    simp only [argsValid, Bool.and_eq_true] at hv
    simp only [argsPieces, tokens_append, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨t, ts, he, ht⟩ := expr_head e
    have hle : 1 ≤ (tokens e.pieces).length := by rw [he]; simp
    have hm : ∀ t ∈ (tokens (moreArgsPieces es) ++ .Sym .RParen :: r).head?,
        t ≠ .Sym .LParen := by
      cases es <;> simp [moreArgsPieces]
    rw [parseArgs.eq_def, List.append_assoc]
    simp only
    split
    · next r' heq => rw [he] at heq; simp at heq; exact absurd heq.1 (ht _)
    · rw [parseExpr_pieces e hv.1 _ hm m (by omega)]
      simp [parseMoreArgs_pieces es hv.2 r m (by omega), bind, Except.bind, pure, Except.pure]

theorem parseMoreArgs_pieces : ∀ (es : List Expression), argsValid es = true →
    ∀ (r : List Token) n, 3 * ((tokens (moreArgsPieces es)).length + 1) ≤ n →
    parseMoreArgs n (tokens (moreArgsPieces es) ++ .Sym .RParen :: r) = .ok (es, r)
  | [], _, r, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  | e :: es, hv, r, n, hn => by
    simp only [argsValid, Bool.and_eq_true] at hv
    simp only [moreArgsPieces, sym_eq, tokens_tok, tokens_append, List.length_cons,
      List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : ∀ t ∈ (tokens (moreArgsPieces es) ++ .Sym .RParen :: r).head?,
        t ≠ .Sym .LParen := by
      cases es <;> simp [moreArgsPieces]
    rw [parseMoreArgs.eq_def]
    simp only [List.cons_append, List.append_assoc]
    rw [parseExpr_pieces e hv.1 _ hm m (by omega)]
    simp [parseMoreArgs_pieces es hv.2 r m (by omega), bind, Except.bind, pure, Except.pure]

end

/-- the tokens after a statement do not continue it -/
def stmtFollow (r : List Token) : Prop :=
  ∀ t ∈ r.head?, t ≠ .Sym .LParen ∧ t ≠ .Sym .Comma ∧ t ≠ .Sym .Assign

theorem block_head (b : Block) (k : Nat) : ∃ ts, tokens (b.pieces k) = .Sym .LBrace :: ts := by
  rcases b with ⟨_ | ⟨s, ss⟩⟩ <;> exact ⟨_, rfl⟩

/-- the first printed token of a valid statement is `{` or not a symbol -/
theorem stmt_head (s : Statement) (hv : s.valid = true) (k : Nat) :
    ∃ t ts, tokens (s.pieces k) = t :: ts ∧ (t = .Sym .LBrace ∨ ∀ x, t ≠ .Sym x) := by
  cases s with
  | Block b => obtain ⟨ts, h⟩ := block_head b k; exact ⟨_, _, h, .inl rfl⟩
  | Assignment vs e =>
    cases vs with
    | nil => simp [Statement.valid] at hv
    | cons x xs => exact ⟨_, _, rfl, .inr (by simp)⟩
  | Expression e =>
    obtain ⟨t, ts, h, ht⟩ := expr_head e
    exact ⟨t, ts, h, .inr ht⟩
  | _ => exact ⟨_, _, rfl, .inr (by simp)⟩

theorem stmts_follow (ss : List Statement) (hv : stmtsValid ss = true) (k : Nat)
    (r : List Token) : stmtFollow (tokens (stmtsPieces k ss) ++ .Sym .RBrace :: r) := by
  cases ss with
  | nil => simp [stmtFollow, stmtsPieces]
  | cons s ss =>
    simp only [stmtsValid, Bool.and_eq_true] at hv
    obtain ⟨t, ts, h, ht⟩ := stmt_head s hv.1 k
    simp only [stmtFollow, stmtsPieces, tokens_line, tokens_append, h, List.cons_append,
      List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
    rcases ht with ht | ht
    · subst ht; simp
    · exact ⟨ht _, ht _, ht _⟩

theorem expr_follow_of_stmt {r : List Token} (h : stmtFollow r) :
    ∀ t ∈ r.head?, t ≠ .Sym .LParen := fun t ht => (h t ht).1

theorem block_follow (b : Block) (k : Nat) (r : List Token) :
    ∀ t ∈ (tokens (b.pieces k) ++ r).head?, t ≠ .Sym .LParen := by
  obtain ⟨ts, h⟩ := block_head b k
  simp [h]

macro "bind_simp" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure, Except.map])

mutual

theorem parseBlock_pieces : ∀ (b : Block), b.valid = true → ∀ (k : Nat) (r : List Token) n,
    3 * (tokens (b.pieces k)).length ≤ n → parseBlock n (tokens (b.pieces k) ++ r) = .ok (b, r)
  | ⟨[]⟩, _, k, r, n, hn => by
    simp only [Block.pieces, sym_eq, tokens_tok, tokens_nil, List.length_cons,
      List.length_nil] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rfl
  | ⟨s :: ss⟩, hv, k, r, n, hn => by
    simp only [Block.valid] at hv
    simp only [Block.pieces, sym_eq, tokens_tok, tokens_append, tokens_line, tokens_nil,
      List.cons_append, List.append_assoc, List.length_cons, List.length_append,
      List.length_nil] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseBlock.eq_def]
    simp only [List.nil_append]
    rw [parseStatements_pieces (s :: ss) hv (k + 2) r m (by omega)]
    rfl

theorem parseStatements_pieces : ∀ (ss : List Statement), stmtsValid ss = true →
    ∀ (k : Nat) (r : List Token) n, 3 * ((tokens (stmtsPieces k ss)).length + 1) ≤ n →
    parseStatements n (tokens (stmtsPieces k ss) ++ .Sym .RBrace :: r) = .ok (ss, r)
  | [], _, k, r, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  | s :: ss, hv, k, r, n, hn => by
    have hfollow := stmts_follow ss (by simp only [stmtsValid, Bool.and_eq_true] at hv; exact hv.2)
      k r
    simp only [stmtsValid, Bool.and_eq_true] at hv
    obtain ⟨t, ts, h, ht⟩ := stmt_head s hv.1 k
    have hle : 1 ≤ (tokens (s.pieces k)).length := by rw [h]; simp
    simp only [stmtsPieces, tokens_line, tokens_append, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseStatements.eq_def, List.append_assoc]
    simp only
    split
    · next r' heq =>
      rw [h] at heq; simp at heq
      rcases ht with ht | ht
      · rw [heq.1] at ht; cases ht
      · exact absurd heq.1 (ht _)
    · rw [parseStatement_pieces s hv.1 k _ hfollow m (by omega)]
      bind_simp
      rw [parseStatements_pieces ss hv.2 k r m (by omega)]

theorem parseStatement_pieces : ∀ (s : Statement), s.valid = true → ∀ (k : Nat) (r : List Token),
    stmtFollow r → ∀ n, 3 * (tokens (s.pieces k)).length + 1 ≤ n →
    parseStatement n (tokens (s.pieces k) ++ r) = .ok (s, r)
  | .Block b, hv, k, r, _, n, hn => by
    simp only [Statement.valid] at hv
    simp only [Statement.pieces] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hb := parseBlock_pieces b hv k r m (by omega)
    obtain ⟨ts, h⟩ := block_head b k
    rw [h] at hb ⊢
    rw [parseStatement.eq_def]
    simp only [List.cons_append]
    rw [List.cons_append] at hb
    rw [hb]
    rfl
  | .FunctionDefinition f ps rs b, hv, k, r, _, n, hn => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hf, hps⟩, hrs⟩, hb⟩ := hv
    have hblock := parseBlock_pieces b hb k r
    obtain ⟨ts, hbh⟩ := block_head b k
    simp only [Statement.pieces, word_eq, sym_eq, tokens_tok, tokens_append, List.cons_append,
      List.append_assoc, List.length_cons, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hrets := parseRets_pieces rs hrs (ts ++ r)
    rw [hbh] at hblock ⊢
    rw [parseStatement.eq_def]
    simp only [List.cons_append, ite_true]
    bind_simp
    simp only [parseName, hf, ite_true, expect, parseParams_pieces ps hps]
    simp only [sym_eq] at hrets
    rw [hrets]
    simp only
    simp only [List.cons_append] at hblock
    rw [hblock m (by rw [hbh] at hn; simp at hn ⊢; omega)]
  | .VariableDeclaration vs v, hv, k, r, hr, n, hn => by
    simp only [Statement.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      at hv
    obtain ⟨⟨hne, hvs⟩, he⟩ := hv
    cases v with
    | some e =>
      simp only at he
      simp only [Statement.pieces, word_eq, sym_eq, tokens_tok, tokens_append, List.cons_append,
        List.append_assoc, List.length_cons, List.length_append] at hn ⊢
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [parseStatement.eq_def]
      simp only [ite_true, show ("let" = "function") = False by decide, ite_false]
      rw [parseIdents_pieces validName vs hne hvs _ (by simp)]
      bind_simp
      rw [parseExpr_pieces e he r (expr_follow_of_stmt hr) m (by omega)]
    | none =>
      simp only [Statement.pieces, word_eq, tokens_tok,
        List.append_nil, List.cons_append, List.length_cons] at hn ⊢
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [parseStatement.eq_def]
      simp only [ite_true, show ("let" = "function") = False by decide, ite_false]
      rw [parseIdents_pieces validName vs hne hvs r (fun t ht => (hr t ht).2.1)]
      bind_simp
      split
      · simp [stmtFollow] at hr
      · rfl
  | .Assignment vs e, hv, k, r, hr, n, hn => by
    simp only [Statement.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      at hv
    obtain ⟨⟨hne, hvs⟩, he⟩ := hv
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hx := validIdent_ne (by simpa using (List.all_eq_true.mp hvs) x (by simp))
    have hids :=
      parseIdents_pieces validIdent (x :: xs) hne hvs (.Sym .Assign :: (tokens e.pieces ++ r))
      (by simp)
    simp only [Statement.pieces, sym_eq, tokens_tok, tokens_append, List.cons_append,
      List.append_assoc, List.length_cons, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hrest : ∀ r', parseExpr m (tokens e.pieces ++ r) = r' →
        (do let (vs, r) ← parseIdents validIdent (tokens (identsPieces (x :: xs)) ++ .Sym .Assign ::
              (tokens e.pieces ++ r))
            let r ← expect (.Sym .Assign) r
            let (e, r) ← parseExpr m r
            return (Statement.Assignment vs e, r)) =
          r'.map fun (e, r) => (.Assignment (x :: xs) e, r) := by
      intro r' h; rw [hids]; simp [bind, Except.bind, expect, h, Except.map]; cases r' <;> rfl
    rw [parseStatement.eq_def]
    cases xs with
    | nil =>
      simp only [identsPieces, List.flatMap_nil, word_eq, tokens_tok, tokens_nil,
        List.cons_append, List.nil_append] at hrest ⊢
      simp only [hx, ite_false]
      rw [hrest _ rfl, parseExpr_pieces e he r (expr_follow_of_stmt hr) m (by simp at hn; omega)]
      rfl
    | cons y ys =>
      rw [identsPieces_cons_cons] at hrest ⊢
      simp only [word_eq, sym_eq, tokens_tok, List.cons_append] at hrest ⊢
      simp only [hx, ite_false]
      rw [hrest _ rfl, parseExpr_pieces e he r (expr_follow_of_stmt hr) m (by
        rw [identsPieces_cons_cons] at hn; simp at hn; omega)]
      rfl
  | .If c b, hv, k, r, _, n, hn => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    simp only [Statement.pieces, word_eq, tokens_tok, tokens_append, List.cons_append,
      List.append_assoc, List.length_cons, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseStatement.eq_def]
    simp only [show ("if" = "function") = False by decide, show ("if" = "let") = False by decide,
      ite_true, ite_false]
    rw [parseExpr_pieces c hv.1 _ (block_follow b k r) m (by omega)]
    bind_simp
    rw [parseBlock_pieces b hv.2 k r m (by omega)]
  | .Expression e, hv, k, r, hr, n, hn => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    obtain ⟨hcall, hv⟩ := hv
    simp only [Statement.pieces] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have he := parseExpr_pieces e hv r (expr_follow_of_stmt hr) m (by omega)
    rw [parseStatement.eq_def]
    cases e with
    | FunctionCall f args =>
      simp only [Expression.valid, Bool.and_eq_true] at hv
      have hf := validIdent_ne hv.1
      simp only [Expression.pieces, word_eq, sym_eq, tokens_tok, tokens_append,
        List.cons_append] at he ⊢
      simp only [hf, ite_false]
      rw [he]; rfl
    | Identifier _ | Literal _ => simp at hcall
  | .ForLoop i c p b, hv, k, r, _, n, hn => by
    simp only [Statement.valid, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hi, hc⟩, hp⟩, hb⟩ := hv
    simp only [Statement.pieces, word_eq, tokens_tok, tokens_append, List.cons_append,
      List.append_assoc, List.length_cons, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseStatement.eq_def]
    simp only [show ("for" = "function") = False by decide, show ("for" = "let") = False by decide,
      show ("for" = "if") = False by decide, ite_true, ite_false]
    rw [parseBlock_pieces i hi k _ m (by omega)]
    bind_simp
    rw [parseExpr_pieces c hc _ (block_follow p k _) m (by omega)]
    bind_simp
    rw [parseBlock_pieces p hp k _ m (by omega)]
    bind_simp
    rw [parseBlock_pieces b hb k r m (by omega)]
  | .Break, _, k, r, _, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [Statement.pieces] at hn; omega⟩
    rfl
  | .Continue, _, k, r, _, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [Statement.pieces] at hn; omega⟩
    rfl
  | .Leave, _, k, r, _, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [Statement.pieces] at hn; omega⟩
    rfl

end

theorem map_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) :
    (l.map (·.toNat.toUInt8)).map (fun b => Char.ofNat b.toNat) = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.map_cons]
    rw [ih (fun d hd => h d (by simp [hd]))]
    have := h c (by simp)
    simp [Nat.mod_eq_of_lt (by omega : c.toNat < 256)]

theorem asciiName_ascii (s : String) (h : isAscii s = true) : asciiName (ascii s) = .ok s := by
  simp only [isAscii, List.all_eq_true, decide_eq_true_eq] at h
  have hall : (ascii s).all (· < 128) = true := by
    simp only [ascii, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
    intro c hc
    have := h c hc
    simp [UInt8.lt_iff_toNat_lt, Nat.mod_eq_of_lt (by omega : c.toNat < 256), this]
  unfold asciiName
  rw [ite_eq_left_iff.mpr (fun h => absurd hall h)]
  unfold ascii
  rw [map_ascii _ h, String.ofList_toList]

theorem parseItems_data (ds : List Data) (hv : ds.all (isAscii ·.name) = true) (k : Nat)
    (r : List Token) (n : Nat) (hn : 3 * ((tokens (ds.flatMap (Data.pieces k))).length + 1) ≤ n) :
    parseItems n (tokens (ds.flatMap (Data.pieces k)) ++ .Sym .RBrace :: r) =
      .ok (([], ds), r) := by
  induction ds generalizing n with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hv
    simp only [List.flatMap_cons, Data.pieces, word_eq, tokens_line, tokens_tok,
      List.cons_append, List.nil_append, List.length_cons] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseItems.eq_def]
    simp only [asciiName_ascii d.name hv.1]
    bind_simp
    rw [ih hv.2 m (by omega)]

mutual

theorem parseObject_pieces : ∀ (o : Object), o.valid = true → ∀ (k : Nat) (r : List Token) n,
    3 * (tokens (o.pieces k)).length ≤ n → parseObject n (tokens (o.pieces k) ++ r) = .ok (o, r)
  | ⟨name, code, objects, data⟩, hv, k, r, n, hn => by
    simp only [Object.valid, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨⟨hname, hcode⟩, hobjects⟩, hdata⟩, hnames⟩ := hv
    simp only [Object.pieces, word_eq, sym_eq, tokens_tok, tokens_line, tokens_append,
      tokens_nil, List.cons_append, List.append_assoc, List.nil_append, List.length_cons,
      List.length_append, List.length_nil] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [parseObject.eq_def]
    simp only [asciiName_ascii name hname]
    bind_simp
    rw [parseBlock_pieces code hcode (k + 2) _ m (by omega)]
    simp only
    rw [← List.append_assoc, parseItems_pieces objects hobjects data hdata (k + 2) r m (by omega)]
    simp only [Option.isNone_iff_eq_none] at hnames
    simp only [hnames]

theorem parseItems_pieces : ∀ (os : List Object), objectsValid os = true →
    ∀ (ds : List Data), ds.all (isAscii ·.name) = true → ∀ (k : Nat) (r : List Token) n,
    3 * ((tokens (objectsPieces k os)).length + (tokens (ds.flatMap (Data.pieces k))).length + 1)
      ≤ n →
    parseItems n (tokens (objectsPieces k os) ++ tokens (ds.flatMap (Data.pieces k)) ++
      .Sym .RBrace :: r) = .ok ((os, ds), r)
  | [], _, ds, hds, k, r, n, hn => by
    simp only [objectsPieces, tokens_nil, List.nil_append, List.length_nil] at hn ⊢
    exact parseItems_data ds hds k r n (by omega)
  | ⟨name, code, objects, data⟩ :: os, hv, ds, hds, k, r, n, hn => by
    simp only [objectsValid, Bool.and_eq_true] at hv
    have hle : 1 ≤ (tokens (Object.pieces k ⟨name, code, objects, data⟩)).length := by
      simp [Object.pieces]
    simp only [objectsPieces, tokens_line, tokens_append, List.length_append] at hn ⊢
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ho := parseObject_pieces ⟨name, code, objects, data⟩ hv.1 k
      (tokens (objectsPieces k os) ++ tokens (ds.flatMap (Data.pieces k)) ++ .Sym .RBrace :: r) m
      (by omega)
    rw [parseItems.eq_def]
    simp only [List.append_assoc] at ho ⊢
    simp only [Object.pieces, word_eq, sym_eq, tokens_tok, tokens_line, tokens_append, tokens_nil,
      List.cons_append, List.append_assoc, List.nil_append] at ho ⊢
    split
    · simp_all
    · simp_all
    rw [ho]
    bind_simp
    rw [← List.append_assoc, parseItems_pieces os hv.2 ds hds k r m (by omega)]

end

end Yul
