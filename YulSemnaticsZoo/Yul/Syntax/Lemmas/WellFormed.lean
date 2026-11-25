import YulSemnaticsZoo.Yul.Syntax.WellFormed

set_option doc.verso true

/-!
# Yul: lemmas about well-formed ASTs

The clocked semantics uses these lemmas to carry the proofs of well-formedness into the parts of
an AST:
* {lit}`Scope.after` changes only the variables of a scope.
* An expression uses only the variables and the functions of its scope.
* A part that is well-formed stays well-formed with fewer hidden names. The hidden names only
  stop a declaration. The body of a function is thus well-formed in the scope with no hidden
  names.
-/

namespace Yul

variable {d : Dialect} {N : List String}

/-! ## The scope after statements -/

@[simp] theorem Scope.after_funs : (Scope.after Γ s).funs = Γ.funs := by cases s <;> rfl
@[simp] theorem Scope.after_hidden : (Scope.after Γ s).hidden = Γ.hidden := by cases s <;> rfl
@[simp] theorem Scope.after_inLoopBody : (Scope.after Γ s).inLoopBody = Γ.inLoopBody := by
  cases s <;> rfl
@[simp] theorem Scope.after_inInit : (Scope.after Γ s).inInit = Γ.inInit := by cases s <;> rfl
@[simp] theorem Scope.after_inFunction : (Scope.after Γ s).inFunction = Γ.inFunction := by
  cases s <;> rfl

theorem Scope.after_with_hidden : Scope.after { Γ with hidden := H } s =
    { Scope.after Γ s with hidden := H } := by cases s <;> rfl

@[simp] theorem Scope.foldl_funs : (List.foldl Scope.after Γ ss).funs = Γ.funs := by
  induction ss generalizing Γ <;> simp_all
@[simp] theorem Scope.foldl_hidden : (List.foldl Scope.after Γ ss).hidden = Γ.hidden := by
  induction ss generalizing Γ <;> simp_all
@[simp] theorem Scope.foldl_inLoopBody :
    (List.foldl Scope.after Γ ss).inLoopBody = Γ.inLoopBody := by
  induction ss generalizing Γ <;> simp_all
@[simp] theorem Scope.foldl_inInit : (List.foldl Scope.after Γ ss).inInit = Γ.inInit := by
  induction ss generalizing Γ <;> simp_all
@[simp] theorem Scope.foldl_inFunction :
    (List.foldl Scope.after Γ ss).inFunction = Γ.inFunction := by
  induction ss generalizing Γ <;> simp_all

theorem Scope.foldl_with_hidden : List.foldl Scope.after { Γ with hidden := H } ss =
    { List.foldl Scope.after Γ ss with hidden := H } := by
  induction ss generalizing Γ with
  | nil => rfl
  | cons s ss ih => simp only [List.foldl, Scope.after_with_hidden, ih]

/-- the variables of the scope after statements: the variables of their declarations, then the
variables of the scope -/
theorem Scope.foldl_vars_suffix : Γ.vars <:+ (List.foldl Scope.after Γ ss).vars := by
  induction ss generalizing Γ with
  | nil => exact List.suffix_refl _
  | cons s ss ih =>
    refine List.IsSuffix.trans ?_ ih
    cases s <;> simp [Scope.after]

/-! ## Expressions use only the variables and the functions -/

mutual

theorem Expression.wellFormed_congr {Γ Γ' : Scope} (hv : Γ'.vars = Γ.vars)
    (hf : Γ'.funs = Γ.funs) : (e : Expression) → (n : Nat) →
    (e.WellFormed d N Γ' n ↔ e.WellFormed d N Γ n)
  | .Literal _, _ => Iff.rfl
  | .Identifier _, _ => by simp only [Expression.WellFormed, hv]
  | .FunctionCall f args, _ => by
    unfold Expression.WellFormed
    split
    · next kinds _ _ => rw [builtinArgsWellFormed_congr hv hf kinds args]
    · rw [hf, argsWellFormed_congr hv hf args]

theorem argsWellFormed_congr {Γ Γ' : Scope} (hv : Γ'.vars = Γ.vars) (hf : Γ'.funs = Γ.funs) :
    (es : List Expression) → (argsWellFormed d N Γ' es ↔ argsWellFormed d N Γ es)
  | [] => Iff.rfl
  | e :: es => by
    simp only [argsWellFormed, Expression.wellFormed_congr hv hf e 1, argsWellFormed_congr hv hf es]

theorem builtinArgsWellFormed_congr {Γ Γ' : Scope} (hv : Γ'.vars = Γ.vars)
    (hf : Γ'.funs = Γ.funs) : (ks : List Arg) → (es : List Expression) →
    (builtinArgsWellFormed d N Γ' ks es ↔ builtinArgsWellFormed d N Γ ks es)
  | .Expression :: ks, e :: es => by
    simp only [builtinArgsWellFormed, Expression.wellFormed_congr hv hf e 1,
      builtinArgsWellFormed_congr hv hf ks es]
  | .Literal :: ks, _ :: es => by
    simp only [builtinArgsWellFormed, builtinArgsWellFormed_congr hv hf ks es]
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | k :: _, [] => by cases k <;> exact Iff.rfl

end

/-! ## Fewer hidden names -/

theorem Scope.declares_hidden (h : Scope.Declares d Γ xs) (hH : H ⊆ Γ.hidden) :
    Scope.Declares d { Γ with hidden := H } xs :=
  ⟨h.1, fun x hx => let ⟨a, b, c, e, f⟩ := h.2 x hx; ⟨a, b, c, e, fun g => f (hH g)⟩⟩

theorem Expression.wellFormed_hidden {Γ : Scope} (h : Expression.WellFormed d N Γ e n) :
    Expression.WellFormed d N { Γ with hidden := H } e n :=
  (Expression.wellFormed_congr (Γ' := { Γ with hidden := H }) (Γ := Γ) rfl rfl e n).2 h

mutual

theorem Block.wellFormed_hidden {Γ : Scope} (hH : H ⊆ Γ.hidden) :
    (b : Block) → b.WellFormed d N Γ → b.WellFormed d N { Γ with hidden := H }
  | ⟨ss⟩, ⟨h1, h2⟩ =>
    ⟨Scope.declares_hidden h1 hH,
      statementsWellFormed_hidden (Γ := { Γ with funs := functions ss ++ Γ.funs }) hH ss h2⟩

theorem statementsWellFormed_hidden {Γ : Scope} (hH : H ⊆ Γ.hidden) :
    (ss : List Statement) → statementsWellFormed d N Γ ss →
      statementsWellFormed d N { Γ with hidden := H } ss
  | [], _ => trivial
  | s :: ss, ⟨h1, h2⟩ => by
    refine ⟨Statement.wellFormed_hidden hH s h1, ?_⟩
    rw [Scope.after_with_hidden]
    exact statementsWellFormed_hidden (by simpa using hH) ss h2

theorem Statement.wellFormed_hidden {Γ : Scope} (hH : H ⊆ Γ.hidden) :
    (s : Statement) → s.WellFormed d N Γ → s.WellFormed d N { Γ with hidden := H }
  | .Block b, h => Block.wellFormed_hidden hH b h
  | .FunctionDefinition _ _ _ body, ⟨h1, h2, h3⟩ =>
    ⟨h1, Scope.declares_hidden h2 hH,
      Block.wellFormed_hidden (fun x hx => by
        simp only [List.mem_append] at hx ⊢; exact hx.imp id (@hH x)) body h3⟩
  | .VariableDeclaration _ none, ⟨h1, _⟩ => ⟨Scope.declares_hidden h1 hH, trivial⟩
  | .VariableDeclaration _ (some e), ⟨h1, h2⟩ =>
    ⟨Scope.declares_hidden h1 hH, Expression.wellFormed_hidden h2⟩
  | .Assignment _ e, ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, Expression.wellFormed_hidden h3⟩
  | .If c b, ⟨h1, h2⟩ =>
    ⟨Expression.wellFormed_hidden h1, Block.wellFormed_hidden hH b h2⟩
  | .Expression e, h => Expression.wellFormed_hidden h
  | .ForLoop ⟨init⟩ c post body, ⟨h1, h2, h3, h4⟩ => by
    have hH' : H ⊆ (List.foldl Scope.after
        { Γ with inLoopBody := false, inInit := true } init).hidden := by simpa using hH
    refine ⟨statementsWellFormed_hidden (Γ := { Γ with inLoopBody := false, inInit := true }) hH
      init h1, ?_, ?_, ?_⟩
    · show c.WellFormed d N { List.foldl Scope.after
        { { Γ with inLoopBody := false, inInit := true } with hidden := H } init with
          inInit := Γ.inInit } 1
      rw [Scope.foldl_with_hidden]
      exact Expression.wellFormed_hidden (Γ := { List.foldl Scope.after
        { Γ with inLoopBody := false, inInit := true } init with inInit := Γ.inInit }) h2
    · show body.WellFormed d N { { List.foldl Scope.after
        { { Γ with inLoopBody := false, inInit := true } with hidden := H } init with
          inInit := Γ.inInit } with inLoopBody := true }
      rw [Scope.foldl_with_hidden]
      exact Block.wellFormed_hidden (Γ := { { List.foldl Scope.after
        { Γ with inLoopBody := false, inInit := true } init with
          inInit := Γ.inInit } with inLoopBody := true }) hH' body h3
    · show post.WellFormed d N { List.foldl Scope.after
        { { Γ with inLoopBody := false, inInit := true } with hidden := H } init with
          inInit := Γ.inInit }
      rw [Scope.foldl_with_hidden]
      exact Block.wellFormed_hidden (Γ := { List.foldl Scope.after
        { Γ with inLoopBody := false, inInit := true } init with inInit := Γ.inInit }) hH' post h4
  | .Break, h => h
  | .Continue, h => h
  | .Leave, h => h

end

/-- the code of a well-formed object is well-formed in the empty scope -/
theorem Object.wellFormed_code (h : Object.WellFormed d o) : o.code.WellFormed d o.dataNames {} := by
  obtain ⟨_, _, _, _⟩ := o
  exact h.1

end Yul
