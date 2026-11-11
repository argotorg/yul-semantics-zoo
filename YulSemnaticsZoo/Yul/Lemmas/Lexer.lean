import YulSemnaticsZoo.Yul.Lexer
import YulSemnaticsZoo.Yul.Printer

set_option doc.verso true

/-!
# Yul: lexing printed text gives the printed tokens

{lit}`lex_print`: for pieces whose words the lexer can read as words, lexing the rendered text gives
the tokens of the pieces.
-/

namespace Yul

/-! ## Characters -/

theorem hexValue_hexDigit : ∀ d, d < 16 → hexValue (hexDigit d) = some d := by decide

theorem digit_facts : ∀ d, d < 10 →
    hexValue (Char.ofNat (48 + d)) = some d ∧ (Char.ofNat (48 + d)).isDigit = true ∧
    isIdentStart (Char.ofNat (48 + d)) = false ∧ isSpace (Char.ofNat (48 + d)) = false ∧
    Char.ofNat (48 + d) ≠ '/' ∧ Char.ofNat (48 + d) ≠ 'x' := by decide

theorem toNat_ofNat_ascii : ∀ n, n < 128 → (Char.ofNat n).toNat = n := by decide

theorem utf8EncodeChar_ascii :
    ∀ n, n < 128 → String.utf8EncodeChar (Char.ofNat n) = [n.toUInt8] := by
  decide

/-- the characters that {name}`render` puts after a word or a number -/
def stopChars : List Char := [' ', '\n', '(', ')', ',']

theorem stopChars_facts : ∀ c ∈ stopChars,
    isIdentChar c = false ∧ c.isDigit = false ∧ c ≠ 'x' ∧ c ≠ '"' ∧ c ≠ '\'' := by decide

/-! ## Lexing one token -/

theorem span_append (p : Char → Bool) (s r : List Char) (hs : ∀ c ∈ s, p c = true)
    (hr : ∀ c ∈ r.head?, p c = false) : span p (s ++ r) = (s, r) := by
  induction s with
  | nil => cases r <;> simp_all [span]
  | cons c s ih => simp_all [span]

theorem lexToken_word (c : Char) (cs r : List Char) (hc : isIdentStart c = true)
    (hcs : ∀ d ∈ cs, isIdentChar d = true) (hr : ∀ d ∈ r.head?, d ∈ stopChars) :
    lexToken c (cs ++ r) = .ok (.Word (String.ofList (c :: cs)), r) := by
  have hspan : span isIdentChar (c :: cs ++ r) = (c :: cs, r) := by
    apply span_append
    · intro d hd
      cases hd with
      | head => simp [isIdentChar, hc]
      | tail _ h => exact hcs d h
    · intro d hd; exact (stopChars_facts d (hr d hd)).1
  simp only [lexToken, hc, ite_true, ← List.cons_append, hspan]
  split
  · next q r' heq =>
    have hq := stopChars_facts q (hr q (by simp))
    simp_all
  · rfl

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  rw [decimal]; split <;> simp

theorem decimal_digits (n : Nat) : ∀ d ∈ decimal n,
    d.isDigit = true ∧ isIdentStart d = false ∧ isSpace d = false ∧ d ≠ '/' ∧ d ≠ 'x' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · next h =>
      intro d hd
      simp at hd
      have := digit_facts n h
      subst hd
      exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
    · next h =>
      intro d hd
      simp at hd
      cases hd with
      | inl hd => exact ih (n / 10) (by omega) d hd
      | inr hd =>
        have := digit_facts (n % 10) (by omega)
        subst hd
        exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

theorem digitsValue_decimal (n : Nat) : digitsValue 10 (decimal n) = some n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · next h => simp [digitsValue, (digit_facts n h).1, h]
    · next h =>
      rw [digitsValue, List.foldlM_append, ← digitsValue, ih (n / 10) (by omega)]
      simp [(digit_facts (n % 10) (by omega)).1, Nat.mod_lt n (by omega : 10 > 0)]
      omega

theorem nonzero_digit : ∀ k, k < 10 → 1 ≤ k → Char.ofNat (48 + k) ≠ '0' := by decide

theorem decimal_single {n : Nat} {c : Char} (h : decimal n = [c]) : n < 10 := by
  rw [decimal] at h
  split at h
  · assumption
  · obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil (decimal_ne_nil (n / 10))
    rw [hd] at h
    simp at h

/-- a printed decimal number of two or more digits does not start with {lit}`0` -/
theorem decimal_head (n : Nat) : ∀ c d ds, decimal n = c :: d :: ds → c ≠ '0' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c d ds h
    rw [decimal] at h
    split at h
    · simp at h
    · next hn =>
      obtain ⟨c', cs', hd⟩ := List.exists_cons_of_ne_nil (decimal_ne_nil (n / 10))
      rw [hd] at h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      cases cs' with
      | nil =>
        have h10 := decimal_single hd
        rw [decimal, ite_eq_left_iff.mpr (fun h => absurd h10 h)] at hd
        simp only [List.cons.injEq, and_true] at hd
        rw [← hd]
        exact nonzero_digit (n / 10) h10 (by omega)
      | cons d' ds' => exact ih (n / 10) (by omega) c' d' ds' hd

theorem lexToken_number (n : Nat) (r : List Char) (hr : ∀ d ∈ r.head?, d ∈ stopChars) :
    ∃ c cs, decimal n = c :: cs ∧ isSpace c = false ∧ c ≠ '/' ∧
      lexToken c (cs ++ r) = .ok (.Number n, r) := by
  obtain ⟨c, cs, hdec⟩ := List.exists_cons_of_ne_nil (decimal_ne_nil n)
  have hd := decimal_digits n
  rw [hdec] at hd
  have hc := hd c (by simp)
  refine ⟨c, cs, hdec, hc.2.2.1, hc.2.2.2.1, ?_⟩
  have hspan : span Char.isDigit (c :: cs ++ r) = (c :: cs, r) := by
    apply span_append
    · intro d hd'; exact (hd d hd').1
    · intro d hd'; exact (stopChars_facts d (hr d hd')).2.1
  have hval : digitsValue 10 (c :: cs) = some n := hdec ▸ digitsValue_decimal n
  have hended : ended (.Number n) r = .ok (.Number n, r) := by
    cases r with
    | nil => rfl
    | cons d r => simp [ended, (stopChars_facts d (hr d (by simp))).1]
  have hnot : ∀ x xs, c :: cs ≠ '0' :: x :: xs := by
    intro x xs h
    simp only [List.cons.injEq] at h
    obtain ⟨hc0, rfl⟩ := h
    exact decimal_head n c x xs hdec hc0
  simp only [lexToken, hc.2.1, hc.1, Bool.false_eq_true, ite_false, ite_true]
  split
  · next cs' heq =>
    -- `0x` cannot start a printed number: the character after `0` is a digit or a stop char
    exfalso
    cases cs with
    | nil =>
      simp at heq
      exact (stopChars_facts 'x' (hr 'x' (by simp [heq]))).2.2.1 rfl
    | cons d ds =>
      simp at heq
      exact (hd d (by simp)).2.2.2.2 heq.1
  · -- a printed number does not start with `0` and another digit
    simp only [← List.cons_append, hspan, hval]
    exact hended

theorem digitsValue_hexByte (b : UInt8) :
    digitsValue 16 [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)] = some b.toNat := by
  have hlt := b.toNat_lt
  simp [digitsValue, hexValue_hexDigit (b.toNat / 16) (by omega),
    hexValue_hexDigit (b.toNat % 16) (by omega), show b.toNat / 16 < 16 by omega,
    Nat.mod_lt _ (by omega : 16 > 0)]
  omega

theorem lexString_escape (b : UInt8) (cs : List Char) :
    lexString (escape b ++ cs) = (lexString cs).map fun (bs, r) => (b :: bs, r) := by
  unfold escape
  split
  · next h => subst h; rw [lexString.eq_def]; simp
  · split
    · next h => subst h; rw [lexString.eq_def]; simp
    · split
      · next h1 h2 h3 =>
        have hb : b.toNat < 128 := by have := h3.2; simp [UInt8.lt_iff_toNat_lt] at this; omega
        have hn := toNat_ofNat_ascii b.toNat hb
        have hne : ∀ c : Char, c.toNat ≠ b.toNat → Char.ofNat b.toNat ≠ c := by
          intro c hc h; exact hc (by rw [← h, hn])
        have h20 := h3.1
        simp [UInt8.le_iff_toNat_le] at h20
        have hq := hne '"' (by intro h; exact h1 (UInt8.toNat_inj.mp (by simpa using h.symm)))
        have hs := hne '\\' (by intro h; exact h2 (UInt8.toNat_inj.mp (by simpa using h.symm)))
        have hl1 := hne '\n' (by simp; omega)
        have hl2 := hne '\r' (by simp; omega)
        rw [List.singleton_append, lexString.eq_def]
        simp [hq, hs, hl1, hl2, utf8EncodeChar_ascii b.toNat hb]
      · rw [lexString.eq_def]
        simp [digitsValue_hexByte]

theorem lexString_escapes (bs : List UInt8) (r : List Char) :
    lexString (bs.flatMap escape ++ '"' :: r) = .ok (bs, r) := by
  induction bs with
  | nil => rw [lexString.eq_def]; simp
  | cons b bs ih => simp [List.flatMap_cons, List.append_assoc, lexString_escape, ih, Except.map]

/-! ## Lexing printed tokens -/

def Token.lexable : Token → Bool
  | .Word s => isWord s
  | _ => true

/-- the characters {lit}`r` after the characters of {lit}`t` do not change how the lexer reads
  {lit}`t` -/
def Token.follows : Token → List Char → Prop
  | .Word _, r => ∀ c ∈ r.head?, c ∈ stopChars
  | .Number _, r => ∀ c ∈ r.head?, c ∈ stopChars
  | _, _ => True

theorem identStart_facts (c : Char) (h : isIdentStart c = true) :
    isSpace c = false ∧ c ≠ '/' := by
  constructor
  · cases hs : isSpace c
    · rfl
    · simp [isSpace] at hs
      rcases hs with ((hs | hs) | hs) | hs <;> subst hs <;> revert h <;> decide
  · intro hc; subst hc; simp [isIdentStart] at h

theorem lexToken_chars (t : Token) (ht : t.lexable = true) (r : List Char) (hr : t.follows r) :
    ∃ c cs, t.chars = c :: cs ∧ isSpace c = false ∧ c ≠ '/' ∧
      lexToken c (cs ++ r) = .ok (t, r) := by
  cases t with
  | Word s =>
    simp only [Token.lexable, isWord] at ht
    split at ht
    · next c cs heq =>
      simp only [Bool.and_eq_true, List.all_eq_true] at ht
      refine ⟨c, cs, by simp [Token.chars, heq], (identStart_facts c ht.1).1,
        (identStart_facts c ht.1).2, ?_⟩
      rw [lexToken_word c cs r ht.1 ht.2 hr, ← heq, String.ofList_toList]
    · simp at ht
  | Number n =>
    obtain ⟨c, cs, h1, h2, h3, h4⟩ := lexToken_number n r hr
    exact ⟨c, cs, by simp [Token.chars, h1], h2, h3, h4⟩
  | Str bs =>
    refine ⟨'"', bs.flatMap escape ++ ['"'], rfl, by decide, by decide, ?_⟩
    simp [lexToken, isIdentStart, lexString_escapes, Except.map]
  | Sym s => cases s <;> exact ⟨_, _, rfl, by decide, by decide, rfl⟩


theorem lexWith_spaces (k m : Nat) (x : List Char) :
    lexWith (m + k) (List.replicate k ' ' ++ x) = lexWith m x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, show m + (k + 1) = (m + k) + 1 by omega]
    simp [lexWith, isSpace, ih]

theorem gap_false {t u : Token} (h : gap t u = false) :
    t = .Sym .LParen ∨ u = .Sym .LParen ∨ u = .Sym .RParen ∨ u = .Sym .Comma := by
  unfold gap at h
  split at h <;> simp_all

theorem lexWith_render (ps : List Piece) (h : ∀ t ∈ tokens ps, t.lexable = true) (n : Nat)
    (hn : (render ps).length ≤ n) : lexWith n (render ps) = .ok (tokens ps) := by
  induction ps generalizing n with
  | nil => cases n <;> rfl
  | cons p ps ih =>
    cases p with
    | line k =>
      simp only [render, List.length_cons, List.length_append, List.length_replicate] at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = (m + k) + 1 := ⟨n - k - 1, by omega⟩
      have hps : ∀ t ∈ tokens ps, t.lexable = true := fun t ht => h t (by simpa [tokens] using ht)
      show lexWith _ ('\n' :: (List.replicate k ' ' ++ render ps)) = _
      simp only [lexWith, isSpace]
      simp only [beq_self_eq_true, Bool.or_true, Bool.true_or, ite_true, lexWith_spaces]
      simpa [tokens] using ih hps m (by omega)
    | tok t =>
      have ht : t.lexable = true := h t (by simp [tokens])
      have hps : ∀ t ∈ tokens ps, t.lexable = true :=
        fun u hu => h u (by simp [tokens]; right; simpa [tokens] using hu)
      have hsep' : sepBefore t ps = [' '] ∨ sepBefore t ps = [] := by
        unfold sepBefore; split
        · split <;> simp
        · simp
      have hfollow : t.follows (sepBefore t ps ++ render ps) := by
        cases t with
        | Str _ | Sym _ => trivial
        | Word _ | Number _ =>
          intro c hc
          rcases hsep' with hs | hs
          · rw [hs] at hc; simp at hc; subst hc; simp [stopChars]
          · rw [hs] at hc
            simp at hc
            match ps, hs with
            | [], _ => simp [render] at hc
            | .line k :: _, _ => simp [render] at hc; subst hc; simp [stopChars]
            | .tok u :: _, hs =>
              simp only [sepBefore] at hs
              split at hs
              · simp at hs
              · next hg =>
                rcases gap_false (Bool.not_eq_true _ ▸ hg) with h | h | h | h
                · cases h
                all_goals subst h; simp [render, Token.chars] at hc; subst hc; simp [stopChars]
      obtain ⟨c, cs, hch, hsp, hsl, hlex⟩ := lexToken_chars t ht _ hfollow
      have hrender : render (.tok t :: ps) = c :: (cs ++ (sepBefore t ps ++ render ps)) := by
        simp only [render, hch, List.cons_append, List.append_assoc]
      rw [hrender] at hn ⊢
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      have hrest : lexWith m (sepBefore t ps ++ render ps) = .ok (tokens ps) := by
        rcases hsep' with hs | hs
        · rw [hs]
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp [hs] at hn; omega⟩
          simp only [List.singleton_append]
          simp [lexWith, isSpace]
          exact ih hps m' (by simp [hs] at hn; omega)
        · rw [hs]; exact ih hps m (by simp [hs] at hn; omega)
      simp only [lexWith, hsp, hsl, Bool.false_eq_true, ite_false, hlex]
      simp [bind, Except.bind, hrest, tokens, pure, Except.pure]

theorem lex_render (ps : List Piece) (h : ∀ t ∈ tokens ps, t.lexable = true) :
    lex (render ps) = .ok (tokens ps) :=
  lexWith_render ps h _ (Nat.le_refl _)


@[simp] theorem tokens_nil : tokens [] = [] := rfl
@[simp] theorem tokens_tok (t : Token) (ps : List Piece) :
    tokens (.tok t :: ps) = t :: tokens ps := rfl
@[simp] theorem tokens_line (k : Nat) (ps : List Piece) : tokens (.line k :: ps) = tokens ps := rfl
@[simp] theorem tokens_append (a b : List Piece) : tokens (a ++ b) = tokens a ++ tokens b := by
  simp [tokens, List.filterMap_append]
@[simp] theorem word_eq (s : String) : word s = .tok (.Word s) := rfl
@[simp] theorem sym_eq (s : Symbol) : sym s = .tok (.Sym s) := rfl

theorem lex_print {ps : List Piece} (h : (tokens ps).all Token.lexable = true) :
    lex (String.ofList (render ps)).toList = .ok (tokens ps) := by
  rw [String.toList_ofList]
  exact lex_render ps (List.all_eq_true.mp h)

end Yul
