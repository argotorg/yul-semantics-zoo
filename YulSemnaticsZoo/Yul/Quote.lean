import Lean
import YulSemnaticsZoo.Yul.Parser

set_option doc.verso true

/-!
# Yul: quasiquoter

`[yul| … |]` is Yul text, which {name}`Yul.Expression.parse`, `Statement.parse`, `Block.parse` or
`Object.parse` parses when Lean elaborates it; the expected type tells which one.

```
def b : Yul.Block := [yul| { let x := add(1, 2) } |]
```
-/

namespace Yul
open Lean Elab Term Meta Parser

deriving instance ToExpr for Yul.Literal
deriving instance ToExpr for Expression
deriving instance ToExpr for Block, Statement
deriving instance ToExpr for Data
deriving instance ToExpr for Object

/-- the text up to `|]`, and `|]` -/
partial def quoteBodyFn : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError
  else
    let curr := c.get' i h
    let i := c.next' i h
    if curr == '|' then
      if h : c.atEnd i then s.mkEOIError
      else if c.get' i h == ']' then s.next' c i h
      else quoteBodyFn c (s.setPos i)
    else quoteBodyFn c (s.setPos i)

def quoteBody : Parser := { fn := rawFn quoteBodyFn (trailingWs := true) }

@[combinator_parenthesizer quoteBody]
def quoteBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter quoteBody]
def quoteBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

syntax (name := yulQuote) "[yul|" quoteBody : term

@[term_elab yulQuote]
def elabYulQuote : TermElab := fun stx expected? => do
  -- the atom ends with `|]`
  let text := String.ofList (stx[1].getAtomVal.toList.dropLast.dropLast)
  let some expected := expected?
    | throwError "[yul| … |] needs an expected type: Expression, Statement, Block or Object"
  let expected ← whnfR (← instantiateMVars expected)
  let result ←
    if expected.isConstOf ``Expression then pure ((Expression.parse text).map toExpr)
    else if expected.isConstOf ``Statement then pure ((Statement.parse text).map toExpr)
    else if expected.isConstOf ``Block then pure ((Block.parse text).map toExpr)
    else if expected.isConstOf ``Object then pure ((Object.parse text).map toExpr)
    else throwError "[yul| … |] makes an Expression, Statement, Block or Object, not {expected}"
  match result with
  | .ok e => return e
  | .error msg => throwError "Yul: {msg}"

end Yul
