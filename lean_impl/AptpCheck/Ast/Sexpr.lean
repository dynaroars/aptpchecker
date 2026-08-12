import Mathlib

/-!
# S-expression front-end

Reproduces the statement-joining of the reference `read_aptp.py` `read_statements`
(strip `;` comments, join multi-line statements by parenthesis balance) and
provides a small S-expression tokenizer/parser plus an **exact** decimal→`ℚ`
reader. Everything works over `List Char` to be robust to the String API.
-/

namespace AptpCheck.Ast

/-- Split a char list on a separator, keeping empty segments (like Python `str.split(sep)`). -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      let rest := splitOnChar sep cs
      if c == sep then [] :: rest
      else match rest with
           | [] => [[c]]
           | r :: rs => (c :: r) :: rs

/-- Drop leading whitespace. -/
def ltrim (l : List Char) : List Char := l.dropWhile (·.isWhitespace)
/-- Drop trailing whitespace. -/
def rtrim (l : List Char) : List Char := (l.reverse.dropWhile (·.isWhitespace)).reverse
/-- Trim both ends. -/
def trimC (l : List Char) : List Char := rtrim (ltrim l)

/-- Everything before the first `;`. -/
def beforeSemicolon (l : List Char) : List Char := l.takeWhile (· ≠ ';')

/-- Split raw text into statements, joining lines until parentheses balance.
Mirrors `read_statements`; returns each statement as a char list. -/
def readStatements (content : String) : Except String (Array (List Char)) := Id.run do
  let lines := splitOnChar '\n' content.toList
  let mut bal : Int := 0
  let mut stmts : Array (List Char) := #[]
  let mut cur : List Char := []
  for rawLine in lines do
    let line := rtrim (beforeSemicolon (trimC rawLine))
    if line.isEmpty then
      continue
    bal := bal + (line.countP (· == '(') : Int) - (line.countP (· == ')') : Int)
    if bal < 0 then
      return .error "mismatched parenthesis"
    cur := if cur.isEmpty then line else cur ++ (' ' :: line)
    if bal == 0 then
      stmts := stmts.push cur
      cur := []
  if !cur.isEmpty then
    stmts := stmts.push cur
  return .ok stmts

/-- Fold step for `readStatementsFold`; the accumulator is
`(bal, stmts, cur)` (running paren balance, finished statements, current
partial statement), short-circuiting on a paren-balance error. -/
def readStmtStep (acc : Except String (Int × Array (List Char) × List Char))
    (rawLine : List Char) : Except String (Int × Array (List Char) × List Char) :=
  match acc with
  | .error e => .error e
  | .ok (bal, stmts, cur) =>
    let line := rtrim (beforeSemicolon (trimC rawLine))
    if line.isEmpty then .ok (bal, stmts, cur)
    else
      let bal' := bal + (line.countP (· == '(') : Int) - (line.countP (· == ')') : Int)
      if bal' < 0 then .error "mismatched parenthesis"
      else
        let cur' := if cur.isEmpty then line else cur ++ (' ' :: line)
        if bal' == 0 then .ok (bal', stmts.push cur', [])
        else .ok (bal', stmts, cur')

/-- Total `List.foldl`-based reimplementation of `readStatements` with **identical
behaviour** (each fold step threads `(bal, stmts, cur)` through the accumulator and
short-circuits on error, exactly as the `Id.run do` loop did). Used by `parseAptp`
so the statement reader has equational lemmas for the faithfulness proofs;
`readStatements` itself is left intact for `.net`. -/
def readStatementsFold (content : String) : Except String (Array (List Char)) :=
  match (splitOnChar '\n' content.toList).foldl readStmtStep (.ok (0, #[], [])) with
  | .error e => .error e
  | .ok (_, stmts, cur) => .ok (if cur.isEmpty then stmts else stmts.push cur)

/-- An S-expression: an atom or a list. -/
inductive Sexp where
  | atom (s : String)
  | list (xs : List Sexp)
  deriving Repr, Inhabited

/-- Tokenize into `(`, `)` and atom tokens. -/
def tokenize (input : List Char) : List String := Id.run do
  let mut toks : List String := []          -- built in reverse
  let mut cur : List Char := []             -- current atom, reversed
  for c in input do
    if c == '(' || c == ')' then
      if !cur.isEmpty then toks := String.ofList cur.reverse :: toks; cur := []
      toks := String.ofList [c] :: toks
    else if c.isWhitespace then
      if !cur.isEmpty then toks := String.ofList cur.reverse :: toks; cur := []
    else
      cur := c :: cur
  if !cur.isEmpty then toks := String.ofList cur.reverse :: toks
  return toks.reverse

/- Fuel-parameterized S-expression parser, **structural on `fuel`** (so it is a
total definition and the kernel gets equational lemmas). Each `(`-descent and
each list element consumes fuel; `parseStatement` supplies `tokens.length + 1`,
which is always enough since every recursive step consumes ≥ 1 token. The
`out of fuel` branches are therefore dead for `parseStatement`, and the result is
identical to the previous mutual `partial def` on every input.

Pattern order matters: the empty and `)` cases (fuel-independent), then the
out-of-fuel `(` case, then the productive `(` case, then finally the atom case
(so an atom token is never confused with an unmatched paren). -/
mutual
/-- Parse one S-expression given `fuel`, returning the remaining tokens. -/
def parseSexpFuel : Nat → List String → Option (Sexp × List String)
  | _,      []          => none
  | _,      ")" :: _    => none
  | 0,      "(" :: _    => none
  | fuel+1, "(" :: rest =>
      match parseListFuel fuel rest [] with
      | some (xs, rest') => some (Sexp.list xs, rest')
      | none => none
  | _,      a :: rest   => some (Sexp.atom a, rest)

/-- Parse list elements until the matching `)`. Structural on `fuel`. -/
def parseListFuel : Nat → List String → List Sexp → Option (List Sexp × List String)
  | _,      ")" :: rest, acc => some (acc.reverse, rest)
  | _,      [],          _   => none
  | 0,      _,           _   => none
  | fuel+1, toks,        acc =>
      match parseSexpFuel fuel toks with
      | some (e, toks') => parseListFuel fuel toks' (e :: acc)
      | none => none
end

/-- Parse one S-expression, returning the remaining tokens. Supplies fuel equal
to `toks.length + 1`, always enough since each step consumes ≥ 1 token. -/
def parseSexp (toks : List String) : Option (Sexp × List String) :=
  parseSexpFuel (toks.length + 1) toks

/-- Parse a full statement (char list) into one S-expression. -/
def parseStatement (l : List Char) : Option Sexp :=
  match parseSexp (tokenize l) with
  | some (e, _) => some e
  | none => none

/-- Parse a nonempty digit list into a `Nat` (empty → `0`). -/
def natOfDigits? (l : List Char) : Option Nat :=
  l.foldl (fun acc c =>
    match acc with
    | some n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none
    | none => none) (some 0)

/-- Parse a signed decimal literal into the exact rational it denotes.
Handles `123`, `-2.0`, `+1.5`, `.5`, `10.` — no exponent. -/
def parseRat? (s0 : String) : Option ℚ :=
  let (neg, cs) :=
    match s0.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | cs => (false, cs)
  match splitOnChar '.' cs with
  | [i] => (natOfDigits? i).map (fun n => if neg then -(n : ℚ) else (n : ℚ))
  | [i, f] =>
      match natOfDigits? i, natOfDigits? f with
      | some ni, some nf =>
          let q : ℚ := (ni : ℚ) + (nf : ℚ) / (10 : ℚ) ^ f.length
          some (if neg then -q else q)
      | _, _ => none
  | _ => none

end AptpCheck.Ast
