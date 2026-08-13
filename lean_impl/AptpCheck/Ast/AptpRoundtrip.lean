import AptpCheck.Ast.Aptp
import AptpCheck.Ast.NetRoundtrip

/-!
# Faithfulness of the `.aptp` S-expression front-end: printer/parser round-trips

This module certifies the (now total) `.aptp` S-expression parser
(`AptpCheck.Ast.parseSexp` / `parseStatement`, backed by the fuel-structural
`parseSexpFuel`/`parseListFuel` in `Ast/Sexpr.lean`) by proving that a canonical
printer round-trips through it. Unlike the sibling `.net` parser (`NetRoundtrip`),
`.aptp` input is *parenthesized*, so both the tokenizer characterization and the
S-expression recursion are new relative to that development. We reuse the `.net`
tokenizer/statement machinery (`tokStep`, `tokPost`, `tokenize_eq`, `jn`,
`joinSp`, `GoodStr`, …) from `AptpCheck.Ast.Roundtrip`.

Main results (all axiom-clean: `propext`, `Classical.choice`, `Quot.sound`):

* `parseSexp_sexpToks`     — the fuel parser recovers any well-formed S-expression
                             from its token list, consuming all tokens.
* `tokenize_jn'` / `tokenize_joinSp'` — the tokenizer recovers a space-joined list
                             of well-formed tokens, *including paren tokens*.
* `parseStatement_stmtChars` — **statement round-trip**: `parseStatement` applied to
                             the printed character form of a well-formed S-expression
                             returns exactly that S-expression.
* `parseRat_RawDec`        — `parseRat?` inverts a canonical decimal printer (numbers
                             carried as a `RawDec` = sign + decimal digit lists, to
                             sidestep the `ℚ`-representability gap).
* `parseVarName_print`, `asBoxUpdate_print`, `asObjective_print_YY`/`_Yub` — the
                             per-statement analyser functions round-trip against a
                             canonical printer for `declare`/box/output constraints.
* `stmtChars_cleanBal`     — the printed form of a well-formed statement is a
                             newline-free, comment/trim-invariant, balanced
                             (`(` = `)`) nonempty line — the shape the statement
                             reader expects.
* `decls_pass` / `asserts_pass` / `box_pass` — folding each of `parseAptp`'s scan
                             passes over the full printed statement list recovers,
                             respectively, `(numInputs, numOutputs, neurons)`, the
                             box lower/upper arrays + objective rows + DNF leaves,
                             and the finalized `(lo,hi)` box.
* `parseAptp_printAptp`    — **top-level round-trip**: for a well-formed
                             `RawProblem`, `parseAptp (printAptp raw) = .ok (decode raw)`.

The scan passes of `parseAptp` are now total `List.foldl`s over `Except`
accumulators (see `Ast/Aptp.lean`); this module characterizes each fold and
composes them (via `readStatementsFold_multi` and `parseStatement_stmtChars`)
into the end-to-end certification.
-/

namespace AptpCheck.Ast.AptpRoundtrip

open AptpCheck.Ast AptpCheck.Ast.Roundtrip

/-! ## Token list of an S-expression -/

mutual
/-- Flat token list of an S-expression (parens included). -/
def sexpToks : Sexp → List String
  | .atom s => [s]
  | .list xs => "(" :: (sexpListToks xs ++ [")"])
/-- Flat token list of a list of S-expressions (concatenation). -/
def sexpListToks : List Sexp → List String
  | [] => []
  | e :: es => sexpToks e ++ sexpListToks es
end

/-! ## Well-formedness -/

/-- Parser-level well-formedness: atom strings are never a bare paren token. -/
inductive WFSexp : Sexp → Prop where
  | atom (s : String) : s ≠ "(" → s ≠ ")" → WFSexp (.atom s)
  | list (xs : List Sexp) : (∀ e ∈ xs, WFSexp e) → WFSexp (.list xs)

/-- Printer-level well-formedness: every atom string is a `GoodStr` char-list
(nonempty, all chars usable inside an atom and not `;`). Implies `WFSexp`. -/
inductive WF : Sexp → Prop where
  | atom (s : String) : GoodStr s.toList → WF (.atom s)
  | list (xs : List Sexp) : (∀ e ∈ xs, WF e) → WF (.list xs)

lemma goodStr_ne_lparen {s : String} (h : GoodStr s.toList) : s ≠ "(" := by
  intro he; subst he
  have : IsTokChar '(' := (h.2 '(' (by decide)).1
  exact absurd this.1 (by decide)

lemma goodStr_ne_rparen {s : String} (h : GoodStr s.toList) : s ≠ ")" := by
  intro he; subst he
  have : IsTokChar ')' := (h.2 ')' (by decide)).1
  exact absurd this.1 (by decide)

mutual
/-- `WF` (GoodStr atoms) refines `WFSexp` (non-paren atoms). -/
theorem WF.toWFSexp (e : Sexp) (h : WF e) : WFSexp e := by
  match e, h with
  | .atom s, .atom _ hg => exact .atom s (goodStr_ne_lparen hg) (goodStr_ne_rparen hg)
  | .list xs, .list _ hxs => exact .list xs (fun e he => WF.toWFSexp e (hxs e he))
end

/-! ## Fuel parser step lemmas -/

lemma pSexp_atom (s : String) (rest : List String) (h1 : s ≠ "(") (h2 : s ≠ ")") (fuel : Nat) :
    parseSexpFuel fuel (s :: rest) = some (Sexp.atom s, rest) := by
  unfold parseSexpFuel; split <;> simp_all

lemma pSexp_lparen (f : Nat) (rest : List String) :
    parseSexpFuel (f+1) ("(" :: rest) =
      (match parseListFuel f rest [] with
       | some (xs, rest') => some (Sexp.list xs, rest')
       | none => none) := rfl

lemma pList_rparen (rest : List String) (acc : List Sexp) (fuel : Nat) :
    parseListFuel fuel (")" :: rest) acc = some (acc.reverse, rest) := by
  simp only [parseListFuel]

/-- Reduction step for a non-`)` head with fuel to spare. -/
lemma pList_cons_reduce (f : Nat) (x : String) (tl : List String) (acc : List Sexp)
    (hx : x ≠ ")") (e : Sexp) (rest' : List String)
    (hpe : parseSexpFuel f (x :: tl) = some (e, rest'))
    (K : Option (List Sexp × List String))
    (hk : parseListFuel f rest' (e :: acc) = K) :
    parseListFuel (f+1) (x :: tl) acc = K := by
  conv_lhs => unfold parseListFuel
  split <;> simp_all

/-! ## Length facts about `sexpToks` -/

lemma sexpToks_len_pos (e : Sexp) : 1 ≤ (sexpToks e).length := by
  cases e <;> simp [sexpToks]

lemma sexpToks_list_len (xs : List Sexp) :
    (sexpToks (.list xs)).length = (sexpListToks xs).length + 2 := by
  simp [sexpToks]

lemma sexpListToks_cons_len (e : Sexp) (es : List Sexp) :
    (sexpListToks (e :: es)).length = (sexpToks e).length + (sexpListToks es).length := by
  simp [sexpListToks]

lemma sexpToks_ne_rparen_head (e : Sexp) (hwf : WFSexp e) :
    ∃ x tl, sexpToks e = x :: tl ∧ x ≠ ")" := by
  cases e with
  | atom s => cases hwf with | atom _ h1 h2 => exact ⟨s, [], rfl, h2⟩
  | list xs => exact ⟨"(", sexpListToks xs ++ [")"], rfl, by simp⟩

/-! ## S-expression parser round-trip -/

set_option maxHeartbeats 1000000 in
/-- Combined parser round-trip, by strong induction on fuel. -/
theorem sexp_roundtrip : ∀ (fuel : Nat),
    (∀ (e : Sexp), WFSexp e → (sexpToks e).length ≤ fuel → ∀ (rest : List String),
        parseSexpFuel fuel (sexpToks e ++ rest) = some (e, rest))
  ∧ (∀ (es : List Sexp), (∀ e ∈ es, WFSexp e) → (sexpListToks es).length + 1 ≤ fuel →
        ∀ (acc : List Sexp) (rest : List String),
        parseListFuel fuel (sexpListToks es ++ ")" :: rest) acc
          = some (acc.reverse ++ es, rest)) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    refine ⟨?_, ?_⟩
    · intro e hwf hlen rest
      cases e with
      | atom s =>
        cases hwf with
        | atom _ h1 h2 =>
          simp only [sexpToks, List.cons_append, List.nil_append]
          exact pSexp_atom s rest h1 h2 fuel
      | list xs =>
        cases hwf with
        | list _ hxs =>
          have hlen2 : (sexpListToks xs).length + 2 ≤ fuel := by
            rw [sexpToks_list_len] at hlen; exact hlen
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          have hf : (sexpListToks xs).length + 1 ≤ f := by omega
          have hre : sexpToks (Sexp.list xs) ++ rest
                   = "(" :: (sexpListToks xs ++ ")" :: rest) := by
            simp [sexpToks, List.append_assoc]
          rw [hre, pSexp_lparen f (sexpListToks xs ++ ")" :: rest),
            (IH f (by omega)).2 xs hxs hf [] rest]
          simp
    · intro es hwf hlen acc rest
      cases es with
      | nil =>
        simp only [sexpListToks, List.nil_append]
        rw [pList_rparen]; simp
      | cons e es' =>
        have hwfe : WFSexp e := hwf e (List.mem_cons_self ..)
        have hwfes : ∀ x ∈ es', WFSexp x := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
        have hposE : 1 ≤ (sexpToks e).length := sexpToks_len_pos e
        have hlenc : (sexpToks e).length + (sexpListToks es').length + 1 ≤ fuel := by
          rw [sexpListToks_cons_len] at hlen; omega
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        obtain ⟨x, tl, hx, hxne⟩ := sexpToks_ne_rparen_head e hwfe
        have hxtl : x :: (tl ++ (sexpListToks es' ++ ")" :: rest))
                  = sexpToks e ++ (sexpListToks es' ++ ")" :: rest) := by
          rw [hx]; rfl
        have hpe : parseSexpFuel f (x :: (tl ++ (sexpListToks es' ++ ")" :: rest)))
                 = some (e, sexpListToks es' ++ ")" :: rest) := by
          rw [hxtl, (IH f (by omega)).1 e hwfe (by omega) (sexpListToks es' ++ ")" :: rest)]
        have hpl : parseListFuel f (sexpListToks es' ++ ")" :: rest) (e :: acc)
                 = some ((e :: acc).reverse ++ es', rest) :=
          (IH f (by omega)).2 es' hwfes (by omega) (e :: acc) rest
        have hre : sexpListToks (e :: es') ++ ")" :: rest
                 = x :: (tl ++ (sexpListToks es' ++ ")" :: rest)) := by
          simp [sexpListToks, hx, List.append_assoc]
        rw [hre]
        exact pList_cons_reduce f x _ acc hxne e _ hpe _ (by rw [hpl]; simp)

/-- `parseSexp` (fuel = length + 1) recovers a `WFSexp` S-expression exactly. -/
theorem parseSexp_sexpToks (e : Sexp) (hwf : WFSexp e) :
    parseSexp (sexpToks e) = some (e, []) := by
  have h := (sexp_roundtrip ((sexpToks e).length + 1)).1 e hwf (by omega) []
  simpa [parseSexp] using h

/-! ## Tokenizer round-trip for parenthesized token streams -/

/-- A token char-list emitted by the printer: a paren token, or a good atom. -/
def TokOK (s : List Char) : Prop :=
  s = ['('] ∨ s = [')'] ∨ (s ≠ [] ∧ ∀ c ∈ s, IsTokChar c)

/-- Flush the pending atom `cur` into the token accumulator. -/
def flushCur (cur : List Char) (toks : List String) : List String :=
  if cur.isEmpty then toks else String.ofList cur.reverse :: toks

lemma tokStep_space' (cur : List Char) (toks : List String) :
    tokStep ⟨cur, toks⟩ ' ' = ⟨[], flushCur cur toks⟩ := by
  rw [tokStep_space]; unfold flushCur; split <;> rfl

lemma flushCur_reverse (cur : List Char) (toks : List String) :
    (flushCur cur toks).reverse = tokPost ⟨cur, toks⟩ := by
  unfold flushCur tokPost; split <;> simp_all

lemma tokStep_lparen_empty (toks : List String) :
    tokStep (⟨[], toks⟩ : MProd (List Char) (List String)) '('
      = ⟨[], String.ofList ['('] :: toks⟩ := by
  unfold tokStep; simp

lemma tokStep_rparen_empty (toks : List String) :
    tokStep (⟨[], toks⟩ : MProd (List Char) (List String)) ')'
      = ⟨[], String.ofList [')'] :: toks⟩ := by
  unfold tokStep; simp

lemma tokPost_empty (toks : List String) :
    tokPost (⟨[], toks⟩ : MProd (List Char) (List String)) = toks.reverse := by
  unfold tokPost; simp

/-- Master loop invariant: folding `tokStep` over `jn ss` for `TokOK` tokens. -/
lemma tokPost_foldl_jn' (ss : List (List Char)) (hv : ∀ s ∈ ss, TokOK s) :
    ∀ (cur : List Char) (toks : List String),
      tokPost ((jn ss).foldl tokStep ⟨cur, toks⟩)
        = tokPost ⟨cur, toks⟩ ++ ss.map (fun s => String.ofList s) := by
  induction ss with
  | nil => intro cur toks; simp [jn]
  | cons s ss ih =>
    intro cur toks
    have hs : TokOK s := hv s (List.mem_cons_self ..)
    have hss : ∀ x ∈ ss, TokOK x := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    simp only [jn, List.foldl_cons, List.foldl_append]
    rw [tokStep_space']
    rcases hs with rfl | rfl | ⟨hsne, hstok⟩
    · simp only [List.foldl_cons, List.foldl_nil, tokStep_lparen_empty]
      rw [ih hss [] (String.ofList ['('] :: flushCur cur toks), tokPost_empty,
        ← flushCur_reverse cur toks]
      simp [List.reverse_cons]
    · simp only [List.foldl_cons, List.foldl_nil, tokStep_rparen_empty]
      rw [ih hss [] (String.ofList [')'] :: flushCur cur toks), tokPost_empty,
        ← flushCur_reverse cur toks]
      simp [List.reverse_cons]
    · have hsrev : s.reverse.isEmpty = false := by simp [hsne]
      rw [foldl_tokStep_normal s hstok [] (flushCur cur toks), List.append_nil,
        ih hss s.reverse (flushCur cur toks)]
      rw [show tokPost (⟨s.reverse, flushCur cur toks⟩ : MProd (List Char) (List String))
            = (flushCur cur toks).reverse ++ [String.ofList s] from by unfold tokPost; simp [hsrev]]
      rw [flushCur_reverse]
      simp [List.map_cons]

/-- Tokenizing a `jn`-join of `TokOK` tokens (parens or atoms) recovers them. -/
theorem tokenize_jn' (ss : List (List Char)) (hv : ∀ s ∈ ss, TokOK s) :
    tokenize (jn ss) = ss.map (fun s => String.ofList s) := by
  rw [tokenize_eq, tokPost_foldl_jn' ss hv [] []]
  simp [tokPost_empty]

lemma tokenize_nil : tokenize ([] : List Char) = [] := by
  rw [tokenize_eq]; simp [tokPost_empty]

lemma tokenize_cons_space (rest : List Char) : tokenize (' ' :: rest) = tokenize rest := by
  rw [tokenize_eq, tokenize_eq]
  simp only [List.foldl_cons]
  rw [show tokStep (⟨[], []⟩ : MProd (List Char) (List String)) ' ' = ⟨[], []⟩ from by
    rw [tokStep_space']; simp [flushCur]]

/-- Tokenizing a `joinSp`-join (single-space separated, no leading space) of
`TokOK` tokens recovers them. -/
theorem tokenize_joinSp' (ss : List (List Char)) (hv : ∀ s ∈ ss, TokOK s) :
    tokenize (joinSp ss) = ss.map (fun s => String.ofList s) := by
  cases ss with
  | nil => simp [joinSp, tokenize_nil]
  | cons s rest =>
    have h2 : tokenize (jn (s :: rest)) = (s :: rest).map (fun s => String.ofList s) :=
      tokenize_jn' (s :: rest) hv
    rw [jn_cons_eq, tokenize_cons_space] at h2
    exact h2

/-! ## TokOK-ness of a printed S-expression's tokens -/

lemma goodStr_charlist_tokOK {s : String} (h : GoodStr s.toList) : TokOK s.toList := by
  right; right; exact ⟨h.1, fun c hc => (h.2 c hc).1⟩

mutual
theorem sexpToks_tokOK (e : Sexp) (hwf : WF e) : ∀ t ∈ sexpToks e, TokOK t.toList := by
  match e, hwf with
  | .atom s, .atom _ hg =>
    intro t ht
    simp only [sexpToks, List.mem_singleton] at ht
    subst ht; exact goodStr_charlist_tokOK hg
  | .list xs, .list _ hxs =>
    intro t ht
    simp only [sexpToks, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | rfl
    · left; rfl
    · exact sexpListToks_tokOK xs hxs t ht
    · right; left; rfl
theorem sexpListToks_tokOK (es : List Sexp) (hwf : ∀ e ∈ es, WF e) :
    ∀ t ∈ sexpListToks es, TokOK t.toList := by
  match es, hwf with
  | [], _ => intro t ht; simp [sexpListToks] at ht
  | e :: es', hwf =>
    intro t ht
    simp only [sexpListToks, List.mem_append] at ht
    rcases ht with ht | ht
    · exact sexpToks_tokOK e (hwf e (List.mem_cons_self ..)) t ht
    · exact sexpListToks_tokOK es' (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) t ht
end

/-! ## Statement-level round-trip -/

/-- The printed character form of one statement: the S-expression's tokens,
space-separated (no leading/trailing space). -/
def stmtChars (e : Sexp) : List Char := joinSp ((sexpToks e).map String.toList)

/-- Every char-list token of a `WF` S-expression is `TokOK`. -/
lemma sexpToks_charlists_tokOK (e : Sexp) (hwf : WF e) :
    ∀ s ∈ (sexpToks e).map String.toList, TokOK s := by
  intro s hs
  rw [List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact sexpToks_tokOK e hwf t ht

/-- **Statement round-trip.** `parseStatement` on the printed character form of a
well-formed S-expression returns exactly that S-expression. -/
theorem parseStatement_stmtChars (e : Sexp) (hwf : WF e) :
    parseStatement (stmtChars e) = some e := by
  have htok : tokenize (stmtChars e) = sexpToks e := by
    unfold stmtChars
    rw [tokenize_joinSp' _ (sexpToks_charlists_tokOK e hwf)]
    simp [List.map_map]
  unfold parseStatement
  rw [htok, parseSexp_sexpToks e (WF.toWFSexp e hwf)]

/-! ## Exact decimals: `parseRat?` inverts a canonical decimal printer

`box` bounds and objective RHS values are `ℚ` read by `parseRat?` from finite
decimals; arbitrary `ℚ` (e.g. `1/3`) is not printable. Following the `.net`
"carry the raw source form" trick, we carry each number as a `RawDec` (sign +
decimal digit lists) and prove `parseRat?` recovers its exact value. -/

/-- Total decimal fold (matches `natOfDigits?` on valid digit lists). -/
def natFromDigits (l : List Char) : Nat :=
  l.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

lemma natOfDigits_allDigit (l : List Char) (h : ∀ c ∈ l, c.isDigit) :
    natOfDigits? l = some (natFromDigits l) := by
  unfold natOfDigits? natFromDigits
  suffices H : ∀ (start : Nat),
      l.foldl (fun acc c => match acc with
        | some n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none
        | none => none) (some start)
        = some (l.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) start) by
    exact H 0
  induction l with
  | nil => intro start; rfl
  | cons c cs ih =>
    intro start
    have hc : c.isDigit := h c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, x.isDigit := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons, hc, if_true]
    exact ih hcs (start * 10 + (c.toNat - '0'.toNat))

lemma splitOnChar_no_sep' (sep : Char) (l : List Char) (h : sep ∉ l) :
    splitOnChar sep l = [l] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ sep := by simp at h; tauto
    have hcs : sep ∉ cs := by simp at h ⊢; tauto
    unfold splitOnChar
    simp only [beq_iff_eq, hc, ih hcs]
    rfl

lemma splitOnChar_one_sep (sep : Char) (l1 l2 : List Char) (h : sep ∉ l1) :
    splitOnChar sep (l1 ++ sep :: l2) = l1 :: splitOnChar sep l2 := by
  induction l1 with
  | nil =>
    conv_lhs => rw [List.nil_append]; unfold splitOnChar
    simp
  | cons c cs ih =>
    have hc : c ≠ sep := by simp at h; tauto
    have hcs : sep ∉ cs := by simp at h ⊢; tauto
    conv_lhs => rw [List.cons_append]; unfold splitOnChar
    rw [ih hcs]
    simp [hc]

lemma allDigit_notMem_dot (l : List Char) (h : ∀ c ∈ l, c.isDigit) : '.' ∉ l := by
  intro hm; have := h '.' hm; simp at this

lemma isDigit_ne_underscore {c : Char} (h : c.isDigit) : c ≠ '_' := by
  intro he; subst he; simp at h

/-- A raw decimal literal: sign and decimal digit lists for integer/fraction. -/
structure RawDec where
  neg : Bool
  intDigits : List Char
  fracDigits : List Char

/-- The exact rational the decimal denotes. -/
def RawDec.value (d : RawDec) : ℚ :=
  let q : ℚ := (natFromDigits d.intDigits : ℚ)
             + (natFromDigits d.fracDigits : ℚ) / (10 : ℚ) ^ d.fracDigits.length
  if d.neg then -q else q

/-- Canonical decimal characters, always carrying an explicit sign. -/
def RawDec.chars (d : RawDec) : List Char :=
  (if d.neg then '-' else '+') :: d.intDigits
    ++ (if d.fracDigits.isEmpty then [] else '.' :: d.fracDigits)

/-- Well-formed raw decimal: nonempty integer part, all decimal digits. -/
def RawDec.WF (d : RawDec) : Prop :=
  (d.intDigits ≠ [] ∧ ∀ c ∈ d.intDigits, c.isDigit) ∧ (∀ c ∈ d.fracDigits, c.isDigit)

set_option linter.unusedSimpArgs false in
/-- **`parseRat?` inverts the canonical decimal printer.** -/
theorem parseRat_RawDec (d : RawDec) (hwf : d.WF) :
    parseRat? (String.ofList d.chars) = some d.value := by
  obtain ⟨neg, intD, fracD⟩ := d
  obtain ⟨⟨hine, hidig⟩, hfdig⟩ := hwf
  have hidot : '.' ∉ intD := allDigit_notMem_dot _ hidig
  have hfdot : '.' ∉ fracD := allDigit_notMem_dot _ hfdig
  have hni : natOfDigits? intD = some (natFromDigits intD) := natOfDigits_allDigit _ hidig
  have hnf : natOfDigits? fracD = some (natFromDigits fracD) := natOfDigits_allDigit _ hfdig
  cases fracD with
  | nil =>
    have hsplit : splitOnChar '.' intD = [intD] := splitOnChar_no_sep' '.' intD hidot
    cases neg with
    | true =>
      simp only [RawDec.chars, RawDec.value, if_true, if_false, Bool.false_eq_true,
        List.isEmpty_nil, List.isEmpty_cons, List.append_nil]
      unfold parseRat?
      rw [String.toList_ofList]
      simp only [List.cons_append]
      rw [hsplit]
      simp [natFromDigits, hni]
    | false =>
      simp only [RawDec.chars, RawDec.value, if_true, if_false, Bool.false_eq_true,
        List.isEmpty_nil, List.isEmpty_cons, List.append_nil]
      unfold parseRat?
      rw [String.toList_ofList]
      simp only [List.cons_append]
      rw [hsplit]
      simp [natFromDigits, hni]
  | cons g gs =>
    have hsplit : splitOnChar '.' (intD ++ '.' :: g :: gs) = [intD, g :: gs] := by
      rw [splitOnChar_one_sep '.' intD (g :: gs) hidot, splitOnChar_no_sep' '.' (g :: gs) hfdot]
    cases neg with
    | true =>
      simp only [RawDec.chars, RawDec.value, if_true, if_false, Bool.false_eq_true,
        List.isEmpty_nil, List.isEmpty_cons, List.append_nil]
      unfold parseRat?
      rw [String.toList_ofList]
      simp only [List.cons_append]
      rw [hsplit]
      simp only [hni, hnf, if_true, if_false, Bool.false_eq_true]
    | false =>
      simp only [RawDec.chars, RawDec.value, if_true, if_false, Bool.false_eq_true,
        List.isEmpty_nil, List.isEmpty_cons, List.append_nil]
      unfold parseRat?
      rw [String.toList_ofList]
      simp only [List.cons_append]
      rw [hsplit]
      simp only [hni, hnf, if_true, if_false, Bool.false_eq_true]

/-! ## Per-construct round-trips (pure helper functions)

The parser's per-statement analysers are pure functions; we round-trip each
against a canonical printer. (The two `Id.run do` `for`-loop passes of
`parseAptp` itself, which merge box bounds and collect leaves, are not yet
assembled — see the module note.) -/

/-- Printed characters of a variable name `P_n`. -/
def varNameChars (p : Char) (n : Nat) : List Char := p :: '_' :: natToDigits n

/-- `parseVarName` recovers a printed variable name. -/
theorem parseVarName_print (p : Char) (n : Nat) :
    parseVarName (String.ofList (varNameChars p n)) = some (p, n) := by
  unfold parseVarName varNameChars
  rw [String.toList_ofList]
  simp only [natOfDigits_natToDigits, Option.map_some]

/-- A printed input-box constraint `(op X_i <dec>)` parses to the box update. -/
theorem asBoxUpdate_print (op : String) (i : Nat) (d : RawDec) (hd : d.WF) :
    asBoxUpdate op (String.ofList (varNameChars 'X' i)) (String.ofList d.chars)
      = some (i, op == "<=", d.value) := by
  unfold asBoxUpdate
  rw [parseVarName_print, parseRat_RawDec d hd]
  simp

lemma parseVarName_snd_ne (a c0 : Char) (rest : List Char) (h : c0 ≠ '_') :
    parseVarName (String.ofList (a :: c0 :: rest)) = none := by
  unfold parseVarName
  rw [String.toList_ofList]
  split <;> simp_all

/-- A decimal literal is not a variable name (its second char is a digit). -/
theorem parseVarName_dec_none (d : RawDec) (hd : d.WF) :
    parseVarName (String.ofList d.chars) = none := by
  obtain ⟨neg, intD, fracD⟩ := d
  obtain ⟨⟨hine, hidig⟩, _⟩ := hd
  obtain ⟨c0, rest0, hc0eq⟩ : ∃ c0 rest0, intD = c0 :: rest0 := by
    cases h : intD with
    | nil => exact absurd h hine
    | cons a l => exact ⟨a, l, rfl⟩
  have hc0 : c0.isDigit := hidig c0 (hc0eq ▸ List.mem_cons_self ..)
  have hchars : RawDec.chars ⟨neg, intD, fracD⟩
      = (if neg then '-' else '+') :: c0 :: (rest0 ++ (if fracD.isEmpty then [] else '.' :: fracD)) := by
    simp only [RawDec.chars, hc0eq, List.cons_append]
  rw [hchars]
  exact parseVarName_snd_ne _ c0 _ (isDigit_ne_underscore hc0)

/-- A printed objective `(<= Y_i Y_j)` (difference of two output vars). -/
theorem asObjective_print_YY (numOut : Nat) (i j : Nat) :
    asObjective numOut "<=" (String.ofList (varNameChars 'Y' i)) (String.ofList (varNameChars 'Y' j))
      = some { c := ((List.replicate numOut (0:ℚ)).toArray.set! i 1).set! j (-1), rhs := 0 } := by
  unfold asObjective
  simp only [show ("<=" == ">=") = false from by decide, Bool.false_eq_true, if_false]
  rw [parseVarName_print, parseVarName_print]
  rfl

/-- A printed objective `(<= Y_i <dec>)` (single-output upper bound). -/
theorem asObjective_print_Yub (numOut : Nat) (i : Nat) (d : RawDec) (hd : d.WF) :
    asObjective numOut "<=" (String.ofList (varNameChars 'Y' i)) (String.ofList d.chars)
      = some { c := (List.replicate numOut (0:ℚ)).toArray.set! i 1, rhs := d.value } := by
  unfold asObjective
  simp only [show ("<=" == ">=") = false from by decide, Bool.false_eq_true, if_false]
  rw [parseVarName_print, parseVarName_dec_none d hd, parseRat_RawDec d hd]
  simp

/-! ## Leaf-clause round-trip (`mkLeaf` as a fold) -/

/-- The literal `0` split point, as a canonical decimal (`"+0"`). -/
def zeroDec : RawDec := ⟨false, ['0'], []⟩

lemma zeroDec_wf : zeroDec.WF := by
  refine ⟨⟨by simp [zeroDec], ?_⟩, by simp [zeroDec]⟩
  intro c hc; simp only [zeroDec, List.mem_singleton] at hc; subst hc; decide

lemma zeroDec_value : zeroDec.value = 0 := by
  simp [RawDec.value, natFromDigits, zeroDec]

lemma zeroDec_pointList : (String.ofList zeroDec.chars).toList = ['+', '0'] := by
  rw [String.toList_ofList]; decide

lemma parseRat_zero : parseRat? (String.ofList zeroDec.chars) = some 0 := by
  rw [parseRat_RawDec zeroDec zeroDec_wf, zeroDec_value]

/-- Printed clause item for a signed neuron id `k ≠ 0`: `(>= N_k 0)` or `(< N_{|k|} 0)`. -/
def leafItemSexp (k : Int) : Sexp :=
  if 0 < k then
    .list [.atom ">=", .atom (String.ofList (varNameChars 'N' k.toNat)), .atom (String.ofList zeroDec.chars)]
  else
    .list [.atom "<", .atom (String.ofList (varNameChars 'N' (-k).toNat)), .atom (String.ofList zeroDec.chars)]

/-- One `mkLeafStep` on a printed clause item pushes exactly the signed id `k`. -/
lemma mkLeafStep_item (start : Array Int) (k : Int) (hk : k ≠ 0) :
    mkLeafStep (.ok start) (leafItemSexp k) = .ok (start.push k) := by
  rcases lt_trichotomy k 0 with hneg | h0 | hpos
  · have hnk : ¬ (0 < k) := by omega
    have hkk : -(Int.ofNat (-k).toNat) = k := by
      rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]; omega
    simp only [leafItemSexp, hnk, if_false, mkLeafStep, zeroDec_pointList,
      parseVarName_print, parseRat_zero, ne_eq, not_true_eq_false, if_false,
      show ("<" == ">=") = false from by decide, show ("<" == "<") = true from by decide,
      if_true, Bool.false_eq_true, hkk]
    rfl
  · exact absurd h0 hk
  · have hkk : (Int.ofNat k.toNat) = k := by
      rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]
    simp only [leafItemSexp, hpos, if_true, mkLeafStep, zeroDec_pointList,
      parseVarName_print, parseRat_zero, ne_eq, not_true_eq_false, if_false,
      show (">=" == ">=") = true from by decide, if_true, hkk]
    rfl

/-- Folding printed clause items accumulates exactly the signed ids. -/
lemma mkLeaf_foldl (L : List Int) (hL : ∀ k ∈ L, k ≠ 0) (start : Array Int) :
    (L.map leafItemSexp).foldl mkLeafStep (.ok start) = .ok (start ++ L.toArray) := by
  induction L generalizing start with
  | nil => simp
  | cons k ks ih =>
    have hk : k ≠ 0 := hL k (List.mem_cons_self ..)
    have hks : ∀ x ∈ ks, x ≠ 0 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.foldl_cons, mkLeafStep_item start k hk, ih hks (start.push k)]
    congr 1
    apply Array.toList_inj.mp
    simp

/-- Printed `(and …)` clause for a leaf (list of signed neuron ids). -/
def leafClause (L : List Int) : Sexp := .list (.atom "and" :: L.map leafItemSexp)

/-- **Leaf round-trip.** `mkLeaf` recovers a printed leaf clause exactly. -/
theorem mkLeaf_leafClause (L : List Int) (hL : ∀ k ∈ L, k ≠ 0) :
    mkLeaf (leafClause L) = .ok L.toArray := by
  unfold mkLeaf leafClause
  simp only []
  rw [mkLeaf_foldl L hL #[]]
  simp

/-! ## Statement reader round-trip (`readStatementsFold_multi`)

Generalizes `NetRoundtrip.readStatements_single` to many statements: statements
printed one-per-line (each followed by `'\n'`) are read back as exactly that list.
Proved against the fold-based `readStatementsFold` (which `parseAptp` uses). -/

/-- Statements joined with a trailing newline each. -/
def joinNL (lines : List (List Char)) : List Char := lines.flatMap (fun s => s ++ ['\n'])

/-- A clean, balanced, newline-free, nonempty statement line — exactly the shape a
printed S-expression statement has. -/
def CleanBalLine (l : List Char) : Prop :=
  '\n' ∉ l ∧ rtrim (beforeSemicolon (trimC l)) = l ∧ l ≠ [] ∧
  l.countP (· == '(') = l.countP (· == ')')

lemma splitOnChar_joinNL (lines : List (List Char)) (hnl : ∀ l ∈ lines, '\n' ∉ l) :
    splitOnChar '\n' (joinNL lines) = lines ++ [[]] := by
  induction lines with
  | nil => rfl
  | cons s ss ih =>
    have hs : '\n' ∉ s := hnl s (List.mem_cons_self ..)
    have hss : ∀ l ∈ ss, '\n' ∉ l := fun l hl => hnl l (List.mem_cons_of_mem _ hl)
    have hjoin : joinNL (s :: ss) = s ++ '\n' :: joinNL ss := by
      simp [joinNL, List.flatMap_cons]
    rw [hjoin, splitOnChar_one_sep '\n' s (joinNL ss) hs, ih hss]
    rfl

/-- The empty line is a no-op for the statement-reader fold step. -/
lemma readStmtStep_nil (acc : Except String (Int × Array (List Char) × List Char)) :
    readStmtStep acc [] = acc := by
  cases acc with
  | error e => rfl
  | ok st =>
    obtain ⟨bal, stmts, cur⟩ := st
    unfold readStmtStep
    simp [trimC, ltrim, rtrim, beforeSemicolon]

/-- A clean balanced line (with balance already `0`) is pushed as a complete statement. -/
lemma readStmtStep_clean (stmts : Array (List Char)) (l : List Char) (hc : CleanBalLine l) :
    readStmtStep (.ok (0, stmts, [])) l = .ok (0, stmts.push l, []) := by
  obtain ⟨hnl, hclean, hne, hbal⟩ := hc
  have hemp : l.isEmpty = false := by simpa using hne
  have h2 : (l.countP (· == '(') : Int) = (l.countP (· == ')') : Int) := by exact_mod_cast hbal
  unfold readStmtStep
  simp [hclean, hemp, h2]

/-- Folding the reader step over clean balanced lines accumulates them in order. -/
lemma readStmtStep_fold (lines : List (List Char)) (hc : ∀ l ∈ lines, CleanBalLine l) :
    ∀ (stmts : Array (List Char)),
      lines.foldl readStmtStep (.ok (0, stmts, [])) = .ok (0, stmts ++ lines.toArray, []) := by
  induction lines with
  | nil => intro stmts; simp
  | cons l ls ih =>
    intro stmts
    have hl : CleanBalLine l := hc l (List.mem_cons_self ..)
    have hls : ∀ x ∈ ls, CleanBalLine x := fun x hx => hc x (List.mem_cons_of_mem _ hx)
    rw [List.foldl_cons, readStmtStep_clean stmts l hl, ih hls (stmts.push l)]
    have harr : stmts.push l ++ ls.toArray = stmts ++ (l :: ls).toArray := by
      apply Array.toList_inj.mp; simp
    rw [harr]

/-- **Multi-statement reader round-trip.** Content that is a newline-terminated join
of clean balanced statement lines is read back as exactly those statements. -/
theorem readStatementsFold_multi (lines : List (List Char)) (content : String)
    (hc : ∀ l ∈ lines, CleanBalLine l) (hcontent : content.toList = joinNL lines) :
    readStatementsFold content = .ok lines.toArray := by
  have hnl : ∀ l ∈ lines, '\n' ∉ l := fun l hl => (hc l hl).1
  unfold readStatementsFold
  rw [hcontent, splitOnChar_joinNL lines hnl, List.foldl_append,
    readStmtStep_fold lines hc #[], List.foldl_cons, List.foldl_nil, readStmtStep_nil]
  simp


/-! ## Assembly fold lemmas (scan passes as folds over the printed statements) -/

/-- parseAll fold: printed statements parse back to the sexps (short-circuit-free). -/
lemma parseAll_fold (es : List Sexp) (hwf : ∀ e ∈ es, WF e) :
    ∀ (start : Array Sexp),
      (es.map stmtChars).foldl parseAllStep (.ok start) = .ok (start ++ es.toArray) := by
  induction es with
  | nil => intro start; simp
  | cons e es ih =>
    intro start
    have hwfe : WF e := hwf e (List.mem_cons_self ..)
    have hwfes : ∀ x ∈ es, WF x := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.foldl_cons]
    have hstep : parseAllStep (.ok start) (stmtChars e) = .ok (start.push e) := by
      unfold parseAllStep
      rw [parseStatement_stmtChars e hwfe]
    rw [hstep, ih hwfes (start.push e)]
    have : start.push e ++ es.toArray = start ++ (e :: es).toArray := by
      apply Array.toList_inj.mp; simp
    rw [this]

/-- Objective spec: difference of two outputs, or single-output upper bound. -/
inductive RawObj where
  | diff (i j : Nat)
  | ub (i : Nat) (d : RawDec)

def xDeclSexp (i : Nat) : Sexp :=
  .list [.atom "declare-const", .atom (String.ofList (varNameChars 'X' i)), .atom "Real"]
def yDeclSexp (j : Nat) : Sexp :=
  .list [.atom "declare-const", .atom (String.ofList (varNameChars 'Y' j)), .atom "Real"]
def nDeclSexp (k : Nat) : Sexp :=
  .list [.atom "declare-pwl", .atom (String.ofList (varNameChars 'N' k)), .atom "ReLU"]
def boxLoSexp (i : Nat) (d : RawDec) : Sexp :=
  .list [.atom "assert", .list [.atom ">=", .atom (String.ofList (varNameChars 'X' i)), .atom (String.ofList d.chars)]]
def boxHiSexp (i : Nat) (d : RawDec) : Sexp :=
  .list [.atom "assert", .list [.atom "<=", .atom (String.ofList (varNameChars 'X' i)), .atom (String.ofList d.chars)]]
def objSexp : RawObj → Sexp
  | .diff i j => .list [.atom "assert", .list [.atom "<=", .atom (String.ofList (varNameChars 'Y' i)), .atom (String.ofList (varNameChars 'Y' j))]]
  | .ub i d => .list [.atom "assert", .list [.atom "<=", .atom (String.ofList (varNameChars 'Y' i)), .atom (String.ofList d.chars)]]
def orAssertSexp (leaves : List (List Int)) : Sexp :=
  .list [.atom "assert", .list (.atom "or" :: leaves.map leafClause)]

-- scanDeclsStep steps
lemma scanDeclsStep_x (acc : Int × Int × Array Nat) (i : Nat) :
    scanDeclsStep (.ok acc) (xDeclSexp i) = .ok (max acc.1 (Int.ofNat i), acc.2.1, acc.2.2) := by
  obtain ⟨mi, mo, ns⟩ := acc
  unfold scanDeclsStep xDeclSexp
  simp only [List.dropLast_concat]
  rw [show [Sexp.atom (String.ofList (varNameChars 'X' i)), Sexp.atom "Real"].dropLast
        = [Sexp.atom (String.ofList (varNameChars 'X' i))] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, scanConstName, parseVarName_print]

lemma scanDeclsStep_y (acc : Int × Int × Array Nat) (j : Nat) :
    scanDeclsStep (.ok acc) (yDeclSexp j) = .ok (acc.1, max acc.2.1 (Int.ofNat j), acc.2.2) := by
  obtain ⟨mi, mo, ns⟩ := acc
  unfold scanDeclsStep yDeclSexp
  simp only [List.dropLast_concat]
  rw [show [Sexp.atom (String.ofList (varNameChars 'Y' j)), Sexp.atom "Real"].dropLast
        = [Sexp.atom (String.ofList (varNameChars 'Y' j))] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, scanConstName, parseVarName_print]

lemma scanDeclsStep_n (acc : Int × Int × Array Nat) (k : Nat) :
    scanDeclsStep (.ok acc) (nDeclSexp k) = .ok (acc.1, acc.2.1, acc.2.2.push k) := by
  obtain ⟨mi, mo, ns⟩ := acc
  unfold scanDeclsStep nDeclSexp
  simp only [List.dropLast_concat]
  rw [show [Sexp.atom (String.ofList (varNameChars 'N' k)), Sexp.atom "ReLU"].dropLast
        = [Sexp.atom (String.ofList (varNameChars 'N' k))] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, scanPwlName, parseVarName_print]

-- identity lemmas
lemma scanDeclsStep_assert (acc : Int × Int × Array Nat) (body : Sexp) :
    scanDeclsStep (.ok acc) (.list [.atom "assert", body]) = .ok acc := by
  obtain ⟨mi, mo, ns⟩ := acc; rfl

lemma scanAssertsStep_xdecl (numOut : Nat) (acc : AssertState) (i : Nat) :
    scanAssertsStep numOut (.ok acc) (xDeclSexp i) = .ok acc := by
  obtain ⟨lo, hi, objs, leaves⟩ := acc; rfl

lemma scanAssertsStep_ydecl (numOut : Nat) (acc : AssertState) (j : Nat) :
    scanAssertsStep numOut (.ok acc) (yDeclSexp j) = .ok acc := by
  obtain ⟨lo, hi, objs, leaves⟩ := acc; rfl

lemma scanAssertsStep_ndecl (numOut : Nat) (acc : AssertState) (k : Nat) :
    scanAssertsStep numOut (.ok acc) (nDeclSexp k) = .ok acc := by
  obtain ⟨lo, hi, objs, leaves⟩ := acc; rfl

lemma scanAssertsStep_boxLo (numOut : Nat) (lo hi : Array (Option ℚ)) (objs : Array Objective)
    (leaves : Array (Array Int)) (i : Nat) (d : RawDec) (hd : d.WF) (hnone : lo[i]! = none) :
    scanAssertsStep numOut (.ok (lo, hi, objs, leaves)) (boxLoSexp i d)
      = .ok (lo.set! i (some d.value), hi, objs, leaves) := by
  unfold scanAssertsStep boxLoSexp
  simp only [asBoxUpdate_print ">=" i d hd, show (">=" == "<=") = false from by decide,
    Bool.false_eq_true, if_false, hnone]

lemma scanAssertsStep_boxHi (numOut : Nat) (lo hi : Array (Option ℚ)) (objs : Array Objective)
    (leaves : Array (Array Int)) (i : Nat) (d : RawDec) (hd : d.WF) (hnone : hi[i]! = none) :
    scanAssertsStep numOut (.ok (lo, hi, objs, leaves)) (boxHiSexp i d)
      = .ok (lo, hi.set! i (some d.value), objs, leaves) := by
  unfold scanAssertsStep boxHiSexp
  simp only [asBoxUpdate_print "<=" i d hd, show ("<=" == "<=") = true from by decide,
    if_true, hnone]

lemma scanAssertsStep_objDiff (numOut : Nat) (lo hi : Array (Option ℚ)) (objs : Array Objective)
    (leaves : Array (Array Int)) (i j : Nat) :
    scanAssertsStep numOut (.ok (lo, hi, objs, leaves)) (objSexp (.diff i j))
      = .ok (lo, hi, objs.push { c := ((List.replicate numOut (0:ℚ)).toArray.set! i 1).set! j (-1), rhs := 0 }, leaves) := by
  unfold scanAssertsStep objSexp
  have hbox : asBoxUpdate "<=" (String.ofList (varNameChars 'Y' i)) (String.ofList (varNameChars 'Y' j)) = none := by
    unfold asBoxUpdate; rw [parseVarName_print]; rfl
  simp only [hbox, asObjective_print_YY]

lemma scanAssertsStep_objUb (numOut : Nat) (lo hi : Array (Option ℚ)) (objs : Array Objective)
    (leaves : Array (Array Int)) (i : Nat) (d : RawDec) (hd : d.WF) :
    scanAssertsStep numOut (.ok (lo, hi, objs, leaves)) (objSexp (.ub i d))
      = .ok (lo, hi, objs.push { c := (List.replicate numOut (0:ℚ)).toArray.set! i 1, rhs := d.value }, leaves) := by
  unfold scanAssertsStep objSexp
  have hbox : asBoxUpdate "<=" (String.ofList (varNameChars 'Y' i)) (String.ofList d.chars) = none := by
    unfold asBoxUpdate; rw [parseVarName_print]; rfl
  simp only [hbox, asObjective_print_Yub _ _ d hd]

-- Array set!/get! helpers
lemma get!_set!_ne (a : Array (Option ℚ)) (i j : Nat) (v : Option ℚ) (hij : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [Array.set!, Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  simp [Array.getElem?_setIfInBounds, hij]

lemma get!_set!_self (a : Array (Option ℚ)) (i : Nat) (v : Option ℚ) (hi : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [Array.set!, Array.getElem!_eq_getD]
  simp [Array.getElem?_setIfInBounds, hi]

lemma set!_size (a : Array (Option ℚ)) (i : Nat) (v : Option ℚ) : (a.set! i v).size = a.size := by
  simp

/-- Folding sets over indices not equal to `j` leaves index `j` untouched. -/
lemma foldl_set_get_ne (is : List Nat) (a : Array (Option ℚ)) (g : Nat → Option ℚ) (j : Nat)
    (hj : j ∉ is) : (is.foldl (fun a i => a.set! i (g i)) a)[j]! = a[j]! := by
  induction is generalizing a with
  | nil => rfl
  | cons i is' ih =>
    have hne : i ≠ j := by simp only [List.mem_cons, not_or] at hj; exact Ne.symm hj.1
    have hj' : j ∉ is' := by simp only [List.mem_cons, not_or] at hj; exact hj.2
    rw [List.foldl_cons, ih (a.set! i (g i)) hj', get!_set!_ne a i j (g i) hne]

/-- Folding sets over a nodup index list writes each index to its value. -/
lemma foldl_set_get (is : List Nat) (a : Array (Option ℚ)) (g : Nat → Option ℚ) (j : Nat)
    (hj : j ∈ is) (hnd : is.Nodup) (hbound : ∀ i ∈ is, i < a.size) :
    (is.foldl (fun a i => a.set! i (g i)) a)[j]! = g j := by
  induction is generalizing a with
  | nil => simp at hj
  | cons i is' ih =>
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hj with rfl | hj'
    · -- j = i (head)
      rw [foldl_set_get_ne is' (a.set! j (g j)) g j hnd.1]
      exact get!_set!_self a j (g j) (hbound j (List.mem_cons_self ..))
    · -- j ∈ is'
      have hbound' : ∀ x ∈ is', x < (a.set! i (g i)).size := by
        intro x hx; rw [set!_size]; exact hbound x (List.mem_cons_of_mem _ hx)
      exact ih (a.set! i (g i)) hj' hnd.2 hbound'

lemma boxLo_scan (numOut : Nat) (is : List Nat) (dof : Nat → RawDec)
    (hwf : ∀ i ∈ is, (dof i).WF) (hnd : is.Nodup) (hi : Array (Option ℚ))
    (objs : Array Objective) (leaves : Array (Array Int)) :
    ∀ (lo : Array (Option ℚ)), (∀ i ∈ is, i < lo.size) → (∀ i ∈ is, lo[i]! = none) →
    (is.map (fun i => boxLoSexp i (dof i))).foldl (scanAssertsStep numOut) (.ok (lo, hi, objs, leaves))
      = .ok (is.foldl (fun a i => a.set! i (some (dof i).value)) lo, hi, objs, leaves) := by
  induction is with
  | nil => intro lo _ _; simp
  | cons i is' ih =>
    intro lo hbound hnone
    rw [List.nodup_cons] at hnd
    have hwfi : (dof i).WF := hwf i (List.mem_cons_self ..)
    have hnonei : lo[i]! = none := hnone i (List.mem_cons_self ..)
    rw [List.map_cons, List.foldl_cons,
      scanAssertsStep_boxLo numOut lo hi objs leaves i (dof i) hwfi hnonei, List.foldl_cons]
    apply ih (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) hnd.2 (lo.set! i (some (dof i).value))
    · intro x hx; rw [set!_size]; exact hbound x (List.mem_cons_of_mem _ hx)
    · intro x hx
      have hxi : i ≠ x := fun h => hnd.1 (h ▸ hx)
      rw [get!_set!_ne lo i x _ hxi]; exact hnone x (List.mem_cons_of_mem _ hx)

lemma boxHi_scan (numOut : Nat) (is : List Nat) (dof : Nat → RawDec)
    (hwf : ∀ i ∈ is, (dof i).WF) (hnd : is.Nodup) (lo : Array (Option ℚ))
    (objs : Array Objective) (leaves : Array (Array Int)) :
    ∀ (hi : Array (Option ℚ)), (∀ i ∈ is, i < hi.size) → (∀ i ∈ is, hi[i]! = none) →
    (is.map (fun i => boxHiSexp i (dof i))).foldl (scanAssertsStep numOut) (.ok (lo, hi, objs, leaves))
      = .ok (lo, is.foldl (fun a i => a.set! i (some (dof i).value)) hi, objs, leaves) := by
  induction is with
  | nil => intro hi _ _; simp
  | cons i is' ih =>
    intro hi hbound hnone
    rw [List.nodup_cons] at hnd
    have hwfi : (dof i).WF := hwf i (List.mem_cons_self ..)
    have hnonei : hi[i]! = none := hnone i (List.mem_cons_self ..)
    rw [List.map_cons, List.foldl_cons,
      scanAssertsStep_boxHi numOut lo hi objs leaves i (dof i) hwfi hnonei, List.foldl_cons]
    apply ih (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) hnd.2 (hi.set! i (some (dof i).value))
    · intro x hx; rw [set!_size]; exact hbound x (List.mem_cons_of_mem _ hx)
    · intro x hx
      have hxi : i ≠ x := fun h => hnd.1 (h ▸ hx)
      rw [get!_set!_ne hi i x _ hxi]; exact hnone x (List.mem_cons_of_mem _ hx)

lemma push_append_toArray {α} (a : Array α) (x : α) (l : List α) :
    a.push x ++ l.toArray = a ++ (x :: l).toArray := by
  apply Array.toList_inj.mp; simp

def decodeObj (numOut : Nat) : RawObj → Objective
  | .diff i j => { c := ((List.replicate numOut (0:ℚ)).toArray.set! i 1).set! j (-1), rhs := 0 }
  | .ub i d => { c := (List.replicate numOut (0:ℚ)).toArray.set! i 1, rhs := d.value }
def WFObj : RawObj → Prop
  | .diff _ _ => True
  | .ub _ d => d.WF

lemma objs_scan (numOut : Nat) (os : List RawObj) (hwf : ∀ o ∈ os, WFObj o)
    (lo hi : Array (Option ℚ)) (leaves : Array (Array Int)) :
    ∀ (objsAcc : Array Objective),
    (os.map objSexp).foldl (scanAssertsStep numOut) (.ok (lo, hi, objsAcc, leaves))
      = .ok (lo, hi, objsAcc ++ (os.map (decodeObj numOut)).toArray, leaves) := by
  induction os with
  | nil => intro objsAcc; simp
  | cons o os ih =>
    intro objsAcc
    have hwfo : WFObj o := hwf o (List.mem_cons_self ..)
    have hwfos : ∀ x ∈ os, WFObj x := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.foldl_cons]
    cases o with
    | diff i j =>
      rw [scanAssertsStep_objDiff numOut lo hi objsAcc leaves i j, ih hwfos]
      simp only [List.map_cons, decodeObj, push_append_toArray]
    | ub i d =>
      rw [scanAssertsStep_objUb numOut lo hi objsAcc leaves i d hwfo, ih hwfos]
      simp only [List.map_cons, decodeObj, push_append_toArray]

lemma clause_scan (ls : List (List Int)) (hwf : ∀ L ∈ ls, L ≠ [] ∧ ∀ k ∈ L, k ≠ 0) :
    ∀ (leavesAcc : Array (Array Int)),
    (ls.map leafClause).foldl scanClauseStep (.ok leavesAcc)
      = .ok (leavesAcc ++ (ls.map List.toArray).toArray) := by
  induction ls with
  | nil => intro leavesAcc; simp
  | cons L ls ih =>
    intro leavesAcc
    obtain ⟨hLne, hLnz⟩ := hwf L (List.mem_cons_self ..)
    have hwfs : ∀ x ∈ ls, x ≠ [] ∧ ∀ k ∈ x, k ≠ 0 := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.foldl_cons]
    have hstep : scanClauseStep (.ok leavesAcc) (leafClause L) = .ok (leavesAcc.push L.toArray) := by
      unfold scanClauseStep
      rw [mkLeaf_leafClause L hLnz]
      simp only []
      rw [if_neg (by simp [hLne])]
    rw [hstep, ih hwfs]
    congr 1; apply Array.toList_inj.mp; simp

/-- Reducing `scanAssertsStep` on an `(assert (or …))` whose first clause is a list. -/
lemma scanAssertsStep_or_of_listhead (numOut : Nat) (lo hi : Array (Option ℚ))
    (objs : Array Objective) (leaves : Array (Array Int)) (ch : List Sexp) (ct : List Sexp) :
    scanAssertsStep numOut (.ok (lo, hi, objs, leaves))
        (.list [.atom "assert", .list (.atom "or" :: (Sexp.list ch) :: ct)])
      = (match (Sexp.list ch :: ct).foldl scanClauseStep (.ok leaves) with
         | .error er => .error er | .ok l' => .ok (lo, hi, objs, l')) := rfl

lemma scanAssertsStep_orAssert (numOut : Nat) (lo hi : Array (Option ℚ)) (objs : Array Objective)
    (leaves : Array (Array Int)) (ls : List (List Int)) (hne : ls ≠ [])
    (hwf : ∀ L ∈ ls, L ≠ [] ∧ ∀ k ∈ L, k ≠ 0) :
    scanAssertsStep numOut (.ok (lo, hi, objs, leaves)) (orAssertSexp ls)
      = .ok (lo, hi, objs, leaves ++ (ls.map List.toArray).toArray) := by
  obtain ⟨c0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hbody : orAssertSexp (c0 :: rest)
      = .list [.atom "assert", .list (.atom "or" ::
          Sexp.list (.atom "and" :: c0.map leafItemSexp) :: rest.map leafClause)] := by
    simp [orAssertSexp, leafClause, List.map_cons]
  rw [hbody, scanAssertsStep_or_of_listhead numOut lo hi objs leaves
        (.atom "and" :: c0.map leafItemSexp) (rest.map leafClause),
      show (Sexp.list (.atom "and" :: c0.map leafItemSexp) :: rest.map leafClause)
          = (c0 :: rest).map leafClause from by simp [leafClause, List.map_cons],
      clause_scan (c0 :: rest) hwf leaves]

lemma finalizeBox_list (lo hi : Array (Option ℚ)) (fl fh : Nat → ℚ) (is : List Nat)
    (h : ∀ i ∈ is, lo[i]! = some (fl i) ∧ hi[i]! = some (fh i)) :
    ∀ (start : Array (ℚ × ℚ)),
    is.foldl (finalizeBoxStep lo hi) (.ok start) = .ok (start ++ (is.map (fun i => (fl i, fh i))).toArray) := by
  induction is with
  | nil => intro start; simp
  | cons i is' ih =>
    intro start
    obtain ⟨hloi, hhii⟩ := h i (List.mem_cons_self ..)
    have hstep : finalizeBoxStep lo hi (.ok start) i = .ok (start.push (fl i, fh i)) := by
      unfold finalizeBoxStep
      rw [hloi, hhii]
    rw [List.foldl_cons, hstep, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    congr 1; apply Array.toList_inj.mp; simp

/-- Fold identity: `scanDeclsStep` is a no-op on `assert` statements. -/
lemma scanDecls_assertsIdent (es : List Sexp) (h : ∀ e ∈ es, ∃ body, e = .list [.atom "assert", body])
    (acc : Int × Int × Array Nat) : es.foldl scanDeclsStep (.ok acc) = .ok acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨body, rfl⟩ := h e (List.mem_cons_self ..)
    rw [List.foldl_cons, scanDeclsStep_assert acc body,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) acc]

lemma nDecls_fold (ns : List Nat) (mi mo : Int) :
    ∀ (nsAcc : Array Nat),
      (ns.map nDeclSexp).foldl scanDeclsStep (.ok (mi, mo, nsAcc)) = .ok (mi, mo, nsAcc ++ ns.toArray) := by
  induction ns with
  | nil => intro nsAcc; simp
  | cons k ks ih =>
    intro nsAcc
    rw [List.map_cons, List.foldl_cons, scanDeclsStep_n (mi, mo, nsAcc) k, ih (nsAcc.push k),
      push_append_toArray]

/-! ## Printed-statement well-formedness and cleanliness

The end-to-end assembly needs each printed statement S-expression to be `WF`
(all atoms `GoodStr`), and its printed character form to be a `CleanBalLine`
(newline-free, trim/comment-invariant, nonempty, balanced parens) so the
statement reader (`readStatementsFold_multi`) reads it back as one statement. -/

/-- A digit character is usable inside an atom and is not `;`. -/
lemma digit_good {c : Char} (h : c.isDigit = true) : IsTokChar c ∧ c ≠ ';' := by
  have hb : ('0' ≤ c) ∧ (c ≤ '9') := by
    unfold Char.isDigit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  obtain ⟨h0, h9⟩ := hb
  have hlp : c ≠ '(' := (lt_of_lt_of_le (by decide) h0).ne'
  have hrp : c ≠ ')' := (lt_of_lt_of_le (by decide) h0).ne'
  have hsp : c ≠ ' ' := (lt_of_lt_of_le (by decide) h0).ne'
  have htab : c ≠ '\t' := (lt_of_lt_of_le (by decide) h0).ne'
  have hcr : c ≠ '\r' := (lt_of_lt_of_le (by decide) h0).ne'
  have hnl : c ≠ '\n' := (lt_of_lt_of_le (by decide) h0).ne'
  have hsemi : c ≠ ';' := (lt_of_le_of_lt h9 (by decide)).ne
  refine ⟨⟨?_, ?_⟩, hsemi⟩
  · rw [Bool.or_eq_false_iff]
    exact ⟨by simpa using hlp, by simpa using hrp⟩
  · unfold Char.isWhitespace
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨⟨⟨hsp, htab⟩, hcr⟩, hnl⟩

/-- A printed variable name `P_n` (with `P` a good char) is a `GoodStr`. -/
lemma varNameChars_good (p : Char) (n : Nat) (hp : IsTokChar p ∧ p ≠ ';') :
    GoodStr (varNameChars p n) := by
  refine ⟨by simp [varNameChars], ?_⟩
  intro c hc
  simp only [varNameChars, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · exact hp
  · exact ⟨⟨by decide, by decide⟩, by decide⟩
  · exact natToDigits_good n c hc

/-- A well-formed raw decimal prints to a `GoodStr`. -/
lemma rawDec_chars_good (d : RawDec) (hd : d.WF) : GoodStr (RawDec.chars d) := by
  obtain ⟨⟨hine, hidig⟩, hfdig⟩ := hd
  refine ⟨by simp [RawDec.chars], ?_⟩
  intro c hc
  simp only [RawDec.chars, List.mem_append, List.mem_cons] at hc
  rcases hc with (rfl | hc) | hc
  · split_ifs <;> exact ⟨⟨by decide, by decide⟩, by decide⟩
  · exact digit_good (hidig c hc)
  · by_cases hfe : d.fracDigits.isEmpty
    · simp only [hfe, if_true, List.not_mem_nil] at hc
    · simp only [hfe, Bool.false_eq_true, if_false, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨⟨by decide, by decide⟩, by decide⟩
      · exact digit_good (hfdig c hc)

-- Fixed-atom goodness (each char checked individually).
lemma good_declConst : GoodStr "declare-const".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_declPwl : GoodStr "declare-pwl".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_Real : GoodStr "Real".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_assert : GoodStr "assert".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_ge : GoodStr ">=".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_le : GoodStr "<=".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_lt : GoodStr "<".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc; exact ⟨by decide, by decide, by decide⟩
lemma good_or : GoodStr "or".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_and : GoodStr "and".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩

lemma wf_atom_lit {s : String} (h : GoodStr s.toList) : WF (.atom s) := WF.atom s h
lemma wf_atom_ofList (l : List Char) (h : GoodStr l) : WF (.atom (String.ofList l)) := by
  apply WF.atom; rw [String.toList_ofList]; exact h

lemma WF_xDeclSexp (i : Nat) : WF (xDeclSexp i) := by
  apply WF.list; intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact wf_atom_lit good_declConst
  · exact wf_atom_ofList _ (varNameChars_good 'X' i ⟨⟨by decide, by decide⟩, by decide⟩)
  · exact wf_atom_lit good_Real

lemma WF_yDeclSexp (j : Nat) : WF (yDeclSexp j) := by
  apply WF.list; intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact wf_atom_lit good_declConst
  · exact wf_atom_ofList _ (varNameChars_good 'Y' j ⟨⟨by decide, by decide⟩, by decide⟩)
  · exact wf_atom_lit good_Real

lemma WF_nDeclSexp (k : Nat) : WF (nDeclSexp k) := by
  apply WF.list; intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact wf_atom_lit good_declPwl
  · exact wf_atom_ofList _ (varNameChars_good 'N' k ⟨⟨by decide, by decide⟩, by decide⟩)
  · exact wf_atom_lit good_ReLU

lemma WF_boxLoSexp (i : Nat) (d : RawDec) (hd : d.WF) : WF (boxLoSexp i d) := by
  apply WF.list; intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact wf_atom_lit good_assert
  · apply WF.list; intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl
    · exact wf_atom_lit good_ge
    · exact wf_atom_ofList _ (varNameChars_good 'X' i ⟨⟨by decide, by decide⟩, by decide⟩)
    · exact wf_atom_ofList _ (rawDec_chars_good d hd)

lemma WF_boxHiSexp (i : Nat) (d : RawDec) (hd : d.WF) : WF (boxHiSexp i d) := by
  apply WF.list; intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact wf_atom_lit good_assert
  · apply WF.list; intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl
    · exact wf_atom_lit good_le
    · exact wf_atom_ofList _ (varNameChars_good 'X' i ⟨⟨by decide, by decide⟩, by decide⟩)
    · exact wf_atom_ofList _ (rawDec_chars_good d hd)

lemma WF_objSexp (o : RawObj) (hwf : WFObj o) : WF (objSexp o) := by
  cases o with
  | diff i j =>
    apply WF.list; intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact wf_atom_lit good_assert
    · apply WF.list; intro e' he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · exact wf_atom_lit good_le
      · exact wf_atom_ofList _ (varNameChars_good 'Y' i ⟨⟨by decide, by decide⟩, by decide⟩)
      · exact wf_atom_ofList _ (varNameChars_good 'Y' j ⟨⟨by decide, by decide⟩, by decide⟩)
  | ub i d =>
    apply WF.list; intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact wf_atom_lit good_assert
    · apply WF.list; intro e' he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · exact wf_atom_lit good_le
      · exact wf_atom_ofList _ (varNameChars_good 'Y' i ⟨⟨by decide, by decide⟩, by decide⟩)
      · exact wf_atom_ofList _ (rawDec_chars_good d hwf)

lemma WF_leafItemSexp (k : Int) : WF (leafItemSexp k) := by
  have hz : WF (Sexp.atom (String.ofList zeroDec.chars)) :=
    wf_atom_ofList _ (rawDec_chars_good zeroDec zeroDec_wf)
  unfold leafItemSexp
  split
  · apply WF.list; intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact wf_atom_lit good_ge
    · exact wf_atom_ofList _ (varNameChars_good 'N' k.toNat ⟨⟨by decide, by decide⟩, by decide⟩)
    · exact hz
  · apply WF.list; intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact wf_atom_lit good_lt
    · exact wf_atom_ofList _ (varNameChars_good 'N' (-k).toNat ⟨⟨by decide, by decide⟩, by decide⟩)
    · exact hz

lemma WF_leafClause (L : List Int) : WF (leafClause L) := by
  apply WF.list; intro e he
  simp only [List.mem_cons] at he
  rcases he with rfl | he
  · exact wf_atom_lit good_and
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
    exact WF_leafItemSexp k

lemma WF_orAssertSexp (leaves : List (List Int)) : WF (orAssertSexp leaves) := by
  apply WF.list; intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact wf_atom_lit good_assert
  · apply WF.list; intro e' he'
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact wf_atom_lit good_or
    · obtain ⟨L, _, rfl⟩ := List.mem_map.mp he'
      exact WF_leafClause L

/-- A printed token char-list: a paren, or a good atom. -/
def PTok (t : List Char) : Prop := t = ['('] ∨ t = [')'] ∨ GoodStr t

lemma ptok_props {t : List Char} (h : PTok t) :
    t ≠ [] ∧ ∀ c ∈ t, c ≠ ';' ∧ c ≠ '\n' ∧ c.isWhitespace = false := by
  rcases h with rfl | rfl | hg
  · refine ⟨by simp, ?_⟩; intro c hc; simp only [List.mem_singleton] at hc; subst hc
    exact ⟨by decide, by decide, by decide⟩
  · refine ⟨by simp, ?_⟩; intro c hc; simp only [List.mem_singleton] at hc; subst hc
    exact ⟨by decide, by decide, by decide⟩
  · obtain ⟨hne, hchars⟩ := hg
    refine ⟨hne, ?_⟩; intro c hc
    obtain ⟨htc, hsemi⟩ := hchars c hc
    exact ⟨hsemi, isTokChar_ne_newline htc, htc.2⟩

mutual
/-- Every printed char-list token of a `WF` S-expression is a `PTok`. -/
lemma sexpToks_ptok (e : Sexp) (hwf : WF e) : ∀ t ∈ (sexpToks e).map String.toList, PTok t := by
  match e, hwf with
  | .atom s, .atom _ hg =>
    intro t ht
    simp only [sexpToks, List.map_cons, List.map_nil, List.mem_singleton] at ht
    subst ht; exact Or.inr (Or.inr hg)
  | .list xs, .list _ hxs =>
    intro t ht
    simp only [sexpToks, List.map_cons, List.map_append, List.map_nil, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | rfl
    · exact Or.inl (by decide)
    · exact sexpListToks_ptok xs hxs t ht
    · exact Or.inr (Or.inl (by decide))
lemma sexpListToks_ptok (es : List Sexp) (hwf : ∀ e ∈ es, WF e) :
    ∀ t ∈ (sexpListToks es).map String.toList, PTok t := by
  match es, hwf with
  | [], _ => intro t ht; simp [sexpListToks] at ht
  | e :: es', hwf =>
    intro t ht
    simp only [sexpListToks, List.map_append, List.mem_append] at ht
    rcases ht with ht | ht
    · exact sexpToks_ptok e (hwf e (List.mem_cons_self ..)) t ht
    · exact sexpListToks_ptok es' (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) t ht
end

/-- Char count over `jn` sums per-token counts (`' '` separators are ignored). -/
lemma countP_jn (p : Char → Bool) (hp : p ' ' = false) :
    ∀ (ss : List (List Char)), (jn ss).countP p = (ss.map (fun t => t.countP p)).sum := by
  intro ss
  induction ss with
  | nil => simp [jn]
  | cons s ss ih =>
    have hjn : jn (s :: ss) = ' ' :: (s ++ jn ss) := by simp [jn]
    rw [hjn, List.countP_cons, List.countP_append, ih, hp]
    simp [List.map_cons]

/-- Char count over `joinSp` sums per-token counts (`' '` separators are ignored). -/
lemma countP_joinSp (p : Char → Bool) (hp : p ' ' = false) :
    ∀ (ss : List (List Char)), (joinSp ss).countP p = (ss.map (fun t => t.countP p)).sum := by
  intro ss
  cases ss with
  | nil => simp [joinSp]
  | cons s ss =>
    simp only [joinSp, List.countP_append, countP_jn p hp, List.map_cons, List.sum_cons]

mutual
/-- Printed S-expression tokens have balanced `(`/`)` char counts. -/
lemma sexpToks_balSum (e : Sexp) (hwf : WF e) :
    ((sexpToks e).map (fun t => t.toList.countP (· == '('))).sum
      = ((sexpToks e).map (fun t => t.toList.countP (· == ')'))).sum := by
  match e, hwf with
  | .atom s, .atom _ hg =>
    have hlp : s.toList.countP (· == '(') = 0 := List.countP_eq_zero.mpr (fun c hc => by
      have := (isTokChar_notParen (hg.2 c hc).1).1; simpa using this)
    have hrp : s.toList.countP (· == ')') = 0 := List.countP_eq_zero.mpr (fun c hc => by
      have := (isTokChar_notParen (hg.2 c hc).1).2; simpa using this)
    simp [sexpToks, hlp, hrp]
  | .list xs, .list _ hxs =>
    simp only [sexpToks, List.map_cons, List.map_append, List.map_nil, List.sum_cons,
      List.sum_append, List.sum_nil, add_zero]
    have e1 : "(".toList.countP (· == '(') = 1 := by decide
    have e2 : ")".toList.countP (· == '(') = 0 := by decide
    have e3 : "(".toList.countP (· == ')') = 0 := by decide
    have e4 : ")".toList.countP (· == ')') = 1 := by decide
    rw [e1, e2, e3, e4, sexpListToks_balSum xs hxs]; omega
lemma sexpListToks_balSum (es : List Sexp) (hwf : ∀ e ∈ es, WF e) :
    ((sexpListToks es).map (fun t => t.toList.countP (· == '('))).sum
      = ((sexpListToks es).map (fun t => t.toList.countP (· == ')'))).sum := by
  match es, hwf with
  | [], _ => simp [sexpListToks]
  | e :: es', hwf =>
    simp only [sexpListToks, List.map_append, List.sum_append]
    rw [sexpToks_balSum e (hwf e (List.mem_cons_self ..)),
      sexpListToks_balSum es' (fun x hx => hwf x (List.mem_cons_of_mem _ hx))]
end

/-- The printed form of a `WF` statement has balanced parentheses. -/
lemma stmtChars_balanced (e : Sexp) (hwf : WF e) :
    (stmtChars e).countP (· == '(') = (stmtChars e).countP (· == ')') := by
  unfold stmtChars
  rw [countP_joinSp (· == '(') (by decide), countP_joinSp (· == ')') (by decide),
    List.map_map, List.map_map]
  exact sexpToks_balSum e hwf

lemma ltrim_joinSp_headNW (c : Char) (cs : List Char) (ms : List (List Char))
    (hcw : c.isWhitespace = false) :
    ltrim (joinSp ((c :: cs) :: ms)) = joinSp ((c :: cs) :: ms) := by
  simp only [joinSp, List.cons_append]
  exact ltrim_cons_nonWs c (cs ++ jn ms) hcw

lemma ltrim_joinSp_ptok (M : List (List Char)) (hne : M ≠ []) (h : ∀ t ∈ M, PTok t) :
    ltrim (joinSp M) = joinSp M := by
  obtain ⟨m, ms, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hmne, hmchars⟩ := ptok_props (h m (List.mem_cons_self ..))
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hmne
  exact ltrim_joinSp_headNW c cs ms (hmchars c (List.mem_cons_self ..)).2.2

lemma rtrim_joinSp_snoc (front : List (List Char)) (t' : List Char) (d : Char)
    (hd : d.isWhitespace = false) :
    rtrim (joinSp (front ++ [t' ++ [d]])) = joinSp (front ++ [t' ++ [d]]) := by
  cases front with
  | nil =>
    simp only [List.nil_append, joinSp, jn, List.append_nil]
    exact rtrim_append_nonWs t' d hd
  | cons s xs =>
    rw [joinSp_append_singleton]
    rw [show joinSp (s :: xs) ++ ' ' :: (t' ++ [d]) = (joinSp (s :: xs) ++ ' ' :: t') ++ [d] from by
      simp [List.append_assoc]]
    exact rtrim_append_nonWs _ d hd

lemma ptok_last (t : List Char) (h : PTok t) : ∃ t' d, t = t' ++ [d] ∧ d.isWhitespace = false := by
  obtain ⟨hne, hchars⟩ := ptok_props h
  rcases List.eq_nil_or_concat t with h0 | ⟨t', d, hcc⟩
  · exact absurd h0 hne
  · rw [List.concat_eq_append] at hcc; subst hcc
    exact ⟨t', d, rfl, (hchars d (by simp)).2.2⟩

lemma rtrim_joinSp_ptok (M : List (List Char)) (hne : M ≠ []) (h : ∀ t ∈ M, PTok t) :
    rtrim (joinSp M) = joinSp M := by
  rcases List.eq_nil_or_concat M with h0 | ⟨front, t, hcc⟩
  · exact absurd h0 hne
  · rw [List.concat_eq_append] at hcc; subst hcc
    obtain ⟨t', d, htd, hd⟩ := ptok_last t (h t (by simp))
    rw [htd]; exact rtrim_joinSp_snoc front t' d hd

lemma stmtChars_ne_nil (e : Sexp) (hwf : WF e) : stmtChars e ≠ [] := by
  unfold stmtChars
  have hne : (sexpToks e).map String.toList ≠ [] := by cases e <;> simp [sexpToks]
  obtain ⟨m, ms, hM⟩ := List.exists_cons_of_ne_nil hne
  rw [hM]
  have hmp : PTok m := sexpToks_ptok e hwf m (by rw [hM]; exact List.mem_cons_self ..)
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil (ptok_props hmp).1
  simp [joinSp]

/-- **Printed statement is a clean, balanced line.** The character form of any
`WF` S-expression is exactly the shape `readStatementsFold_multi` expects. -/
theorem stmtChars_cleanBal (e : Sexp) (hwf : WF e) : CleanBalLine (stmtChars e) := by
  have hM : (sexpToks e).map String.toList ≠ [] := by cases e <;> simp [sexpToks]
  have hp : ∀ t ∈ (sexpToks e).map String.toList, PTok t := sexpToks_ptok e hwf
  have hnl : ∀ c ∈ stmtChars e, c ≠ '\n' := by
    intro c hc
    rcases mem_joinSp (by rw [← stmtChars]; exact hc) with rfl | ⟨s, hs, hcs⟩
    · decide
    · exact ((ptok_props (hp s hs)).2 c hcs).2.1
  have hsemi : ∀ c ∈ stmtChars e, c ≠ ';' := by
    intro c hc
    rcases mem_joinSp (by rw [← stmtChars]; exact hc) with rfl | ⟨s, hs, hcs⟩
    · decide
    · exact ((ptok_props (hp s hs)).2 c hcs).1
  have hlt : ltrim (stmtChars e) = stmtChars e := ltrim_joinSp_ptok _ hM hp
  have hrt : rtrim (stmtChars e) = stmtChars e := rtrim_joinSp_ptok _ hM hp
  have hbs : beforeSemicolon (stmtChars e) = stmtChars e := beforeSemicolon_eq_self _ hsemi
  refine ⟨fun h => (hnl '\n' h) rfl, ?_, stmtChars_ne_nil e hwf, stmtChars_balanced e hwf⟩
  calc rtrim (beforeSemicolon (trimC (stmtChars e)))
      = rtrim (beforeSemicolon (rtrim (ltrim (stmtChars e)))) := by rw [trimC]
    _ = rtrim (beforeSemicolon (stmtChars e)) := by rw [hlt, hrt]
    _ = rtrim (stmtChars e) := by rw [hbs]
    _ = stmtChars e := hrt

/-! ## Scan-pass folds over the printed statement list

The two scan passes of `parseAptp` fold over *all* printed statements. On each
pass, statements of the "wrong" kind are no-ops (`scanDeclsStep` skips asserts;
`scanAssertsStep` skips declares), so the passes decompose along the statement
segments via `List.foldl_append`. -/

/-- Folding the max over `range n` from `-1` gives `n - 1` (as an `Int`). -/
lemma foldl_max_range (n : Nat) :
    (List.range n).foldl (fun (m : Int) i => max m (Int.ofNat i)) (-1) = (n : Int) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    have hn : (Int.ofNat n : Int) = (n : Int) := rfl
    rw [hn, max_eq_right (by omega)]
    push_cast; omega

/-- Declares pass over the printed `X_i` declarations: accumulates `max`. -/
lemma xDecls_fold (is : List Nat) (mo : Int) (ns : Array Nat) :
    ∀ (start : Int),
      (is.map xDeclSexp).foldl scanDeclsStep (.ok (start, mo, ns))
        = .ok (is.foldl (fun (m : Int) i => max m (Int.ofNat i)) start, mo, ns) := by
  induction is with
  | nil => intro start; simp
  | cons i is ih =>
    intro start
    rw [List.map_cons, List.foldl_cons, scanDeclsStep_x (start, mo, ns) i]
    exact ih (max start (Int.ofNat i))

/-- Declares pass over the printed `Y_j` declarations: accumulates `max`. -/
lemma yDecls_fold (is : List Nat) (mi : Int) (ns : Array Nat) :
    ∀ (start : Int),
      (is.map yDeclSexp).foldl scanDeclsStep (.ok (mi, start, ns))
        = .ok (mi, is.foldl (fun (m : Int) i => max m (Int.ofNat i)) start, ns) := by
  induction is with
  | nil => intro start; simp
  | cons i is ih =>
    intro start
    rw [List.map_cons, List.foldl_cons, scanDeclsStep_y (mi, start, ns) i]
    exact ih (max start (Int.ofNat i))

/-- The asserts pass skips `X_i` declarations. -/
lemma scanAsserts_xdeclFold (numOut : Nat) (is : List Nat) :
    ∀ (acc : AssertState), (is.map xDeclSexp).foldl (scanAssertsStep numOut) (.ok acc) = .ok acc := by
  induction is with
  | nil => intro acc; simp
  | cons i is ih =>
    intro acc
    rw [List.map_cons, List.foldl_cons, scanAssertsStep_xdecl numOut acc i]
    exact ih acc

/-- The asserts pass skips `Y_j` declarations. -/
lemma scanAsserts_ydeclFold (numOut : Nat) (is : List Nat) :
    ∀ (acc : AssertState), (is.map yDeclSexp).foldl (scanAssertsStep numOut) (.ok acc) = .ok acc := by
  induction is with
  | nil => intro acc; simp
  | cons i is ih =>
    intro acc
    rw [List.map_cons, List.foldl_cons, scanAssertsStep_ydecl numOut acc i]
    exact ih acc

/-- The asserts pass skips `N_k` declarations. -/
lemma scanAsserts_ndeclFold (numOut : Nat) (ks : List Nat) :
    ∀ (acc : AssertState), (ks.map nDeclSexp).foldl (scanAssertsStep numOut) (.ok acc) = .ok acc := by
  induction ks with
  | nil => intro acc; simp
  | cons k ks ih =>
    intro acc
    rw [List.map_cons, List.foldl_cons, scanAssertsStep_ndecl numOut acc k]
    exact ih acc

lemma replicate_none_size (n : Nat) : ((List.replicate n (none : Option ℚ)).toArray).size = n := by
  simp

lemma replicate_none_get! (n i : Nat) (h : i < n) :
    (List.replicate n (none : Option ℚ)).toArray[i]! = none := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, h]

/-! ## End-to-end `parseAptp ∘ printAptp` round-trip

A `RawProblem` carries the *source* form of a problem (decimals as `RawDec`,
neurons/objectives/leaves as lists) alongside its `Problem` interpretation
(`decode`). `printAptp` renders it as a canonical `.aptp` file; the main theorem
shows `parseAptp` recovers exactly `decode raw` for well-formed `raw`. -/

/-- The source form of a checkable problem. `loDof`/`hiDof` give the (decimal)
lower/upper bound for each input; `objs`/`leaves` are the output rows and DNF
leaves. -/
structure RawProblem where
  numInputs : Nat
  numOutputs : Nat
  neurons : List Nat
  loDof : Nat → RawDec
  hiDof : Nat → RawDec
  objs : List RawObj
  leaves : List (List Int)

/-- Well-formedness: the box has exactly one well-formed `(lo,hi)` per input,
each objective is a single well-formed row, and the leaves are nonempty, use
only nonzero signed neuron ids, and reference declared neurons. -/
structure RawProblem.WF (raw : RawProblem) : Prop where
  loWF : ∀ i < raw.numInputs, (raw.loDof i).WF
  hiWF : ∀ i < raw.numInputs, (raw.hiDof i).WF
  objsWF : ∀ o ∈ raw.objs, WFObj o
  leavesNe : raw.leaves ≠ []
  leavesWF : ∀ L ∈ raw.leaves, L ≠ [] ∧ ∀ k ∈ L, k ≠ 0
  leavesRef : ∀ L ∈ raw.leaves, ∀ k ∈ L, k.natAbs ∈ raw.neurons

/-- The `Problem` a `RawProblem` denotes. -/
def decode (raw : RawProblem) : Problem :=
  { numInputs := raw.numInputs,
    numOutputs := raw.numOutputs,
    neurons := raw.neurons.toArray,
    box := ((List.range raw.numInputs).map (fun i => ((raw.loDof i).value, (raw.hiDof i).value))).toArray,
    objectives := (raw.objs.map (decodeObj raw.numOutputs)).toArray,
    leaves := (raw.leaves.map List.toArray).toArray }

/-- The declaration statements (`declare-const X_i`/`Y_j`, `declare-pwl N_k`). -/
def declStmts (raw : RawProblem) : List Sexp :=
  (List.range raw.numInputs).map xDeclSexp
  ++ (List.range raw.numOutputs).map yDeclSexp
  ++ raw.neurons.map nDeclSexp

/-- The assert statements (box lower/upper bounds, objectives, the DNF `or`). -/
def assertStmts (raw : RawProblem) : List Sexp :=
  (List.range raw.numInputs).map (fun i => boxLoSexp i (raw.loDof i))
  ++ (List.range raw.numInputs).map (fun i => boxHiSexp i (raw.hiDof i))
  ++ raw.objs.map objSexp
  ++ [orAssertSexp raw.leaves]

/-- All statements of a printed problem, declarations then asserts. -/
def stmtsOf (raw : RawProblem) : List Sexp := declStmts raw ++ assertStmts raw

/-- The lower-bound array produced by folding the box-lower asserts. -/
def loArr (raw : RawProblem) : Array (Option ℚ) :=
  (List.range raw.numInputs).foldl (fun a i => a.set! i (some (raw.loDof i).value))
    (List.replicate raw.numInputs (none : Option ℚ)).toArray
/-- The upper-bound array produced by folding the box-upper asserts. -/
def hiArr (raw : RawProblem) : Array (Option ℚ) :=
  (List.range raw.numInputs).foldl (fun a i => a.set! i (some (raw.hiDof i).value))
    (List.replicate raw.numInputs (none : Option ℚ)).toArray

/-- Render a `RawProblem` as a canonical `.aptp` file: one statement per line,
each newline-terminated. -/
def printAptp (raw : RawProblem) : String :=
  String.ofList (joinNL ((stmtsOf raw).map stmtChars))

lemma assertStmts_isAssert (raw : RawProblem) :
    ∀ e ∈ assertStmts raw, ∃ body, e = .list [.atom "assert", body] := by
  intro e he
  simp only [assertStmts, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with ((h | h) | h) | h
  · obtain ⟨i, _, rfl⟩ := h; exact ⟨_, rfl⟩
  · obtain ⟨i, _, rfl⟩ := h; exact ⟨_, rfl⟩
  · obtain ⟨o, _, rfl⟩ := h; cases o <;> exact ⟨_, rfl⟩
  · subst h; exact ⟨_, rfl⟩

/-- Every printed statement of a well-formed problem is a `WF` S-expression. -/
lemma stmtsOf_wf (raw : RawProblem) (hwf : raw.WF) : ∀ e ∈ stmtsOf raw, WF e := by
  intro e he
  simp only [stmtsOf, declStmts, assertStmts, List.mem_append, List.mem_map,
    List.mem_singleton] at he
  rcases he with ((h | h) | h) | (((h | h) | h) | h)
  · obtain ⟨i, _, rfl⟩ := h; exact WF_xDeclSexp i
  · obtain ⟨j, _, rfl⟩ := h; exact WF_yDeclSexp j
  · obtain ⟨k, _, rfl⟩ := h; exact WF_nDeclSexp k
  · obtain ⟨i, hi, rfl⟩ := h; exact WF_boxLoSexp i _ (hwf.loWF i (List.mem_range.mp hi))
  · obtain ⟨i, hi, rfl⟩ := h; exact WF_boxHiSexp i _ (hwf.hiWF i (List.mem_range.mp hi))
  · obtain ⟨o, ho, rfl⟩ := h; exact WF_objSexp o (hwf.objsWF o ho)
  · subst h; exact WF_orAssertSexp raw.leaves

/-- **Declares pass.** Folding `scanDeclsStep` over all printed statements
recovers `(numInputs-1, numOutputs-1, neurons)` (asserts are skipped). -/
lemma decls_pass (raw : RawProblem) :
    (stmtsOf raw).foldl scanDeclsStep (.ok (-1, -1, #[]))
      = .ok ((raw.numInputs : Int) - 1, (raw.numOutputs : Int) - 1, raw.neurons.toArray) := by
  rw [stmtsOf, List.foldl_append, declStmts, List.foldl_append, List.foldl_append,
    xDecls_fold (List.range raw.numInputs) (-1) #[] (-1), foldl_max_range,
    yDecls_fold (List.range raw.numOutputs) ((raw.numInputs : Int) - 1) #[] (-1), foldl_max_range,
    nDecls_fold raw.neurons ((raw.numInputs : Int) - 1) ((raw.numOutputs : Int) - 1) #[],
    scanDecls_assertsIdent (assertStmts raw) (assertStmts_isAssert raw)]
  simp

/-- **Asserts pass.** Folding `scanAssertsStep` over all printed statements
recovers the box lower/upper arrays, the objective rows, and the DNF leaves
(declares are skipped). -/
lemma asserts_pass (raw : RawProblem) (hwf : raw.WF) :
    (stmtsOf raw).foldl (scanAssertsStep raw.numOutputs)
        (.ok ((List.replicate raw.numInputs (none : Option ℚ)).toArray,
              (List.replicate raw.numInputs (none : Option ℚ)).toArray, #[], #[]))
      = .ok (loArr raw, hiArr raw,
             (raw.objs.map (decodeObj raw.numOutputs)).toArray,
             (raw.leaves.map List.toArray).toArray) := by
  have hloWF : ∀ i ∈ List.range raw.numInputs, (raw.loDof i).WF :=
    fun i hi => hwf.loWF i (List.mem_range.mp hi)
  have hhiWF : ∀ i ∈ List.range raw.numInputs, (raw.hiDof i).WF :=
    fun i hi => hwf.hiWF i (List.mem_range.mp hi)
  have hbound : ∀ i ∈ List.range raw.numInputs,
      i < ((List.replicate raw.numInputs (none : Option ℚ)).toArray).size :=
    fun i hi => by rw [replicate_none_size]; exact List.mem_range.mp hi
  have hnone : ∀ i ∈ List.range raw.numInputs,
      ((List.replicate raw.numInputs (none : Option ℚ)).toArray)[i]! = none :=
    fun i hi => replicate_none_get! _ i (List.mem_range.mp hi)
  -- declares are no-ops for the asserts pass
  rw [stmtsOf, List.foldl_append, declStmts, List.foldl_append, List.foldl_append,
    scanAsserts_xdeclFold raw.numOutputs (List.range raw.numInputs),
    scanAsserts_ydeclFold raw.numOutputs (List.range raw.numOutputs),
    scanAsserts_ndeclFold raw.numOutputs raw.neurons]
  -- process the assert segments in order
  rw [assertStmts, List.foldl_append, List.foldl_append, List.foldl_append,
    boxLo_scan raw.numOutputs (List.range raw.numInputs) raw.loDof hloWF List.nodup_range
      (List.replicate raw.numInputs (none : Option ℚ)).toArray #[] #[]
      (List.replicate raw.numInputs (none : Option ℚ)).toArray hbound hnone]
  rw [boxHi_scan raw.numOutputs (List.range raw.numInputs) raw.hiDof hhiWF List.nodup_range
      _ #[] #[] (List.replicate raw.numInputs (none : Option ℚ)).toArray hbound hnone]
  rw [objs_scan raw.numOutputs raw.objs hwf.objsWF _ _ #[] #[]]
  rw [List.foldl_cons, List.foldl_nil,
    scanAssertsStep_orAssert raw.numOutputs _ _ _ #[] raw.leaves
      hwf.leavesNe hwf.leavesWF]
  simp [loArr, hiArr]

/-- **Box-finalize pass.** With the folded lower/upper arrays, `finalizeBoxStep`
produces the `(lo,hi)` pair array. -/
lemma box_pass (raw : RawProblem) :
    (List.range raw.numInputs).foldl (finalizeBoxStep (loArr raw) (hiArr raw)) (.ok #[])
      = .ok ((List.range raw.numInputs).map
          (fun i => ((raw.loDof i).value, (raw.hiDof i).value))).toArray := by
  have hbnd : ∀ x ∈ List.range raw.numInputs,
      x < ((List.replicate raw.numInputs (none : Option ℚ)).toArray).size :=
    fun x hx => by rw [replicate_none_size]; exact List.mem_range.mp hx
  have hget : ∀ i ∈ List.range raw.numInputs,
      (loArr raw)[i]! = some (raw.loDof i).value ∧ (hiArr raw)[i]! = some (raw.hiDof i).value := by
    intro i hi
    refine ⟨?_, ?_⟩
    · exact foldl_set_get (List.range raw.numInputs) _ (fun i => some (raw.loDof i).value) i hi
        List.nodup_range hbnd
    · exact foldl_set_get (List.range raw.numInputs) _ (fun i => some (raw.hiDof i).value) i hi
        List.nodup_range hbnd
  rw [finalizeBox_list (loArr raw) (hiArr raw) (fun i => (raw.loDof i).value)
      (fun i => (raw.hiDof i).value) (List.range raw.numInputs) hget #[]]
  simp

/-- **Top-level round-trip.** For any well-formed `RawProblem`, parsing its
printed form recovers exactly the decoded `Problem`. Composes the statement
reader, the S-expression parser, and the declares/asserts/box passes. -/
theorem parseAptp_printAptp (raw : RawProblem) (hwf : raw.WF) :
    parseAptp (printAptp raw) = .ok (decode raw) := by
  have hclean : ∀ l ∈ (stmtsOf raw).map stmtChars, CleanBalLine l := by
    intro l hl
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
    exact stmtChars_cleanBal e (stmtsOf_wf raw hwf e he)
  have hread : readStatementsFold (printAptp raw) = .ok ((stmtsOf raw).map stmtChars).toArray :=
    readStatementsFold_multi ((stmtsOf raw).map stmtChars) (printAptp raw) hclean
      (by rw [printAptp, String.toList_ofList])
  have hN : ((raw.numInputs : Int) - 1 + 1).toNat = raw.numInputs := by omega
  have hM : ((raw.numOutputs : Int) - 1 + 1).toNat = raw.numOutputs := by omega
  unfold parseAptp
  rw [hread]
  simp only [except_ok_bind,
    parseAll_fold (stmtsOf raw) (stmtsOf_wf raw hwf) #[], Array.empty_append,
    decls_pass raw, hN, hM, asserts_pass raw hwf, box_pass raw, decode]

end AptpCheck.Ast.AptpRoundtrip
