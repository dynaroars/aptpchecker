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

end AptpCheck.Ast.AptpRoundtrip
