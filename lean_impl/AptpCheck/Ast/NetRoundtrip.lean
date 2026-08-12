import AptpCheck.Ast.Net

/-!
# Faithfulness of the `.net` parser: printer/parser round-trip lemmas

This module works towards making the `.net` network parser
(`AptpCheck.Ast.parseNet`) *faithful*: for each **total** stage of the parser we
prove that a printer emitting the exact `.net` grammar round-trips through it.
To sidestep the representability gap (not every `ℚ` is exactly printable in the
format), weights are carried as their float32 *bit patterns* (`UInt32`), printed
as 8-hex-digit `0xXXXXXXXX` tokens — exactly the shape `parseWeight?` decodes via
`float32ToRat`.

Verified, axiom-clean round-trips (no `sorry`, no `native_decide`):

* `parseWeight_printHex`   — one weight: `parseWeight? (printHex b) = some (float32ToRat b)`.
* `takeWeights_printHex`   — a printed weight list: `takeWeights` recovers the decoded array.
* `natOfDigits_natToDigits`— decimal naturals (used for layer dimensions).
* `readInputDims_decTok`   — the `INPUT` dimension is read back exactly.
* `tokenize_jn`            — the tokenizer: a space-separated list of well-formed
                             atoms tokenizes back to exactly those atoms
                             (via the loop-to-`foldl` characterization `tokenize_eq`).
* `readStatements_single`  — the statement reader on a single well-formed line
                             (comment strip + trim + parenthesis balance) returns
                             that line as the sole statement.

**Full round-trip (now proved):** `Ast/Net.lean`'s layer loop was refactored from
a `partial def` into `parseLayersFuel` (total, structural on a `Nat` fuel), which
the kernel *can* unfold and induct on. With that in place this file now proves the
complete assembly `parseNet (printNet r) = .ok (rawToNet r)` for well-formed
`RawNet`s — see `parseNet_printNet` at the end. `printNet`/`rawToNet` carry weights
as float32 bit patterns (printed `0xXXXXXXXX`, decoded by `float32ToRat`), and the
theorem covers `Linear`, `ReLU`, and `Flatten` layers with one `INPUT` dimension.
The build is `sorry`-free and axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace AptpCheck.Ast.Roundtrip

open AptpCheck.Ast AptpCheck.Numeric AptpCheck.Model

/-! ## Hex digits -/

/-- Character for a single hex nibble (`0..15`); values `≥ 16` default to `'f'`. -/
def hexChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

/-- `hexChar` is a right inverse of the parser's `hexDigit?` on nibbles. -/
lemma hexDigit_hexChar : ∀ d, d < 16 → hexDigit? (hexChar d) = some d := by decide

/-- Specialised to a reduced-mod argument, which is always a nibble. -/
lemma hexDigit_hexChar_mod (k : Nat) : hexDigit? (hexChar (k % 16)) = some (k % 16) :=
  hexDigit_hexChar (k % 16) (Nat.mod_lt k (by norm_num))

/-- The 8 hex digits of a 32-bit value, most-significant first. -/
def hexDigitsOfNat (n : Nat) : List Char :=
  [ hexChar (n / 268435456 % 16), hexChar (n / 16777216 % 16),
    hexChar (n / 1048576 % 16),   hexChar (n / 65536 % 16),
    hexChar (n / 4096 % 16),      hexChar (n / 256 % 16),
    hexChar (n / 16 % 16),        hexChar (n % 16) ]

/-- The parser's `natOfHex?` inverts `hexDigitsOfNat` on any 32-bit value. -/
lemma natOfHex_hexDigits (n : Nat) (h : n < 4294967296) :
    natOfHex? (hexDigitsOfNat n) = some n := by
  unfold natOfHex? hexDigitsOfNat
  simp only [List.foldl_cons, List.foldl_nil, hexDigit_hexChar_mod]
  congr 1
  omega

/-! ## One weight token -/

/-- Print a float32 bit pattern as a `0xXXXXXXXX` token (8 hex digits). -/
def printHex (b : UInt32) : String :=
  String.ofList ('0' :: 'x' :: hexDigitsOfNat b.toNat)

@[simp] lemma printHex_toList (b : UInt32) :
    (printHex b).toList = '0' :: 'x' :: hexDigitsOfNat b.toNat := by
  simp [printHex]

/-- **Step 1 (single weight round-trip).** Parsing a printed float32 bit pattern
recovers exactly the rational `float32ToRat` decodes it to. -/
theorem parseWeight_printHex (b : UInt32) :
    parseWeight? (printHex b) = some (float32ToRat b) := by
  unfold parseWeight?
  rw [printHex_toList]
  simp only []
  rw [natOfHex_hexDigits b.toNat (UInt32.toNat_lt_size b)]
  simp [UInt32.ofNat_toNat]

/-! ## Decimal naturals (for dimensions) -/

/-- Character for a single decimal digit (`0..9`); values `≥ 10` default to `'0'`. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9' | _ => '0'

lemma digitChar_isDigit : ∀ d, d < 10 → (digitChar d).isDigit = true := by decide
lemma digitChar_toNat : ∀ d, d < 10 → (digitChar d).toNat - '0'.toNat = d := by decide

/-- Decimal digits of a `Nat`, most-significant first. -/
def natToDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n]
  else natToDigits (n / 10) ++ [digitChar (n % 10)]
  termination_by n
  decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

/-- Appending one valid decimal digit multiplies the accumulated value by ten. -/
lemma natOfDigits_append (L : List Char) (m d : Nat) (hd : d < 10)
    (hL : natOfDigits? L = some m) :
    natOfDigits? (L ++ [digitChar d]) = some (m * 10 + d) := by
  unfold natOfDigits? at hL ⊢
  rw [List.foldl_append, hL]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [digitChar_isDigit d hd, digitChar_toNat d hd]
  simp

/-- The parser's `natOfDigits?` inverts `natToDigits`. -/
lemma natOfDigits_natToDigits (n : Nat) : natOfDigits? (natToDigits n) = some n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [natToDigits]
    split
    · next h =>
      unfold natOfDigits?
      simp only [List.foldl_cons, List.foldl_nil]
      rw [digitChar_isDigit n h, digitChar_toNat n h]; simp
    · next h =>
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by norm_num)
      rw [natOfDigits_append _ _ _ (Nat.mod_lt n (by norm_num)) (ih (n / 10) hlt)]
      congr 1; omega

/-! ## Tokenizer characterization

The parser's `tokenize` runs a `for`-loop over the input characters with two
mutable accumulators. We characterize that loop as a pure `List.foldl` over
`tokStep`, then prove that a space-separated list of well-formed tokens
tokenizes back to exactly that list. -/

/-- One step of `tokenize`'s loop; state is `⟨cur, toks⟩` (both built reversed). -/
def tokStep (r : MProd (List Char) (List String)) (c : Char) : MProd (List Char) (List String) :=
  if c == '(' || c == ')' then
    (if !r.1.isEmpty then ⟨[], String.ofList [c] :: String.ofList r.1.reverse :: r.2⟩
     else ⟨r.1, String.ofList [c] :: r.2⟩)
  else if c.isWhitespace then
    (if !r.1.isEmpty then ⟨[], String.ofList r.1.reverse :: r.2⟩ else ⟨r.1, r.2⟩)
  else ⟨c :: r.1, r.2⟩

/-- Post-processing after `tokenize`'s loop: flush the last token, un-reverse. -/
def tokPost (r : MProd (List Char) (List String)) : List String :=
  if !r.1.isEmpty then (String.ofList r.1.reverse :: r.2).reverse else r.2.reverse

/-- A character `tokenize` treats as part of an atom (not a paren, not whitespace). -/
def IsTokChar (c : Char) : Prop := (c == '(' || c == ')') = false ∧ c.isWhitespace = false

/-- Space-before-each join of statement/token character lists, matching how
`parseNet` re-joins statements (`acc ++ ' ' :: s`, prefixing each with a space). -/
def jn : List (List Char) → List Char
  | [] => []
  | s :: ss => ' ' :: s ++ jn ss

private lemma id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- The parser's `tokenize` loop equals a `List.foldl` of `tokStep`. -/
lemma tokenize_eq (input : List Char) :
    tokenize input = tokPost (input.foldl tokStep ⟨[], []⟩) := by
  simp only [tokenize, Id.run, pure_bind,
    ← apply_ite (f := fun z => (pure (f := Id) (ForInStep.yield z))),
    List.forIn_pure_yield_eq_foldl]
  simp only [id_pure]
  rfl

/-- Folding `tokStep` over a run of atom characters accumulates them (reversed). -/
lemma foldl_tokStep_normal (cs : List Char) (h : ∀ c ∈ cs, IsTokChar c)
    (cur : List Char) (toks : List String) :
    cs.foldl tokStep ⟨cur, toks⟩ = ⟨cs.reverse ++ cur, toks⟩ := by
  induction cs generalizing cur toks with
  | nil => rfl
  | cons c cs ih =>
    have hc : IsTokChar c := h c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, IsTokChar x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons]
    have : tokStep ⟨cur, toks⟩ c = ⟨c :: cur, toks⟩ := by
      unfold tokStep; rw [hc.1]; simp [hc.2]
    rw [this, ih hcs]; simp

/-- A space flushes the current atom (if any). -/
lemma tokStep_space (cur : List Char) (toks : List String) :
    tokStep ⟨cur, toks⟩ ' ' =
      (if cur.isEmpty then ⟨[], toks⟩ else ⟨[], String.ofList cur.reverse :: toks⟩) := by
  unfold tokStep; norm_num; split <;> simp_all

/-- Master loop invariant: folding `tokStep` over `jn ss` (with a running atom
`cur` and accumulated tokens `toks`) yields, after post-processing, the earlier
tokens, then `cur` flushed, then each element of `ss` as a token. -/
lemma tokPost_foldl_jn (ss : List (List Char))
    (hv : ∀ s ∈ ss, s ≠ [] ∧ ∀ c ∈ s, IsTokChar c) :
    ∀ (cur : List Char) (toks : List String),
      tokPost ((jn ss).foldl tokStep ⟨cur, toks⟩)
        = toks.reverse ++ (if cur.isEmpty then [] else [String.ofList cur.reverse])
            ++ ss.map (fun s => String.ofList s) := by
  induction ss with
  | nil =>
    intro cur toks
    simp only [jn, List.foldl_nil, List.map_nil, List.append_nil]
    unfold tokPost; split <;> simp_all
  | cons s ss ih =>
    intro cur toks
    obtain ⟨hsne, hstok⟩ := hv s (List.mem_cons_self ..)
    have hss : ∀ x ∈ ss, x ≠ [] ∧ ∀ c ∈ x, IsTokChar c :=
      fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hsrev : s.reverse.isEmpty = false := by simp [hsne]
    simp only [jn, List.foldl_cons, List.foldl_append]
    rw [tokStep_space]
    by_cases hcur : cur.isEmpty
    · simp only [hcur, if_pos]
      rw [foldl_tokStep_normal s hstok [] toks, List.append_nil, ih hss s.reverse toks]
      simp only [hsrev, List.reverse_reverse, List.map_cons,
        Bool.false_eq_true, if_false]
      simp
    · simp only [hcur, if_neg, Bool.false_eq_true, not_false_eq_true]
      rw [foldl_tokStep_normal s hstok [] (String.ofList cur.reverse :: toks),
        List.append_nil, ih hss s.reverse (String.ofList cur.reverse :: toks)]
      simp only [hsrev, List.reverse_reverse, List.map_cons,
        Bool.false_eq_true, if_false, List.reverse_cons]
      simp

/-- **Tokenizer round-trip.** A space-before-each join of well-formed, nonempty,
atom-only tokens tokenizes back to exactly those tokens. -/
theorem tokenize_jn (ss : List (List Char))
    (hv : ∀ s ∈ ss, s ≠ [] ∧ ∀ c ∈ s, IsTokChar c) :
    tokenize (jn ss) = ss.map (fun s => String.ofList s) := by
  rw [tokenize_eq, tokPost_foldl_jn ss hv [] []]
  simp

/-! ## Weight lists (`takeWeights`) -/

/-- **Step 2 (weight-list round-trip).** `takeWeights` over a printed list of
float32 bit patterns recovers exactly the decoded rational array. -/
theorem takeWeights_printHex (ws : List UInt32) (rest : List String) :
    takeWeights ws.length (ws.map printHex ++ rest)
      = .ok ((ws.map float32ToRat).toArray, rest) := by
  induction ws generalizing rest with
  | nil => simp [takeWeights]
  | cons w ws ih =>
    simp only [List.length_cons, List.map_cons, List.cons_append, takeWeights,
      parseWeight_printHex]
    rw [ih rest]
    simp [Except.map]

/-! ## Statement reader (`readStatements`) -/

/-- `splitOnChar` on a separator-free list returns the whole list as one segment. -/
lemma splitOnChar_no_sep (l : List Char) (h : '\n' ∉ l) : splitOnChar '\n' l = [l] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '\n' := by simp at h; tauto
    have hcs : '\n' ∉ cs := by simp at h ⊢; tauto
    unfold splitOnChar; simp only [beq_iff_eq, hc, ih hcs]; rfl

/-- **Statement reader on a single well-formed line.** For content that is a
single line (no newline), free of comments (`;`) and parentheses, with no
surrounding whitespace and nonempty, `readStatements` returns it as one
statement. This is exactly the shape a single-line printed `.net` file has. -/
theorem readStatements_single (content : String)
    (hnl : '\n' ∉ content.toList)
    (hline : rtrim (beforeSemicolon (trimC content.toList)) = content.toList)
    (hne : content.toList ≠ [])
    (hp1 : content.toList.countP (fun x => x == '(') = 0)
    (hp2 : content.toList.countP (fun x => x == ')') = 0) :
    readStatements content = .ok #[content.toList] := by
  have hE : content.toList.isEmpty = false := by
    cases h : content.toList with
    | nil => exact absurd h hne
    | cons c cs => rfl
  unfold readStatements
  simp only [Id.run, splitOnChar_no_sep content.toList hnl,
    List.forIn_cons, List.forIn_nil, hline, hp1, hp2, hE, List.isEmpty_nil]
  rfl

/-! ## Input dimensions (`readInputDims`) -/

/-- A printed decimal token. -/
def decTok (n : Nat) : String := String.ofList (natToDigits n)

@[simp] lemma decTok_toList (n : Nat) : (decTok n).toList = natToDigits n := by
  simp [decTok]

/-- `readInputDims` reads a single printed decimal dimension, stopping at the
following non-numeric token (e.g. `LAYER`/`END`). -/
theorem readInputDims_decTok (n : Nat) (t : String) (rest : List String)
    (ht : natOfDigits? t.toList = none) :
    readInputDims (decTok n :: t :: rest) = ([n], t :: rest) := by
  have hinner : readInputDims (t :: rest) = ([], t :: rest) := by
    unfold readInputDims; simp only [ht]
  unfold readInputDims
  simp only [decTok_toList, natOfDigits_natToDigits, hinner]

/-! ## Raw (printable) networks

A `RawNet` carries weights as their float32 *bit patterns* (`UInt32`), so it is
exactly printable in the `.net` grammar; `rawToNet` decodes it (via `float32ToRat`)
to the `Network` the parser produces. -/

/-- A dense affine layer with weights as float32 bit patterns. -/
structure RawLinear where
  outDim : Nat
  inDim : Nat
  W : Array UInt32
  b : Array UInt32

/-- A printable layer. -/
inductive RawLayer where
  | linear (l : RawLinear)
  | relu
  | flatten

/-- Decode a `RawLayer` to the exact-rational `Layer` the parser yields. -/
def rawToLayer : RawLayer → Layer
  | .relu => .relu
  | .flatten => .flatten
  | .linear l => .linear { outDim := l.outDim, inDim := l.inDim, W := (l.W.toList.map float32ToRat).toArray, b := (l.b.toList.map float32ToRat).toArray }

/-- Well-formed layer: for `Linear`, the weight/bias arrays have the sizes the
declared dimensions demand (so `takeWeights` consumes exactly them). -/
def WFLayer : RawLayer → Prop
  | .linear l => l.outDim * l.inDim = l.W.size ∧ l.outDim = l.b.size
  | _ => True

/-- Tokens of the `LAYER …` block for a list of raw layers (no trailing `END`). -/
def layerTokens : List RawLayer → List String
  | [] => []
  | .relu :: rest => "LAYER" :: "ReLU" :: layerTokens rest
  | .flatten :: rest => "LAYER" :: "Flatten" :: layerTokens rest
  | .linear l :: rest =>
      "LAYER" :: "Linear" :: decTok l.outDim :: decTok l.inDim :: "W" ::
        (l.W.toList.map printHex ++ "B" :: (l.b.toList.map printHex ++ layerTokens rest))

/-- `takeWeights` on a printed weight list, with the count given as a hypothesis. -/
lemma takeWeights_printHex' (n : Nat) (ws : List UInt32) (rest : List String)
    (h : n = ws.length) :
    takeWeights n (ws.map printHex ++ rest) = .ok ((ws.map float32ToRat).toArray, rest) := by
  subst h; exact takeWeights_printHex ws rest

/-- `Except.ok` is a left unit for `bind` (definitional). -/
lemma except_ok_bind {ε α β} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-! ## Layer loop (`parseLayersFuel`) -/

/-- `END` terminates the loop at any fuel. -/
lemma parseLayersFuel_END (fuel : Nat) (xs : List String) (acc : Array Layer) :
    parseLayersFuel fuel ("END" :: xs) acc = .ok acc := by
  cases fuel <;> rfl

/-- One `LAYER Linear` step: parsing a printed Linear block advances to the tail
tokens with the decoded layer pushed onto the accumulator. -/
lemma parseLayersFuel_linear (fuel : Nat) (l : RawLinear) (tail : List String)
    (acc : Array Layer) (hW : l.outDim * l.inDim = l.W.size) (hb : l.outDim = l.b.size) :
    parseLayersFuel (fuel+1)
      ("LAYER" :: "Linear" :: decTok l.outDim :: decTok l.inDim :: "W" ::
        (l.W.toList.map printHex ++ "B" :: (l.b.toList.map printHex ++ tail))) acc
      = parseLayersFuel fuel tail (acc.push (rawToLayer (.linear l))) := by
  have hWlen : l.outDim * l.inDim = l.W.toList.length := by rw [hW, Array.length_toList]
  have hblen : l.outDim = l.b.toList.length := by rw [hb, Array.length_toList]
  simp only [parseLayersFuel, decTok_toList, natOfDigits_natToDigits]
  rw [takeWeights_printHex' _ l.W.toList _ hWlen]
  simp only [except_ok_bind]
  rw [takeWeights_printHex' _ l.b.toList _ hblen]
  simp only [except_ok_bind, rawToLayer]

/-- **Layer-loop round-trip.** For sufficient `fuel`, the loop over the printed
tokens of a list of well-formed layers (followed by `END`) recovers exactly the
decoded layers appended to the accumulator. -/
lemma parseLayersFuel_layerTokens :
    ∀ (layers : List RawLayer), (∀ l ∈ layers, WFLayer l) →
    ∀ (fuel : Nat), layers.length ≤ fuel → ∀ (acc : Array Layer),
      parseLayersFuel fuel (layerTokens layers ++ ["END"]) acc
        = .ok (acc ++ (layers.map rawToLayer).toArray) := by
  intro layers
  induction layers with
  | nil =>
    intro _ fuel _ acc
    simp only [layerTokens, List.nil_append]
    rw [parseLayersFuel_END]
    simp
  | cons layer rest ih =>
    intro hwf fuel hfuel acc
    have hwfrest : ∀ l ∈ rest, WFLayer l := fun l hl => hwf l (List.mem_cons_of_mem _ hl)
    cases fuel with
    | zero => simp only [List.length_cons] at hfuel; omega
    | succ f =>
      have hlen : rest.length ≤ f := by simp only [List.length_cons] at hfuel; omega
      cases layer with
      | relu =>
        have step : parseLayersFuel (f+1) (layerTokens (.relu :: rest) ++ ["END"]) acc
            = parseLayersFuel f (layerTokens rest ++ ["END"]) (acc.push .relu) := rfl
        rw [step, ih hwfrest f hlen]; simp [rawToLayer]
      | flatten =>
        have step : parseLayersFuel (f+1) (layerTokens (.flatten :: rest) ++ ["END"]) acc
            = parseLayersFuel f (layerTokens rest ++ ["END"]) (acc.push .flatten) := rfl
        rw [step, ih hwfrest f hlen]; simp [rawToLayer]
      | linear l =>
        obtain ⟨hW, hb⟩ := hwf _ (List.mem_cons_self ..)
        simp only [layerTokens, List.append_assoc, List.cons_append]
        rw [parseLayersFuel_linear f l (layerTokens rest ++ ["END"]) acc hW hb, ih hwfrest f hlen]
        simp [rawToLayer]

/-! ## Space-join of tokens

`printNet` renders all tokens on a single line, separated by single spaces; this
is `joinSp` at the char-list level. The parser rejoins statements with a *leading*
space per statement (`jn`), so `' ' :: joinSp = jn` bridges the two. -/

/-- Join token char-lists with single-space separators (no leading/trailing space). -/
def joinSp : List (List Char) → List Char
  | [] => []
  | s :: ss => s ++ jn ss

lemma jn_append_singleton (ys : List (List Char)) (t : List Char) :
    jn (ys ++ [t]) = jn ys ++ ' ' :: t := by
  induction ys with
  | nil => simp [jn]
  | cons y ys ih => simp only [List.cons_append, jn, ih]; simp [List.append_assoc]

lemma joinSp_append_singleton (s : List Char) (xs : List (List Char)) (t : List Char) :
    joinSp (s :: xs ++ [t]) = joinSp (s :: xs) ++ ' ' :: t := by
  simp only [List.cons_append, joinSp, jn_append_singleton, List.append_assoc]

lemma jn_cons_eq (s : List Char) (ss : List (List Char)) :
    jn (s :: ss) = ' ' :: joinSp (s :: ss) := by
  simp [jn, joinSp]

/-- Characters that are neither parens, semicolons, nor newlines. -/
def NotBad (c : Char) : Prop := c ≠ '(' ∧ c ≠ ')' ∧ c ≠ ';' ∧ c ≠ '\n'

lemma space_notBad : NotBad ' ' := by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

lemma isTokChar_ne_newline {c : Char} (h : IsTokChar c) : c ≠ '\n' := by
  intro he; subst he; exact absurd h.2 (by decide)

lemma isTokChar_notParen {c : Char} (h : IsTokChar c) : c ≠ '(' ∧ c ≠ ')' := by
  have := h.1
  rw [Bool.or_eq_false_iff] at this
  exact ⟨by simpa using this.1, by simpa using this.2⟩

lemma mem_jn {c : Char} : ∀ (ss : List (List Char)), c ∈ jn ss → c = ' ' ∨ ∃ s ∈ ss, c ∈ s
  | [], h => by simp [jn] at h
  | t :: ss, h => by
      simp only [jn, List.cons_append, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨t, List.mem_cons_self, h⟩
      · rcases mem_jn ss h with h' | ⟨s, hs, hcs⟩
        · exact Or.inl h'
        · exact Or.inr ⟨s, List.mem_cons_of_mem t hs, hcs⟩

lemma mem_joinSp {c : Char} {ss : List (List Char)} (h : c ∈ joinSp ss) :
    c = ' ' ∨ ∃ s ∈ ss, c ∈ s := by
  match ss, h with
  | [], h => simp [joinSp] at h
  | s :: ss, h =>
    simp only [joinSp, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr ⟨s, List.mem_cons_self, h⟩
    · rcases mem_jn ss h with h' | ⟨s', hs', hcs⟩
      · exact Or.inl h'
      · exact Or.inr ⟨s', List.mem_cons_of_mem s hs', hcs⟩

/-! ## Token well-formedness -/

/-- A well-formed token char-list: nonempty, all chars usable inside an atom
(not a paren, whitespace, or `;`). -/
def GoodStr (s : List Char) : Prop := s ≠ [] ∧ ∀ c ∈ s, IsTokChar c ∧ c ≠ ';'

lemma goodStr_of (s : List Char) (hne : s ≠ [])
    (h : ∀ c ∈ s, (c == '(' || c == ')') = false ∧ c.isWhitespace = false ∧ c ≠ ';') :
    GoodStr s :=
  ⟨hne, fun c hc => let ⟨a, b, d⟩ := h c hc; ⟨⟨a, b⟩, d⟩⟩

lemma digitChar_good (d : Nat) : IsTokChar (digitChar d) ∧ digitChar d ≠ ';' := by
  unfold digitChar
  split <;> exact ⟨⟨by decide, by decide⟩, by decide⟩

lemma hexChar_good (d : Nat) : IsTokChar (hexChar d) ∧ hexChar d ≠ ';' := by
  unfold hexChar
  split <;> exact ⟨⟨by decide, by decide⟩, by decide⟩

lemma natToDigits_ne_nil (n : Nat) : natToDigits n ≠ [] := by
  rw [natToDigits]; split <;> simp

lemma natToDigits_good (n : Nat) : ∀ c ∈ natToDigits n, IsTokChar c ∧ c ≠ ';' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [natToDigits]
    split
    · next h => intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact digitChar_good n
    · next h =>
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by norm_num)) c hc
      · simp only [List.mem_singleton] at hc; subst hc; exact digitChar_good (n % 10)

lemma decTok_good (n : Nat) : GoodStr (decTok n).toList := by
  rw [decTok_toList]
  exact ⟨natToDigits_ne_nil n, natToDigits_good n⟩

lemma hexDigitsOfNat_good (n : Nat) : ∀ c ∈ hexDigitsOfNat n, IsTokChar c ∧ c ≠ ';' := by
  intro c hc
  fin_cases hc <;> exact hexChar_good _

lemma printHex_good (b : UInt32) : GoodStr (printHex b).toList := by
  rw [printHex_toList]
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · exact ⟨⟨by decide, by decide⟩, by decide⟩
  · exact ⟨⟨by decide, by decide⟩, by decide⟩
  · exact hexDigitsOfNat_good _ c hc

/-! ## Trim/comment normalisation on a clean single line -/

lemma ltrim_cons_nonWs (c : Char) (l : List Char) (h : c.isWhitespace = false) :
    ltrim (c :: l) = c :: l := by
  simp only [ltrim, List.dropWhile_cons, h, if_false, Bool.false_eq_true]

lemma rtrim_append_nonWs (l : List Char) (c : Char) (h : c.isWhitespace = false) :
    rtrim (l ++ [c]) = l ++ [c] := by
  simp only [rtrim, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.dropWhile_cons, h, if_false, Bool.false_eq_true]
  simp

lemma beforeSemicolon_eq_self (l : List Char) (h : ∀ c ∈ l, c ≠ ';') : beforeSemicolon l = l := by
  rw [beforeSemicolon, List.takeWhile_eq_self_iff]
  intro c hc
  simp [h c hc]

/-! ## Printable networks and their token stream -/

/-- A printable network: an input dimension and a list of printable layers. -/
structure RawNet where
  inDim : Nat
  layers : List RawLayer

/-- Well-formed raw net: every layer is well-formed. -/
def RawNet.WF (r : RawNet) : Prop := ∀ l ∈ r.layers, WFLayer l

/-- The `Network` the parser produces from a `RawNet` (weights decoded to `ℚ`). -/
def rawToNet (r : RawNet) : Network :=
  { inDim := r.inDim, layers := (r.layers.map rawToLayer).toArray }

/-- Full token stream of a printed `.net` file: header, single input dim,
layer blocks, and the terminating `END`. -/
def netTokens (r : RawNet) : List String :=
  "NET" :: "v1" :: "INPUT" :: decTok r.inDim :: (layerTokens r.layers ++ ["END"])

/-- Render a `RawNet` as a single-line `.net` file (tokens space-separated). -/
def printNet (r : RawNet) : String := String.ofList (joinSp ((netTokens r).map String.toList))

-- fixed-string token goodness (each char checked individually to avoid deep `decide` recursion)
lemma good_NET : GoodStr "NET".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_v1 : GoodStr "v1".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_INPUT : GoodStr "INPUT".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_END : GoodStr "END".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_LAYER : GoodStr "LAYER".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_ReLU : GoodStr "ReLU".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_Flatten : GoodStr "Flatten".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_Linear : GoodStr "Linear".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_W : GoodStr "W".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩
lemma good_B : GoodStr "B".toList := by
  refine goodStr_of _ (by decide) ?_; intro c hc; fin_cases hc <;> exact ⟨by decide, by decide, by decide⟩

/-- Every token in a printed layer block is well-formed. -/
lemma layerTokens_good (layers : List RawLayer) :
    ∀ t ∈ layerTokens layers, GoodStr t.toList := by
  induction layers with
  | nil => intro t ht; simp [layerTokens] at ht
  | cons layer rest ih =>
    cases layer with
    | relu =>
      intro t ht
      simp only [layerTokens, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · exact good_LAYER
      · exact good_ReLU
      · exact ih t ht
    | flatten =>
      intro t ht
      simp only [layerTokens, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · exact good_LAYER
      · exact good_Flatten
      · exact ih t ht
    | linear l =>
      intro t ht
      simp only [layerTokens, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | ht | rfl | ht | ht
      · exact good_LAYER
      · exact good_Linear
      · exact decTok_good _
      · exact decTok_good _
      · exact good_W
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact printHex_good b
      · exact good_B
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact printHex_good b
      · exact ih t ht

/-- Every token in a printed `.net` file is well-formed. -/
lemma netChars_good (r : RawNet) : ∀ s ∈ (netTokens r).map String.toList, GoodStr s := by
  intro s hs
  rw [List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  simp only [netTokens, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | ht | rfl
  · exact good_NET
  · exact good_v1
  · exact good_INPUT
  · exact decTok_good _
  · exact layerTokens_good _ t ht
  · exact good_END

/-- The layer loop always has at least as many tokens as layers. -/
lemma layers_length_le (layers : List RawLayer) : layers.length ≤ (layerTokens layers).length := by
  induction layers with
  | nil => simp [layerTokens]
  | cons layer rest ih =>
    cases layer <;> simp only [layerTokens, List.length_cons, List.length_append] <;> omega

/-- Every char of a space-joined stream of good tokens is not a paren/`;`/newline. -/
lemma joinSp_notBad {ss : List (List Char)} (hg : ∀ s ∈ ss, GoodStr s) :
    ∀ c ∈ joinSp ss, NotBad c := by
  intro c hc
  rcases mem_joinSp hc with rfl | ⟨s, hs, hcs⟩
  · exact space_notBad
  · obtain ⟨_, hgs⟩ := hg s hs
    obtain ⟨htc, hsemi⟩ := hgs c hcs
    obtain ⟨hlp, hrp⟩ := isTokChar_notParen htc
    exact ⟨hlp, hrp, hsemi, isTokChar_ne_newline htc⟩

/-- Left-trim is a no-op: the first token starts with a non-whitespace char. -/
lemma ltrim_joinSp (s : List Char) (ss : List (List Char)) (hs : GoodStr s) :
    ltrim (joinSp (s :: ss)) = joinSp (s :: ss) := by
  obtain ⟨hne, hchars⟩ := hs
  cases s with
  | nil => exact absurd rfl hne
  | cons c cs =>
    have hcw : c.isWhitespace = false := (hchars c List.mem_cons_self).1.2
    simp only [joinSp, List.cons_append]
    exact ltrim_cons_nonWs c (cs ++ jn ss) hcw

/-- Right-trim is a no-op: the stream ends with the non-whitespace `END` token. -/
lemma rtrim_joinSp_END (front : List (List Char)) (hne : front ≠ []) :
    rtrim (joinSp (front ++ ["END".toList])) = joinSp (front ++ ["END".toList]) := by
  obtain ⟨s, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [joinSp_append_singleton]
  have hE : joinSp (s :: xs) ++ ' ' :: "END".toList
          = (joinSp (s :: xs) ++ [' ', 'E', 'N']) ++ ['D'] := by
    have : "END".toList = ['E', 'N', 'D'] := by decide
    rw [this]; simp [List.append_assoc]
  rw [hE]
  exact rtrim_append_nonWs _ 'D' (by decide)

/-- The token stream after `END` begins with a non-numeric token (`LAYER` or `END`),
so `readInputDims` stops right after the single input dimension. -/
lemma layerTokens_end_cons (layers : List RawLayer) :
    ∃ t rest0, layerTokens layers ++ ["END"] = t :: rest0 ∧ natOfDigits? t.toList = none := by
  cases layers with
  | nil => exact ⟨"END", [], rfl, by decide⟩
  | cons layer rest =>
    cases layer with
    | relu => exact ⟨"LAYER", _, rfl, by decide⟩
    | flatten => exact ⟨"LAYER", _, rfl, by decide⟩
    | linear l => exact ⟨"LAYER", _, rfl, by decide⟩

/-! ## Full `parseNet ∘ printNet` round-trip -/

/-- Nonempty stream: a leading space plus a space-join is a `jn`. -/
lemma jn_joinSp (ss : List (List Char)) (h : ss ≠ []) : ' ' :: joinSp ss = jn ss := by
  obtain ⟨s, ss, rfl⟩ := List.exists_cons_of_ne_nil h
  exact (jn_cons_eq s ss).symm

/-- `String.ofList` inverts `String.toList` pointwise over a token list. -/
lemma map_ofList_toList (l : List String) : (l.map String.toList).map String.ofList = l := by
  simp [List.map_map]

/-- **Tokenizer on a printed file.** Re-tokenizing a printed `.net` file (after
`parseNet`'s space-prefixed re-join) recovers exactly the token stream. -/
lemma tokenize_netTokens (r : RawNet) :
    tokenize (' ' :: (printNet r).toList) = netTokens r := by
  have hcontent : (printNet r).toList = joinSp ((netTokens r).map String.toList) := by
    simp only [printNet, String.toList_ofList]
  have hne : (netTokens r).map String.toList ≠ [] := by rw [netTokens]; simp
  have htokgood : ∀ s ∈ (netTokens r).map String.toList, s ≠ [] ∧ ∀ c ∈ s, IsTokChar c :=
    fun s hs => let ⟨h1, h2⟩ := netChars_good r s hs; ⟨h1, fun c hc => (h2 c hc).1⟩
  rw [hcontent, jn_joinSp _ hne, tokenize_jn _ htokgood, map_ofList_toList]

/-- **Statement reader on a printed file.** A printed `.net` file is a single
clean line, so `readStatements` returns it as the sole statement. -/
lemma readStatements_printNet (r : RawNet) :
    readStatements (printNet r) = .ok #[(printNet r).toList] := by
  have hgood : ∀ s ∈ (netTokens r).map String.toList, GoodStr s := netChars_good r
  have hcontent : (printNet r).toList = joinSp ((netTokens r).map String.toList) := by
    simp only [printNet, String.toList_ofList]
  have hnc1 : (netTokens r).map String.toList
      = "NET".toList :: (("v1" :: "INPUT" :: decTok r.inDim :: (layerTokens r.layers ++ ["END"])).map String.toList) := by
    rw [netTokens]; simp only [List.map_cons]
  have hnc2 : (netTokens r).map String.toList
      = (("NET" :: "v1" :: "INPUT" :: decTok r.inDim :: layerTokens r.layers).map String.toList) ++ ["END".toList] := by
    rw [netTokens]; simp only [List.cons_append, List.map_cons, List.map_append, List.map_nil]
  have hlt : ltrim (joinSp ((netTokens r).map String.toList)) = joinSp ((netTokens r).map String.toList) := by
    rw [hnc1]; exact ltrim_joinSp _ _ good_NET
  have hrt : rtrim (joinSp ((netTokens r).map String.toList)) = joinSp ((netTokens r).map String.toList) := by
    rw [hnc2]; exact rtrim_joinSp_END _ (by simp)
  have hbs : beforeSemicolon (joinSp ((netTokens r).map String.toList)) = joinSp ((netTokens r).map String.toList) :=
    beforeSemicolon_eq_self _ (fun c hc => (joinSp_notBad hgood c hc).2.2.1)
  apply readStatements_single
  · rw [hcontent]; intro h; exact absurd rfl (joinSp_notBad hgood '\n' h).2.2.2
  · rw [hcontent]; simp only [trimC]; rw [hlt, hrt, hbs, hrt]
  · rw [hcontent, hnc1]; simp [joinSp]
  · rw [hcontent]; apply List.countP_eq_zero.mpr
    intro x hx; simp only [beq_iff_eq]; exact (joinSp_notBad hgood x hx).1
  · rw [hcontent]; apply List.countP_eq_zero.mpr
    intro x hx; simp only [beq_iff_eq]; exact (joinSp_notBad hgood x hx).2.1

/-- **Full round-trip.** For any well-formed `RawNet`, parsing its printed form
recovers exactly the decoded network. Covers `Linear`, `ReLU` and `Flatten`
layers with a single `INPUT` dimension. -/
theorem parseNet_printNet (r : RawNet) (hwf : r.WF) :
    parseNet (printNet r) = .ok (rawToNet r) := by
  obtain ⟨t0, rest0, heq, ht0⟩ := layerTokens_end_cons r.layers
  have hfold : List.foldl (fun acc s => acc ++ ' ' :: s) [] #[(printNet r).toList].toList
             = ' ' :: (printNet r).toList := rfl
  have hnt : netTokens r = "NET" :: "v1" :: "INPUT" :: decTok r.inDim :: t0 :: rest0 := by
    rw [netTokens, heq]
  simp only [parseNet]
  rw [readStatements_printNet r, except_ok_bind, hfold, tokenize_netTokens r, hnt]
  simp only []
  rw [readInputDims_decTok r.inDim t0 rest0 ht0]
  simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
  rw [← heq, parseLayers,
    parseLayersFuel_layerTokens r.layers hwf _ (by
      have := layers_length_le r.layers
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
  simp only [except_ok_bind, rawToNet, Array.empty_append]

end AptpCheck.Ast.Roundtrip
