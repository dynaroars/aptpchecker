import AptpCheck.Ast.Sexpr
import AptpCheck.Numeric.Float
import AptpCheck.Model.Network

/-!
# `.net` exact-network parser

Reads the line-oriented `.net` format (see DESIGN.md §5a). Weights are either
`0xXXXXXXXX` float32 bit patterns (decoded exactly via `float32ToRat`) or exact
decimal literals. Comments (`;` to end of line) are stripped by `readStatements`.
-/

namespace AptpCheck.Ast

open AptpCheck.Model

/-- Value of a single hex digit. -/
def hexDigit? (c : Char) : Option Nat :=
  let n := c.toNat
  if '0'.toNat ≤ n ∧ n ≤ '9'.toNat then some (n - '0'.toNat)
  else if 'a'.toNat ≤ n ∧ n ≤ 'f'.toNat then some (10 + n - 'a'.toNat)
  else if 'A'.toNat ≤ n ∧ n ≤ 'F'.toNat then some (10 + n - 'A'.toNat)
  else none

def natOfHex? (l : List Char) : Option Nat :=
  l.foldl (fun acc c =>
    match acc, hexDigit? c with
    | some n, some d => some (n * 16 + d)
    | _, _ => none) (some 0)

/-- Parse one weight token: a `0x…` float32 bit pattern (exact) or a decimal. -/
def parseWeight? (t : String) : Option ℚ :=
  match t.toList with
  | '0' :: 'x' :: rest => (natOfHex? rest).map (fun n => Numeric.float32ToRat (UInt32.ofNat n))
  | '0' :: 'X' :: rest => (natOfHex? rest).map (fun n => Numeric.float32ToRat (UInt32.ofNat n))
  | _ => parseRat? t

/-- Pop `n` weight tokens. -/
def takeWeights : Nat → List String → Except String (Array ℚ × List String)
  | 0, toks => .ok (#[], toks)
  | n + 1, t :: rest =>
      match parseWeight? t with
      | some q => (takeWeights n rest).map (fun (arr, r) => (#[q] ++ arr, r))
      | none => .error s!"bad weight token: {t}"
  | _ + 1, [] => .error "unexpected end of weights"

/-- Read a run of `Nat` tokens (used for the `INPUT` shape). -/
def readInputDims : List String → (List Nat × List String)
  | t :: rest =>
      match natOfDigits? t.toList with
      | some n => let (ds, r) := readInputDims rest; (n :: ds, r)
      | none => ([], t :: rest)
  | [] => ([], [])

/-- Fuel-parameterized layer parser, **structural on `fuel`** (so the kernel gets
equational lemmas and this is a total definition). Each iteration consumes at
least one token, so any `fuel` at least as large as the number of remaining
statements suffices; `parseLayers` supplies `toks.length + 1`, which is always
enough. The `out of fuel` branch is therefore dead for `parseNet` and the result
is identical to the previous `partial def` on every input. -/
def parseLayersFuel : Nat → List String → Array Layer → Except String (Array Layer)
  | _,      "END" :: _, acc => .ok acc
  | fuel+1, "LAYER" :: "ReLU" :: rest, acc => parseLayersFuel fuel rest (acc.push .relu)
  | fuel+1, "LAYER" :: "Flatten" :: rest, acc => parseLayersFuel fuel rest (acc.push .flatten)
  | fuel+1, "LAYER" :: "Linear" :: outS :: inS :: rest, acc => do
      let some outD := natOfDigits? outS.toList | .error s!"bad out dim: {outS}"
      let some inD := natOfDigits? inS.toList | .error s!"bad in dim: {inS}"
      match rest with
      | "W" :: rest1 =>
          let (W, rest2) ← takeWeights (outD * inD) rest1
          match rest2 with
          | "B" :: rest3 =>
              let (b, rest4) ← takeWeights outD rest3
              parseLayersFuel fuel rest4 (acc.push (.linear { outDim := outD, inDim := inD, W := W, b := b }))
          | _ => .error "expected 'B' after weights"
      | _ => .error "expected 'W' after Linear dims"
  | _,      [], _ => .error "unexpected end of file (missing END)"
  | 0,      _, _ => .error "parseLayers: out of fuel"
  | _,      t :: _, _ => .error s!"unexpected token: {t}"

/-- Total layer parser: run `parseLayersFuel` with more fuel than can ever be
consumed (each iteration eats ≥ 1 token). Behaves exactly like the old
`partial def` on all inputs. -/
def parseLayers (toks : List String) (acc : Array Layer) : Except String (Array Layer) :=
  parseLayersFuel (toks.length + 1) toks acc

/-- Parse a `.net` file. -/
def parseNet (content : String) : Except String Network := do
  let stmts ← readStatements content
  let toks := tokenize (stmts.toList.foldl (fun acc s => acc ++ (' ' :: s)) [])
  match toks with
  | "NET" :: _ver :: "INPUT" :: rest =>
      let (dims, rest2) := readInputDims rest
      let inDim := dims.foldl (· * ·) 1
      let layers ← parseLayers rest2 #[]
      .ok { inDim := inDim, layers := layers }
  | _ => .error "expected 'NET <ver> INPUT ...' header"

end AptpCheck.Ast
