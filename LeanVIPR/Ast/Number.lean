import Mathlib.Data.Rat.Defs

/-!
# Exact numeric parsing for VIPR

Small total helpers for natural numbers and exact finite decimal rationals.
-/

namespace LeanVIPR.Ast

/-- Split a character list on a separator, retaining empty segments. -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      let rest := splitOnChar sep cs
      if c == sep then
        [] :: rest
      else
        match rest with
        | [] => [[c]]
        | r :: rs => (c :: r) :: rs

/-- Parse a digit list into a natural number. -/
def natOfDigits? (l : List Char) : Option Nat :=
  l.foldl (fun acc c =>
    match acc with
    | some n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none
    | none => none) (some 0)

/-- Parse a signed finite decimal as the exact rational it denotes. -/
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

end LeanVIPR.Ast
