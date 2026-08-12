import Mathlib

/-!
# Exact float → rational decoding

A finite IEEE-754 value is exactly a dyadic rational, so network weights read as
32- or 64-bit patterns can be carried into `ℚ` with **zero rounding**. This is the
linchpin that makes the whole checker exact: no step ever uses `Float`.
-/

namespace AptpCheck.Numeric

/-- Decode a 32-bit IEEE-754 (binary32) bit pattern into the exact rational it
denotes. Infinities/NaNs (biased exponent `0xFF`) are not expected in network
weights; they map to `0`. -/
def float32ToRat (w : UInt32) : ℚ :=
  let s : UInt32 := (w >>> 31) &&& 1
  let e : UInt32 := (w >>> 23) &&& 0xFF
  let m : UInt32 := w &&& 0x7FFFFF
  let sign : ℚ := if s == 1 then -1 else 1
  if e == 0 then
    -- subnormal:  (-1)^s · m · 2^(-149)
    sign * (m.toNat : ℚ) * (2 : ℚ) ^ (-149 : ℤ)
  else if e == 0xFF then
    0
  else
    -- normal:  (-1)^s · (2^23 + m) · 2^(e-150)
    sign * ((m.toNat + 2 ^ 23 : ℕ) : ℚ) * (2 : ℚ) ^ ((e.toNat : ℤ) - 150)

/-- Decode a 64-bit IEEE-754 (binary64) bit pattern into the exact rational it
denotes. NaN/∞ (biased exponent `0x7FF`) map to `0`. -/
def float64ToRat (w : UInt64) : ℚ :=
  let s : UInt64 := (w >>> 63) &&& 1
  let e : UInt64 := (w >>> 52) &&& 0x7FF
  let m : UInt64 := w &&& 0xFFFFFFFFFFFFF
  let sign : ℚ := if s == 1 then -1 else 1
  if e == 0 then
    sign * (m.toNat : ℚ) * (2 : ℚ) ^ (-1074 : ℤ)
  else if e == 0x7FF then
    0
  else
    sign * ((m.toNat + 2 ^ 52 : ℕ) : ℚ) * (2 : ℚ) ^ ((e.toNat : ℤ) - 1075)

/-- Sanity: `1.0f` has bit pattern `0x3F800000` and decodes to `1`. -/
example : float32ToRat 0x3F800000 = 1 := by native_decide

/-- Sanity: `-2.0f` has bit pattern `0xC0000000` and decodes to `-2`. -/
example : float32ToRat 0xC0000000 = -2 := by native_decide

/-- Sanity: `0.5f` has bit pattern `0x3F000000` and decodes to `1/2`. -/
example : float32ToRat 0x3F000000 = 1 / 2 := by native_decide

end AptpCheck.Numeric
