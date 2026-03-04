import cvc5Test.Init

namespace cvc5.Test


def run (tm : TermManager) (val : Int) : Env Unit := do
  let expected := s!"ok: {val}"
  let check {α : Type} [ToString α] : α → IO Unit := assertEq expected ∘ toString
  let term ← tm.mkInteger val
  println! "{term}"
  println! "  isInt32Value := {term.isInt32Value}"
  if term.isInt32Value then
    println! "    → {term.getInt32Value}"
    check term.getInt32Value
  println! "  isUInt32Value := {term.isUInt32Value}"
  if term.isUInt32Value then
    println! "    → {term.getUInt32Value}"
    check term.getUInt32Value
  println! "  isInt64Value  := {term.isInt64Value}"
  if term.isInt64Value then
    println! "    → {term.getInt64Value}"
    check term.getInt64Value
  println! "  isUInt64Value := {term.isUInt64Value}"
  if term.isUInt64Value then
    println! "    → {term.getUInt64Value}"
    check term.getUInt64Value

/-- info:
5
  isInt32Value := true
    → ok: 5
  isUInt32Value := true
    → ok: 5
  isInt64Value  := true
    → ok: 5
  isUInt64Value := true
    → ok: 5
0
  isInt32Value := true
    → ok: 0
  isUInt32Value := true
    → ok: 0
  isInt64Value  := true
    → ok: 0
  isUInt64Value := true
    → ok: 0
(- 7)
  isInt32Value := true
    → ok: -7
  isUInt32Value := false
  isInt64Value  := true
    → ok: -7
  isUInt64Value := false
-/
test![BLah, blah] tm => do
  for val in #[5, 0, -7] do run tm val

/-- info:
4294967295
  isInt32Value := false
  isUInt32Value := true
    → ok: 4294967295
  isInt64Value  := true
    → ok: 4294967295
  isUInt64Value := true
    → ok: 4294967295
4294967300
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := true
    → ok: 4294967300
  isUInt64Value := true
    → ok: 4294967300
-/
test![BLah, blah] tm => do
  let u32Max := 4294967295
  let u32Max' := 4294967300
  for val in #[u32Max, u32Max'] do run tm val

/-- info:
18446744073709551615
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := false
  isUInt64Value := true
    → ok: 18446744073709551615
18446744073709551650
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := false
  isUInt64Value := false
-/
test![BLah, blah] tm => do
  let u64Max := 18_446_744_073_709_551_615
  let u64Max' := 18_446_744_073_709_551_650
  for val in #[u64Max, u64Max'] do run tm val

/-- info:
2147483647
  isInt32Value := true
    → ok: 2147483647
  isUInt32Value := true
    → ok: 2147483647
  isInt64Value  := true
    → ok: 2147483647
  isUInt64Value := true
    → ok: 2147483647
2147483700
  isInt32Value := false
  isUInt32Value := true
    → ok: 2147483700
  isInt64Value  := true
    → ok: 2147483700
  isUInt64Value := true
    → ok: 2147483700
(- 2147483648)
  isInt32Value := true
    → ok: -2147483648
  isUInt32Value := false
  isInt64Value  := true
    → ok: -2147483648
  isUInt64Value := false
(- 2147483700)
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := true
    → ok: -2147483700
  isUInt64Value := false
-/
test![BLah, blah] tm => do
  let i32Max := 2147483647
  let i32Max' := 2147483700
  let i32Min := -2147483648
  let i32Min' := -2147483700
  for val in #[i32Max, i32Max', i32Min, i32Min'] do run tm val

/-- info:
9223372036854775807
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := true
    → ok: 9223372036854775807
  isUInt64Value := true
    → ok: 9223372036854775807
9223372036854775810
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := false
  isUInt64Value := true
    → ok: 9223372036854775810
(- 9223372036854775808)
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := true
    → ok: -9223372036854775808
  isUInt64Value := false
(- 9223372036854775850)
  isInt32Value := false
  isUInt32Value := false
  isInt64Value  := false
  isUInt64Value := false
-/
test![BLah, blah] tm => do
  let i64Min := -9_223_372_036_854_775_808
  let i64Min' := -9_223_372_036_854_775_850
  let i64Max := 9_223_372_036_854_775_807
  let i64Max' := 9_223_372_036_854_775_810
  for val in #[i64Max, i64Max', i64Min, i64Min'] do run tm val
