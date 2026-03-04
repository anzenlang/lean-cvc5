import cvc5Test.Init

namespace cvc5.Test

test![FloatingPoint, basic] tm => do
  let (exp, sig) := (3, 5)
  let bv ← tm.mkBitVector 8
  let fp ← tm.mkFloatingPoint exp sig bv
  let (exp', sig', bv') ← fp.getFloatingPointValue
  assertEq exp exp'
  assertEq sig sig'
  assertEq bv bv'
