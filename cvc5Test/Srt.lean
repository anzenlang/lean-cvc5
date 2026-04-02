import cvc5Test.Init



namespace cvc5.Test


test![denullify, test] tm => do
  let bool ← tm.getBooleanSort
  assertEq "Bool" bool.toString
