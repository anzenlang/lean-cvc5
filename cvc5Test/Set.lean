import cvc5Test.Init

namespace cvc5.Test

test![FloatingPoint, basic] tm => do
  let mut set ← tm.mkTerm Kind.SET_SINGLETON #[(← tm.mkInteger 3)]
  let isSet := set.isSetValue
  assertTrue isSet
  let setValue ← set.getSetValue
  assertEq "#[3]" (toString setValue)
