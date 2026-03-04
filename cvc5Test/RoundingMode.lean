import cvc5Test.Init

namespace cvc5.Test

test![RoundingMode, basic] tm => do
  let values := #[
    RoundingMode.ROUND_NEAREST_TIES_TO_EVEN,
    RoundingMode.ROUND_TOWARD_POSITIVE,
    RoundingMode.ROUND_TOWARD_NEGATIVE,
    RoundingMode.ROUND_TOWARD_ZERO,
    RoundingMode.ROUND_NEAREST_TIES_TO_AWAY,
  ]
  for value in values do
    let term ← tm.mkRoundingMode value
    assertTrue term.isRoundingModeValue
    let rm ← term.getRoundingModeValue
    assertEq value rm
