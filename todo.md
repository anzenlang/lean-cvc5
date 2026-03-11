# Skipped

- statistics
- `OptionInfo`
- `DriverOptions`
- `Plugin`
- `Statistics`

## Solver

- `getDifficulty`
- `getProof`: missing `modes::ProofComponent` argument
- `proofToString`: missing most of its arguments, mostly formatting stuff
- `getLearnedLiterals`: missing `modes::LearnedLitType` argument
- `addPlugin`: `Plugin` API missing
- `getStatistics`: `Statistics` API missing

## Notes

Cvc5 `Solver`'s `declareSygusVar`'s documentation seem to be a bad copy-paste.