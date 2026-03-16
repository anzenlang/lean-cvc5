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
- `getOptionInfo`: `OptionInfo` API missing

## Notes in C++ API/tests

### API

- `Solver`'s `declareSygusVar`'s documentation seem to be a bad copy-paste.

### Tests

- [part of solver test `defineFunRecGlobal`](https://github.com/cvc5/cvc5/blob/e342ecb325520619db2a1f49e95f96ebca8029f2/test/unit/api/cpp/api_solver_black.cpp#L516-L519)
  seems wrong: it checks `tm.mkFunctionSort #[srt] srt` fails when `srt` is not a sort from `tm`

- [solver test `getUnsatCore2](https://github.com/cvc5/cvc5/blob/204b81e2992419d40f8ce91df4d1b5e2e7f6e0d3/test/unit/api/cpp/api_solver_black.cpp#L815-L822)
  seems wrong: `incremental` should be set to `true`