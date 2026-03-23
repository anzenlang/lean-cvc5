# Test files

https://github.com/cvc5/cvc5/tree/main/test/unit/api/cpp


- [x] api_command_black
- [x] api_datatype_black
- [x] api_grammar_black
- [x] api_input_parser_black
- [x] api_kind_black
- [x] api_op_black
- [x] api_parametric_datatype_black
- [x] api_proof_black
- [x] api_proof_rule_black
- [x] api_result_black
- [x] api_skolem_id_black
- [x] api_solver_black
- [x] api_sort_black
- [x] api_sort_kind_black
- [x] api_symbol_manager_black
- [x] api_synth_result_black
- [ ] api_term_black
- [x] api_term_manager_black
- [ ] api_types_black

# Skipped

- statistics
- `OptionInfo`
- `DriverOptions`
- `Plugin`s
- `Statistics`

## Solver

- `getDifficulty`
- `getProof`: missing `modes::ProofComponent` argument
- `proofToString`: missing most of its arguments, mostly formatting stuff
- `getLearnedLiterals`: missing `modes::LearnedLitType` argument
- `addPlugin`: `Plugin` API missing
- `getStatistics`: `Statistics` API missing
- `getOptionInfo`: `OptionInfo` API missing
- `assertionNames` parameter of `Solver.proofToString`
- `declareOracleFun`: implemented but tests crash in a very weird way, see
  `cvc5Test/Unit/ApiSolverOracleFun.lean`

## Notes in C++ API/tests

### API

- `Solver`'s `declareSygusVar`'s documentation seem to be a bad copy-paste.

### Tests

- [part of solver test `defineFunRecGlobal`](https://github.com/cvc5/cvc5/blob/e342ecb325520619db2a1f49e95f96ebca8029f2/test/unit/api/cpp/api_solver_black.cpp#L516-L519)
  seems wrong: it checks `tm.mkFunctionSort #[srt] srt` fails when `srt` is not a sort from `tm`

- [solver test `getUnsatCore2](https://github.com/cvc5/cvc5/blob/204b81e2992419d40f8ce91df4d1b5e2e7f6e0d3/test/unit/api/cpp/api_solver_black.cpp#L815-L822)
  seems wrong: `incremental` should be set to `true`

- [this term test](https://github.com/cvc5/cvc5/blob/78cdc5e7b6d127944f92dba7292335782bd0b03e/test/unit/api/cpp/api_term_black.cpp#L654-L655)
  does not use its `t2`, I'm pretty sure it should be in the assertion instead of `t1`