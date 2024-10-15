import Cvc5Test.Init

namespace cvc5.Test

/--
error: failed to prove the bit-vector's size is `> 0`
tm : TermManager
n : UInt32
⊢ 0 < n
---
error: cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
test! tm => do
  let mkBvSort (n : UInt32) :=
    tm.mkBitVectorSort n -- cannot prove `0 < n`
  let _ := mkBvSort 0
  let _ := mkBvSort 1

test! do
  Solver.setOption "produce-models" "true"
  |> assertOk
  Solver.setOption "produce-proofs" "true"
  |> assertOk

  -- bad option
  Solver.setOption "does-not-exist" "true"
  |> assertError "unrecognized option: does-not-exist."
  -- bad value
  Solver.setOption "produce-models" "7"
  |> assertError "
Error in option parsing: Argument '7' for bool option produce-models is not a bool constant
  ".trim

  Solver.getProof
  |> assertError "cannot get proof unless in unsat mode."

  let isSat? ← Solver.checkSat?
  assertEq isSat? true "checkSat should be sat"

  -- illegal `setOption`
  Solver.setOption "produce-proofs" "true"
  |> assertError "
invalid call to 'setOption' for option 'produce-proofs', solver is already fully initialized
  ".trim

  -- `getProof` illegal in sat mode
  Solver.getProof
  |> assertError "cannot get proof unless in unsat mode."
