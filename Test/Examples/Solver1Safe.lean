import Test.Init

namespace cvc5.Safe.Test

open Smt

def work : IO Unit := Smt.run! .qf_lia do
  setOption "produce-proofs" "true"
  setOption "produce-models" "true"

  let n1 ← declareConst "n1" Int
  let n2 ← declareConst "n2" Int

  let b ← declareConst "b" Bool

  let eq ← mkEqual n1 n2
  let neq ← mkNot eq
  let ite ← mkIte b eq neq

  println! "assert {ite}"
  assertFormula ite
  println! "assert {eq}"
  assertFormula eq

  println! "\nchecksat"
  checkSat
    (onSat := do
      println! "- confirmed `sat` result"
      let bVal ← getValue b
      println! "  getValue b := {bVal}"
      let intVals ← getValues #[n1, n2]
      println! "  getValues #[n1, n2] := {intVals}"
    )

  println! "\n\nreset\n\n"
  resetAssertions

  let imp1 ← mkImplies b eq
  let not_b ← mkNot b
  let imp2 ← mkImplies not_b neq

  println! "assert {imp1}"
  assertFormula imp1
  println! "assert {imp2}"
  assertFormula imp2
  println! "assert {eq}"
  assertFormula eq
  println! "assert {not_b}"
  assertFormula not_b

  println! "\nchecksat"
  checkSat
    (onUnsat := do
      println! "- confirmed `unsat` result"
      let proofs ← Smt.getProof
      println! "  proof :="
      for p in proofs do
        println! "    {p.getResult}"
    )


#eval work
