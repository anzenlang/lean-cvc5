import Test.Init

namespace cvc5.Safe.Test

def work : IO Unit := Smt.run! do
  Smt.setOption "produce-proofs" "true"
  Smt.setOption "produce-models" "true"

  Smt.setLogic "QF_LIA"

  let n1 ← Smt.declareConst "n1" Int
  let n2 ← Smt.declareConst "n2" Int

  let b ← Smt.declareConst "b" Bool

  let eq ← Smt.mkEqual n1 n2
  let neq ← Smt.mkNot eq
  let ite ← Smt.mkIte b eq neq

  println! "assert {ite}"
  Smt.assertFormula ite
  println! "assert {eq}"
  Smt.assertFormula eq

  println! "\nchecksat"
  Smt.checkSat
    (onSat := do
      println! "- confirmed `sat` result"
      let bVal ← Smt.getValue b
      println! "  getValue b := {bVal}"
      let intVals ← Smt.getValues #[n1, n2]
      println! "  getValues #[n1, n2] := {intVals}"
    )

  println! "\n\nreset\n\n"
  Smt.resetAssertions

  let imp1 ← Smt.mkImplies b eq
  let not_b ← Smt.mkNot b
  let imp2 ← Smt.mkImplies not_b neq

  println! "assert {imp1}"
  Smt.assertFormula imp1
  println! "assert {imp2}"
  Smt.assertFormula imp2
  println! "assert {eq}"
  Smt.assertFormula eq
  println! "assert {not_b}"
  Smt.assertFormula not_b

  println! "\nchecksat"
  Smt.checkSat
    (onUnsat := do
      println! "- confirmed `unsat` result"
      let proofs ← Smt.getProof
      println! "  proof :="
      for p in proofs do
        println! "    {p.getResult}"
    )


#eval work
