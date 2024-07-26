import Test.Init

namespace cvc5.Test

-- #TODO same but without parsing, needs a few more lean-level cvc5 functions

def work : IO Unit := Ctx.run! do
  Ctx.setOption "produce-proofs" "true"

  Ctx.setLogic "QF_LIA"

  let n1 ← Ctx.declareConst "n1" Int
  let n2 ← Ctx.declareConst "n2" Int

  let b ← Ctx.declareConst "b" Bool

  let eq ← Ctx.mkEqual n1 n2
  let neq ← Ctx.mkNot eq
  let ite ← Ctx.mkIte b eq neq

  Ctx.assertFormula ite
  Ctx.assertFormula eq

  match ← Ctx.checkSat? with
  | none =>
    panic! "got a timeout"
  | some false =>
    panic! "unexpected `unsat` result"
  | some true =>
    println! "confirmed `sat` result"

  Ctx.resetAssertions

  let imp1 ← Ctx.mkImplies b eq
  let not_b ← Ctx.mkNot b
  let imp2 ← Ctx.mkImplies not_b neq

  Ctx.assertFormula imp1
  Ctx.assertFormula imp2
  Ctx.assertFormula eq
  Ctx.assertFormula not_b

  match ← Ctx.checkSat? with
  | none => panic! "got a timeout"
  | some false => println! "confirmed `unsat` result"
  | some true => panic! "unexpected `sat` result"

  let proofs ← Ctx.getProof

  println! "proof:"
  for p in proofs do
    println! "- {p.getResult}"

#eval work
