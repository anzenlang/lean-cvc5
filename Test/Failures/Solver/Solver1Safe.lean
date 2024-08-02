import Test.Init

namespace cvc5.Safe.Test

def work : IO Unit := Smt.run! .qf_lia do
  Smt.setOption "produce-proofs" "true"

  let n1 ← Smt.declareConst "n1" Int
  let n2 ← Smt.declareConst "n2" Int

  let b ← Smt.declareConst "b" Bool

  let badEq ← Smt.mkEqual n1 b
  let badNot ← Smt.mkNot n1
  let badIte1 ← Smt.mkIte n1 n1 n2
  let badIte2 ← Smt.mkIte b n1 b

  let eq ← Smt.mkEqual n1 n2
  let neq ← Smt.mkNot eq
  let ite ← Smt.mkIte b eq neq

  Smt.assertFormula n1

  Smt.getProof

  Smt.getValue b

  Smt.getValues #[n1, n2]
