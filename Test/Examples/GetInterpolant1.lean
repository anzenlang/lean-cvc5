import Test.Init

namespace cvc5.Test

open Smt

def work : IO Unit := Smt.run! do
  setLogic "QF_LIA"
  setOption "produce-interpolants" "true"

  -- from <https://en.wikipedia.org/wiki/Craig_interpolation#Example>

  let p ← declareConst "p" Bool
  let q ← declareConst "q" Bool
  let r ← declareConst "r" Bool
  let s ← declareConst "s" Bool

  let p_and_q ← mkTerm .AND #[p, q]
  let p_nand_q ← mkTerm .NOT #[p_and_q]
  let nr ← mkTerm .NOT #[r]
  let nr_and_q ← mkTerm .AND #[nr, q]
  let φ ←
    mkTerm .IMPLIES #[p_nand_q, nr_and_q]
  println! "φ = {φ}"

  assertFormula φ

  let s_to_p ← mkTerm .IMPLIES #[s, p]
  let s_to_nr ← mkTerm .IMPLIES #[s, nr]
  let ψ ←
    mkTerm .OR #[s_to_p, s_to_nr]
  println! "ψ = {ψ}"

  let i ← getInterpolant ψ

  println! "interpolant: {i}"


#eval work
