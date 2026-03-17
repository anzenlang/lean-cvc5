/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Solver` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_solver_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSolver, declareOracleFunUnsat] tm solver => do
  solver.setOption "oracles" "true"
  let oracle (terms : Array Term) : Env Term := do
    if let some term := terms[0]? then
      if let some val := term.getUInt32Value? then
        return ← val.toNat.succ |> Int.ofNat |> tm.mkInteger
    tm.mkInteger 0
  -- `f` is the function implementing `(lambda ((x Int)) (+ x 1))`
  let f ← solver.declareOracleFun "f" #[int] int oracle
  let three ← tm.mkInteger 3
  let five ← tm.mkInteger 5
  let eq ← tm.mkTerm Kind.EQUAL #[← tm.mkTerm Kind.APPLY_UF #[f, three], five]
  solver.assertFormula eq
  -- `(f 3) = 5`
  assertTrue (← solver.checkSat).isUnsat

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "oracles" "true"
  let int' ← tm'.getIntegerSort
  let oracle' (terms : Array Term) : Env Term := do
    if let some term := terms[0]? then
      if let some val := term.getUInt32Value? then
        return ← val.toNat.succ |> Int.ofNat |> tm'.mkInteger
    tm'.mkInteger 0
  solver'.declareOracleFun "f" #[int'] int oracle' |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.declareOracleFun "f" #[int] int' oracle' |> assertError
    "invalid domain sort in 'sorts' at index 0, \
    expected a sort associated with the term manager of this solver object"

  -- this cannot be caught during declaration, is caught during check-sat
  let f2 ← solver'.declareOracleFun "f2" #[int'] int' oracle
  let eq2 ← tm'.mkTerm Kind.EQUAL #[
    ← tm'.mkTerm Kind.APPLY_UF #[f2, ← tm'.mkInteger 3], ← tm'.mkInteger 5
  ]
  solver'.assertFormula eq2
  solver'.checkSat |> assertError
    "Evaluated an oracle call that is not associated with the term manager of this solver"

  -- added from the original test to check we're handling nested errors properly
  let tm'' ← TermManager.new
  let solver'' ← Solver.new tm''
  solver''.setOption "oracles" "true"
  let int'' ← tm''.getIntegerSort
  let f3 ← solver''.declareOracleFun "f3" #[int''] int''
    fun _ => throw (Error.error "internal failure")
  let eq3 ← tm''.mkTerm Kind.EQUAL #[
    ← tm''.mkTerm Kind.APPLY_UF #[f3, ← tm''.mkInteger 3], ← tm''.mkInteger 5
  ]
  solver''.assertFormula eq3
  solver''.checkSat |> assertError "internal failure"

test![TestApiBlackSolver, declareOracleFunSat] tm solver => do
  solver.setOption "oracles" "true"
  solver.setOption "produce-models" "true"
  -- `f` is the function implementing `(lambda ((x Int)) (% x 10))`
  let f ← solver.declareOracleFun "f" #[int] int fun terms => do
    if let some term := terms[0]? then
      if let some val := term.getUInt32Value? then
        return ← tm.mkInteger (val.toNat % 10)
    tm.mkInteger 0
  let seven ← tm.mkInteger 7
  let x ← tm.mkConst int "x"
  let lb ← tm.mkTerm Kind.GEQ #[x, ← tm.mkInteger 0]
  solver.assertFormula lb
  let ub ← tm.mkTerm Kind.LEQ #[x, ← tm.mkInteger 100]
  solver.assertFormula ub
  let eq ← tm.mkTerm Kind.EQUAL #[← tm.mkTerm Kind.APPLY_UF #[f, x], seven]
  solver.assertFormula eq
  -- `x ≥ 0 ∧ x ≤ 100 ∧ (f x) = 7`
  assertTrue (← solver.checkSat).isSat
  let xval ← solver.getValue x
  assertTrue xval.isUInt32Value
  assertTrue <| xval.getUInt32Value!.toNat % 10 == 7

/-! # TODO

Adding pretty much anything after this point causes the test to crash, usually with code `139`.
-/

-- -- uncomment this to crash
-- #eval do
--   println! "aaaa"

-- -- or this
-- test![TestApiBlackSolver, declareOracleFunSat2] tm solver => do
--   solver.setOption "oracles" "true"
--   solver.setOption "produce-models" "true"
--   -- `eq` is the function implementing `(lambda ((x Int) (y Int)) (= x y))`
--   let eq ← solver.declareOracleFun "eq" #[int, int] bool fun terms => do
--     if let some t1 := terms[0]? then
--       if let some t2 := terms[1]? then
--         return ← tm.mkBoolean (t1 == t2)
--     throw (Error.error "expected exactly two terms")
--   let x ← tm.mkConst int "x"
--   let y ← tm.mkConst int "y"
--   let neq ← tm.mkTerm Kind.NOT #[← tm.mkTerm Kind.APPLY_UF #[eq, x, y]]
--   solver.assertFormula neq
--   -- `(not (eq x y))`
--   assertTrue (← solver.checkSat).isSat
--   let xval ← solver.getValue x
--   let yval ← solver.getValue y
--   assertNe xval yval
