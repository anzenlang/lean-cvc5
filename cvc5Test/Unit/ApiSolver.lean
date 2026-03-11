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

test![TestApiBlackSolver, pow2Large1] tm solver => do
  -- Based on https://github.com/cvc5/cvc5-projects/issues/371
  let string ← tm.getStringSort
  let int ← tm.getIntegerSort
  let s4 ← tm.mkArraySort string int
  let s7 ← tm.mkArraySort int string
  let t10 ← tm.mkIntegerOfString "68038927088685865242724985643"
  let t74 ← tm.mkIntegerOfString "8416288636405"
  let mut ctors := #[]
  let mut dtConsDecl ← tm.mkDatatypeConstructorDecl "_x109"
  dtConsDecl ← dtConsDecl.addSelector "_x108" s7
  ctors := ctors.push dtConsDecl
  dtConsDecl ← tm.mkDatatypeConstructorDecl "_x113"
  dtConsDecl ← dtConsDecl.addSelector "_x110" s4
  dtConsDecl ← dtConsDecl.addSelector "_x111" int
  dtConsDecl ← dtConsDecl.addSelector "_x112" s7
  ctors := ctors.push dtConsDecl
  let s11 ← solver.declareDatatype "_x107" ctors
  let t82 ← tm.mkConst s11 "_x114"
  let t180 ← tm.mkTerm Kind.POW2 #[t10]
  let t258 ← tm.mkTerm Kind.GEQ #[t74, t180]
  solver.assertFormula t258
  solver.simplify t82 true |> assertError
    "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. \
    Exception occurred in:\n  \
    (int.pow2 68038927088685865242724985643)"

test![TestApiBlackSolver, pow2Large2] tm solver => do
  -- Based on https://github.com/cvc5/cvc5-projects/issues/333
  let t1 ← tm.mkBitVector 63 <| (1 : UInt64) <<< 62
  let t2 ← tm.mkTerm Kind.BITVECTOR_UBV_TO_INT #[t1]
  let t3 ← tm.mkTerm Kind.POW2 #[t2]
  let t4 ← tm.mkTerm Kind.DISTINCT #[t3, t2]
  solver.checkSatAssuming #[t4] |> assertError
    "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. \
    Exception occurred in:\n  \
    (int.pow2 4611686018427387904)"

test![TestApiBlackSolver, pow2Large3] tm solver => do
  -- Based on https://github.com/cvc5/cvc5-projects/issues/339
  let t203 ← tm.mkIntegerOfString "6135470354240554220207"
  let t262 ← tm.mkTerm Kind.POW2 #[t203]
  let t536 ← tm.mkTermOfOp (← tm.mkOp Kind.INT_TO_BITVECTOR #[49]) #[t262]
  -- should not throw an exception, will not simplify
  solver.simplify t536 |> assertOkDiscard

test![TestApiBlackSolver, recoverableException] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst (← tm.getBooleanSort) "x"
  solver.assertFormula (← (← x.eqTerm x).notTerm)
  solver.getValue x |> assertError
    "cannot get value unless after a SAT or UNKNOWN response."

test![TestApiBlackSolver, simplify] tm solver => do
  let int ← tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  let uninterpreted ← tm.mkUninterpretedSort "U"
  let funSort1 ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let funSort2 ← tm.mkFunctionSort #[uninterpreted] int
  let consListSort ← do
    let mut consListSpec ← tm.mkDatatypeDecl "list"
    let mut cons ← tm.mkDatatypeConstructorDecl "cons"
    cons ← cons.addSelector "head" int
    cons ← cons.addSelectorSelf "tail"
    consListSpec ← consListSpec.addConstructor cons
    let nil ← tm.mkDatatypeConstructorDecl "nil"
    consListSpec ← consListSpec.addConstructor nil
    tm.mkDatatypeSort consListSpec

  let x ← tm.mkConst bvSort "x"
  solver.simplify x |> assertOkDiscard
  let a ← tm.mkConst bvSort "a"
  solver.simplify a |> assertOkDiscard
  let b ← tm.mkConst bvSort "b"
  solver.simplify b |> assertOkDiscard
  let tru ← tm.mkTrue
  let x_eq_x ← tm.mkTerm Kind.EQUAL #[x, x]
  assertNe tru x_eq_x
  assertEq tru (← solver.simplify x_eq_x)
  let x_eq_b ← tm.mkTerm Kind.EQUAL #[x, b]
  assertNe tru x_eq_b
  assertNe tru (← solver.simplify x_eq_b)

  let i1 ← tm.mkConst int "i1"
  solver.simplify i1 |> assertOkDiscard
  let i2 ← tm.mkTerm Kind.MULT #[i1, ← tm.mkInteger 23]
  solver.simplify i2 |> assertOkDiscard
  assertNe i1 i2
  assertNe i1 (← solver.simplify i2)
  let i3 ← tm.mkTerm Kind.ADD #[i1, ← tm.mkInteger 0]
  solver.simplify i3 |> assertOkDiscard
  assertNe i1 i3
  assertEq i1 (← solver.simplify i3)

  let consList ← consListSort.getDatatype
  let cons ← consList.getConstructor "cons"
  let nil ← consList.getConstructor "nil"
  let dt1 ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[
    ← cons.getTerm,
    ← tm.mkInteger 0,
    ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[← nil.getTerm],
  ]
  solver.simplify dt1 |> assertOkDiscard
  let dt2 ← tm.mkTerm Kind.APPLY_SELECTOR #[
    ← cons.getSelector "head" >>= DatatypeSelector.getTerm,
    dt1
  ]
  solver.simplify dt2 |> assertOkDiscard

  let b1 ← tm.mkVar bvSort "b1"
  solver.simplify b1 |> assertOkDiscard
  let b2 ← tm.mkVar bvSort "b1"
  solver.simplify b2 |> assertOkDiscard
  let b3 ← tm.mkVar uninterpreted "b3"
  solver.simplify b3 |> assertOkDiscard
  let v1 ← tm.mkVar bvSort "v1"
  solver.simplify v1 |> assertOkDiscard
  let v2 ← tm.mkVar int "v2"
  solver.simplify v2 |> assertOkDiscard
  let f1 ← tm.mkVar funSort1 "f1"
  solver.simplify f1 |> assertOkDiscard
  let f2 ← tm.mkVar funSort2 "f2"
  solver.simplify f2 |> assertOkDiscard
  solver.defineFunsRec #[f1, f2] #[#[b1, b2], #[b3]] #[v1, v2]
  solver.simplify f1 |> assertOkDiscard
  solver.simplify f2 |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.simplify x |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, simplifyApplySubs] tm solver => do
  solver.setOption "incremental" "true"
  let int ← tm.getIntegerSort
  let x ← tm.mkConst int "x"
  let zero ← tm.mkInteger 0
  let eq ← tm.mkTerm Kind.EQUAL #[x, zero]
  solver.assertFormula eq
  solver.checkSat |> assertOkDiscard

  assertEq (← solver.simplify x false) x
  assertEq (← solver.simplify x true) zero

test![TestApiBlackSolver, assertFormula] tm solver => do
  solver.assertFormula (← tm.mkTrue) |> assertOkDiscard
  solver.assertFormula (Term.null ()) |> assertError
    "invalid null argument for 'term'"
  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.assertFormula (← tm.mkTrue) |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, checkSatAssuming] tm solver => do
  solver.setOption "incremental" "false"
  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.checkSatAssuming #[← tm.mkTrue] |> assertError
    "cannot make multiple queries unless incremental solving is enabled (try --incremental)"
  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.checkSatAssuming #[← tm.mkTrue] |> assertError
    "invalid term in 'assumptions' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, checkSatAssuming1] tm solver => do
  let bool ← tm.getBooleanSort
  let x ← tm.mkConst bool "x"
  let y ← tm.mkConst bool "y"
  let z ← tm.mkTerm Kind.AND #[x, y]
  solver.setOption "incremental" "true"
  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.checkSatAssuming #[Term.null ()] |> assertError
    "invalid null term in 'assumptions' at index 0"
  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.checkSatAssuming #[z] |> assertOkDiscard

test![TestApiBlackSolver, checkSatAssuming2] tm solver => do
  solver.setOption "incremental" "true"
  let int ← tm.getIntegerSort
  let bool ← tm.getBooleanSort
  let uninterpreted ← tm.mkUninterpretedSort "U"

  let uToIntSort ← tm.mkFunctionSort #[uninterpreted] int
  let intPredSort ← tm.mkFunctionSort #[int] bool

  let n := Term.null ()
  -- constants
  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  -- functions
  let f ← tm.mkConst uToIntSort "f"
  let p ← tm.mkConst intPredSort "p"
  -- values
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  -- terms
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  -- assertions
  let assertions ← tm.mkTerm Kind.AND #[
    ← tm.mkTerm Kind.LEQ #[zero, f_x], -- `0 ≤ f(x)`
    ← tm.mkTerm Kind.LEQ #[zero, f_y], -- `0 ≤ f(y)`
    ← tm.mkTerm Kind.LEQ #[sum, one], -- `f(x) + f(y) ≤ 1`
    ← p_0.notTerm, -- `¬ p(0)`
    p_f_y, -- `p(f(y))`
  ]

  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.assertFormula assertions
  solver.checkSatAssuming #[← tm.mkTerm Kind.DISTINCT #[x, y]] |> assertOkDiscard
  solver.checkSatAssuming #[← tm.mkFalse, ← tm.mkTerm Kind.DISTINCT #[x, y]] |> assertOkDiscard
  solver.checkSatAssuming #[n] |> assertError
    "invalid null term in 'assumptions' at index 0"
  solver.checkSatAssuming #[n, ← tm.mkTerm Kind.DISTINCT #[x, y]] |> assertError
    "invalid null term in 'assumptions' at index 0"

test![TestApiBlackSolver, declareFunFresh] tm solver => do
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let t1 ← solver.declareFun "b" #[] bool true
  let t2 ← solver.declareFun "b" #[] bool false
  let t3 ← solver.declareFun "b" #[] bool false
  t1 == t2 |> assertFalse
  t1 == t3 |> assertFalse
  t2 == t3 |> assertTrue
  let t4 ← solver.declareFun "c" #[] bool false
  t2 == t4 |> assertFalse
  let t5 ← solver.declareFun "b" #[] int false
  t2 == t5 |> assertFalse

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.declareFun "b" #[] int false |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, declareDatatype] tm solver => do
  let lin ← tm.mkDatatypeConstructorDecl "lin"
  let ctors0 := #[lin]
  solver.declareDatatype "" ctors0 |> assertOkDiscard

  let nil ← tm.mkDatatypeConstructorDecl "nil"
  let ctors1 := #[nil]
  solver.declareDatatype "a" ctors1 |> assertOkDiscard

  let cons ← tm.mkDatatypeConstructorDecl "cons"
  let nil2 ← tm.mkDatatypeConstructorDecl "nil"
  let ctors2 := #[cons, nil2]
  solver.declareDatatype "b" ctors2 |> assertOkDiscard

  let cons2 ← tm.mkDatatypeConstructorDecl "cons"
  let nil3 ← tm.mkDatatypeConstructorDecl "nil"
  let ctors3 := #[cons2, nil3]
  solver.declareDatatype "" ctors3 |> assertOkDiscard

  -- must have at least one constructor
  let mut ctors4 := #[]
  solver.declareDatatype "c" ctors4 |> assertError
    "invalid argument '[]' for 'ctors', \
    expected a datatype declaration with at least one constructor"
  -- constructor may not be reused
  let ctor1 ← tm.mkDatatypeConstructorDecl "_x21"
  let ctor2 ← tm.mkDatatypeConstructorDecl "_x31"
  solver.declareDatatype "_x17" #[ctor1, ctor2] |> assertOkDiscard
  solver.declareDatatype "_x86" #[ctor1, ctor2] |> assertError
    "cannot use a constructor for multiple datatypes"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let nnil ← tm.mkDatatypeConstructorDecl "nil"
  solver'.declareDatatype "a" #[nnil] |> assertError
    "invalid datatype constructor declaration in 'ctorsr' at index 0, \
    expected a datatype constructor declaration associated with \
    the term manager of this solver object"

test![TestApiBlackSolver, declareFun] tm solver => do
  let int ← tm.getIntegerSort
  let uninterpreted ← tm.mkUninterpretedSort "U"
  let bvSort ← tm.mkBitVectorSort 32
  let funSort ← tm.mkFunctionSort #[uninterpreted] int
  solver.declareFun "f1" #[] bvSort |> assertOkDiscard
  solver.declareFun "f3" #[bvSort, int] bvSort |> assertOkDiscard
  solver.declareFun "f2" #[] funSort |> assertError
    "invalid argument '(-> U Int)' for 'sort', expected non-function sort as codomain sort"
  -- functions as arguments is allowed
  solver.declareFun "f4" #[bvSort, funSort] bvSort |> assertOkDiscard
  solver.declareFun "f5" #[bvSort, bvSort] funSort |> assertError
    "invalid argument '(-> U Int)' for 'sort', expected non-function sort as codomain sort"

test![TestApiBlackSolver, declareSort] tm solver => do
  solver.declareSort "s" 0 |> assertOkDiscard
  solver.declareSort "s" 2 |> assertOkDiscard
  solver.declareSort "" 2 |> assertOkDiscard

test![TestApiBlackSolver, declareSortFresh] tm solver => do
  let t1 ← solver.declareSort "b" 0 true
  let t2 ← solver.declareSort "b" 0 false
  let t3 ← solver.declareSort "b" 0 false
  t1 == t2 |> assertFalse
  t1 == t3 |> assertFalse
  t2 == t3 |> assertTrue
  let t4 ← solver.declareSort "c" 0 false
  t2 == t4 |> assertFalse
  let t5 ← solver.declareSort "b" 1 false
  t2 == t5 |> assertFalse

test![TestApiBlackSolver, defineFun] tm solver => do
  let int ← tm.getIntegerSort
  let uninterpreted ← tm.mkUninterpretedSort "U"
  let bvSort ← tm.mkBitVectorSort 32
  let funSort ← tm.mkFunctionSort #[uninterpreted] int
  let b1 ← tm.mkVar bvSort "b1"
  let b2 ← tm.mkVar int "b2"
  let b3 ← tm.mkVar funSort "b3"
  let v1 ← tm.mkConst bvSort "v1"
  let v2 ← tm.mkConst funSort "v2"
  solver.defineFun "f" #[] bvSort v1 |> assertOkDiscard
  solver.defineFun "ff" #[b1, b2] bvSort v1 |> assertOkDiscard
  solver.defineFun "ff" #[v1, b2] bvSort v1 |> assertError
    "invalid bound variable in 'bound_vars' at index 0, expected a bound variable"
  solver.defineFun "fff" #[b1] bvSort v2 |> assertError
    "invalid sort of function body 'v2', expected '(_ BitVec 32)', found '(-> U Int)'"
  solver.defineFun "ffff" #[b1] funSort v2 |> assertError
    "invalid argument '(-> U Int)' for 'sort', expected non-function sort as codomain sort"
  -- b3 has function sort, which is allowed as an argument
  solver.defineFun "fffff" #[b1, b3] bvSort v1 |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let bvSort' ← tm'.mkBitVectorSort 32
  let v1' ← tm'.mkConst bvSort' "v1"
  let b1' ← tm'.mkVar bvSort' "b1"
  let b2' ← tm'.mkVar (← tm'.getIntegerSort) "b2"
  solver'.defineFun "f" #[] bvSort v1' |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFun "f" #[] bvSort' v1 |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1, b2'] bvSort' v1' |> assertError
    "invalid term in 'bound_vars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1', b2] bvSort' v1' |> assertError
    "invalid term in 'bound_vars' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1', b2'] bvSort v1' |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1', b2'] bvSort' v1 |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunGlobal] tm solver => do
  let bool ← tm.getBooleanSort
  let bTrue ← tm.mkBoolean true
  -- `(define-fun f () Bool true)`
  let f ← solver.defineFun "f" #[] bool bTrue true
  let b ← tm.mkVar bool "b"
  -- `(define-fun g (b Bool) Bool b)`
  let g ← solver.defineFun "g" #[b] bool b true

  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat
  solver.resetAssertions
  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.defineFun "f" #[] bool bTrue true |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunRec] tm solver => do
  let int ← tm.getIntegerSort
  let uninterpreted ← tm.mkUninterpretedSort "U"
  let bvSort ← tm.mkBitVectorSort 32
  let funSort1 ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let funSort2 ← tm.mkFunctionSort #[uninterpreted] int
  let b1 ← tm.mkVar bvSort "b1"
  let b11 ← tm.mkVar bvSort "b1"
  let b2 ← tm.mkVar int "b2"
  let b3 ← tm.mkVar funSort2 "b3"
  let v1 ← tm.mkConst bvSort "v1"
  let v2 ← tm.mkConst int "v2"
  let v3 ← tm.mkConst funSort2 "v3"
  let f1 ← tm.mkConst funSort1 "f1"
  let f2 ← tm.mkConst funSort2 "f2"
  let f3 ← tm.mkConst bvSort "f3"
  solver.defineFunRec "f" #[] bvSort v1 |> assertOkDiscard
  solver.defineFunRec "ff" #[b1, b2] bvSort v1 |> assertOkDiscard
  solver.defineFunRecTerm f1 #[b1, b11] v1 |> assertOkDiscard
  solver.defineFunRec "fff" #[b1] bvSort v3 |> assertError
    "invalid sort of function body 'v3', expected '(_ BitVec 32)'"
  solver.defineFunRec "ff" #[b1, v2] bvSort v1 |> assertError
    "invalid bound variable in 'bound_vars' at index 1, expected a bound variable"
  solver.defineFunRec "ffff" #[b1] funSort2 v3 |> assertError
    "invalid argument '(-> U Int)' for 'sort', expected non-function sort as codomain sort"
  -- b3 has function sort, which is allowed as an argument
  solver.defineFunRec "fffff" #[b1, b3] bvSort v1 |> assertOkDiscard
  solver.defineFunRecTerm f1 #[b1] v1 |> assertError
    "invalid size of argument 'bound_vars', expected '2'"
  solver.defineFunRecTerm f1 #[b1, b11] v2 |> assertError
    "invalid sort of function body 'v2', expected '(_ BitVec 32)'"
  solver.defineFunRecTerm f1 #[b1, b11] v3 |> assertError
    "invalid sort of function body 'v3', expected '(_ BitVec 32)'"
  solver.defineFunRecTerm f2 #[b1] v2 |> assertError
    "invalid sort of parameter in 'bound_vars' at index 0, expected sort 'U'"
  solver.defineFunRecTerm f3 #[b1] v1 |> assertError
    "invalid argument 'f3' for 'fun', expected function or nullary symbol"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let bvSort2 ← tm'.mkBitVectorSort 32
  let v12 ← tm'.mkConst bvSort2 "v1"
  let b12 ← tm'.mkVar bvSort2 "b1"
  let b22 ← tm'.mkVar (← tm'.getIntegerSort) "b2"
  solver'.defineFunRec "f" #[] bvSort2 v12 |> assertOkDiscard
  solver'.defineFunRec "ff" #[b12, b22] bvSort2 v12 |> assertOkDiscard
  solver'.defineFunRec "f" #[] bvSort v12 |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFunRec "f" #[] bvSort2 v1 |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b1, b22] bvSort2 v12 |> assertError
    "invalid term in 'bound_vars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b12, b2] bvSort2 v12 |> assertError
    "invalid term in 'bound_vars' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b12, b22] bvSort v12 |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b12, b22] bvSort2 v1 |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunRecWrongLogic] tm solver => do
  solver.setLogic "QF_BV"
  let bvSort ← tm.mkBitVectorSort 32
  let funSort ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let b ← tm.mkVar bvSort "b"
  let v ← tm.mkConst bvSort "v"
  let f ← tm.mkConst funSort "f"
  solver.defineFunRec "f" #[] bvSort v |> assertError
    "recursive function definitions require a logic with quantifiers"
  solver.defineFunRecTerm f #[b, b] v |> assertError
    "recursive function definitions require a logic with quantifiers"

test![TestApiBlackSolver, defineFunRecGlobal] tm solver => do
  let bool ← tm.getBooleanSort
  solver.push
  let bTrue ← tm.mkBoolean true
  -- `(define-fun f () Bool true)`
  let f ← solver.defineFunRec "f" #[] bool bTrue true
  let b ← tm.mkVar bool "b"
  -- `(define-fun g (b Boll) Bool b)`
  let g ← do
    let funSort ← tm.mkFunctionSort #[bool] bool
    solver.defineFunRecTerm (← tm.mkConst funSort "g") #[b] b true

  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat
  solver.pop
  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let bool' ← tm'.getBooleanSort
  let b' ← tm'.mkVar bool' "b"
  let g ← tm.mkConst (← tm.mkFunctionSort #[bool] bool) "g"
  let g' ← tm'.mkConst (← tm'.mkFunctionSort #[bool'] bool') "g"
  -- the original test does not check anything about `solver'.defineFunRecTerm`, it just creates
  solver'.defineFunRecTerm g #[b'] b' true |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.defineFunRecTerm g' #[b] b true |> assertError
    "Given term is not associated with the term manager of this solver"


/-! # Synthesis/sygus -/

test![TestApiBlackSolver, declareSygusVar] tm solver => do
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[int] bool
  let nullSort := cvc5.Sort.null ()

  solver.declareSygusVar "" bool |> assertOkDiscard
  solver.declareSygusVar "" funSort |> assertOkDiscard
  solver.declareSygusVar "b" bool |> assertOkDiscard
  solver.declareSygusVar "" nullSort |> assertError
    "invalid null argument for 'sort'"
  solver.declareSygusVar "a" nullSort |> assertError
    "invalid null argument for 'sort'"

  (← Solver.new tm).declareSygusVar "" bool |> assertError
    "cannot call declareSygusVar unless sygus is enabled (use --sygus)"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "sygus" "true"
  solver'.declareSygusVar "" bool |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, declareSygusVar] tm solver => do
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let boolVar ← tm.mkVar bool
  let intVar ← tm.mkVar int

  solver.mkGrammar #[] #[intVar] |> assertOkDiscard
  solver.mkGrammar #[boolVar] #[intVar] |> assertOkDiscard
  solver.mkGrammar #[] #[] |> assertError
    "invalid size of argument 'ntSymbols', expected a non-empty vector"
  solver.mkGrammar #[] #[nullTerm] |> assertError
    "invalid null term in 'ntSymbols' at index 0"
  solver.mkGrammar #[] #[boolTerm] |> assertError
    "invalid bound variable in 'ntSymbols' at index 0, expected a bound variable"
  solver.mkGrammar #[boolTerm] #[intVar] |> assertError
    "invalid bound variable in 'boundVars' at index 0, expected a bound variable"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let boolVar' ← tm'.mkVar (← tm'.getBooleanSort)
  let intVar' ← tm'.mkVar (← tm'.getIntegerSort)
  solver'.mkGrammar #[boolVar'] #[intVar'] |> assertOkDiscard
  solver'.mkGrammar #[boolVar] #[intVar'] |> assertError
    "invalid term in 'boundVars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.mkGrammar #[boolVar'] #[intVar] |> assertError
    "invalid term in 'ntSymbols' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, synthFun] tm solver => do
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let fls ← tm.mkBoolean false
  let nullTerm := Term.null ()
  let term ← tm.mkVar bool "term"
  let start1 ← tm.mkVar bool "start1"
  let start2 ← tm.mkVar int "start2"

  let mut g1 ← solver.mkGrammar #[term] #[start1]
  solver.synthFun "" #[] bool |> assertOkDiscard
  solver.synthFun "f1" #[term] bool |> assertOkDiscard
  solver.synthFun "f2" #[term] bool g1 |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"
  g1 ← g1.addRule start1 fls

  let mut g2 ← solver.mkGrammar #[term] #[start2]
  g2 ← g2.addRule start2 (← tm.mkInteger 0)

  solver.synthFun "" #[] bool |> assertOkDiscard
  solver.synthFun "f1" #[term] bool |> assertOkDiscard
  solver.synthFun "f2" #[term] bool g1 |> assertOkDiscard

  solver.synthFun "f3" #[nullTerm] bool |> assertError
    "invalid null term in 'boundVars' at index 0"
  solver.synthFun "f4" #[term] (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  solver.synthFun "f6" #[term] bool g2 |> assertError
    "invalid Start symbol for grammar, expected Start's sort to be Bool but found Int"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  let bool2 ← tm2.getBooleanSort
  let term2 ← tm2.mkVar bool2 "term2"
  solver2.synthFun "f1" #[term2] bool |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver2.synthFun "" #[] bool |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver2.synthFun "f1" #[term] bool2 |> assertError
    "invalid term in 'boundVars' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, addSygusConstraint] tm solver => do
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let intTerm ← tm.mkInteger 1

  solver.addSygusConstraint boolTerm |> assertOk
  solver.addSygusConstraint nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.addSygusConstraint intTerm |> assertError
    "invalid argument '1' for 'term', expected boolean term"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  solver2.addSygusConstraint boolTerm |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getSygusConstraints] tm solver => do
  solver.setOption "sygus" "true"
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  solver.addSygusConstraint tru
  solver.addSygusConstraint fls
  assertEq (← solver.getSygusConstraints) #[tru, fls]

test![TestApiBlackSolver, addSygusAssume] tm solver => do
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let intTerm ← tm.mkInteger 1

  solver.addSygusAssume boolTerm |> assertOk
  solver.addSygusAssume nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.addSygusAssume intTerm |> assertError
    "invalid argument '1' for 'term', expected boolean term"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  solver2.addSygusAssume boolTerm |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getSygusAssumptions] tm solver => do
  solver.setOption "sygus" "true"
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  solver.addSygusAssume tru
  solver.addSygusAssume fls
  assertEq (← solver.getSygusAssumptions) #[tru, fls]

test![TestApiBlackSolver, getSygusAssumptions] tm solver => do
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let intTerm ← tm.mkInteger 1
  let bool ← tm.getBooleanSort
  let real ← tm.getRealSort

  let inv ← solver.declareFun "inv" #[real] bool
  let pre ← solver.declareFun "pre" #[real] bool
  let trans ← solver.declareFun "trans" #[real, real] bool
  let post ← solver.declareFun "trans" #[real] bool

  let inv1 ← solver.declareFun "inv1" #[real] real

  let trans1 ← solver.declareFun "trans1" #[bool, real] bool
  let trans2 ← solver.declareFun "trans2" #[real, bool] bool
  let trans3 ← solver.declareFun "trans3" #[real, real] real

  solver.addSygusInvConstraint inv pre trans post |> assertOk

  solver.addSygusInvConstraint nullTerm pre trans post |> assertError
    "invalid null argument for 'inv'"
  solver.addSygusInvConstraint inv nullTerm trans post |> assertError
    "invalid null argument for 'pre'"
  solver.addSygusInvConstraint inv pre nullTerm post |> assertError
    "invalid null argument for 'trans'"
  solver.addSygusInvConstraint inv pre trans nullTerm |> assertError
    "invalid null argument for 'post'"

  solver.addSygusInvConstraint inv1 pre trans post |> assertError
    "invalid argument 'inv1' for 'inv', expected boolean range"

  solver.addSygusInvConstraint inv trans trans post |> assertError
    "expected inv and pre to have the same sort"

  solver.addSygusInvConstraint inv pre intTerm post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre pre post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans1 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans2 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans3 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"

  solver.addSygusInvConstraint inv pre trans trans |> assertError
    "expected inv and post to have the same sort"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "sygus" "true"
  let bool' ← tm'.getBooleanSort
  let real' ← tm'.getRealSort
  let inv' ← solver'.declareFun "inv" #[real'] bool'
  let pre' ← solver'.declareFun "inv" #[real'] bool'
  let trans' ← solver'.declareFun "inv" #[real', real'] bool'
  let post' ← solver'.declareFun "inv" #[real'] bool'
  solver'.addSygusInvConstraint inv' pre' trans' post' |> assertOk
  solver'.addSygusInvConstraint inv pre' trans' post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre trans' post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre' trans post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre' trans' post |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, checkSynth] tm solver => do
  solver.setOption "sygus" "true"
  solver.checkSynth |> assertOkDiscard

test![TestApiBlackSolver, getSynthSolution] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"

  let nullTerm := Term.null ()
  let fls ← tm.mkBoolean false
  let bool ← tm.getBooleanSort
  let f ← solver.synthFun "f" #[] bool

  solver.getSynthSolution f |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution

  solver.getSynthSolution f |> assertOkDiscard
  solver.getSynthSolution f |> assertOkDiscard

  solver.getSynthSolution nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.getSynthSolution fls |> assertError
    "synthesis solution not found for given term"

  (← Solver.new tm).getSynthSolution f |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

test![TestApiBlackSolver, getSynthSolutions] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"

  let nullTerm := Term.null ()
  let fls ← tm.mkBoolean false
  let bool ← tm.getBooleanSort
  let f ← solver.synthFun "f" #[] bool

  solver.getSynthSolutions #[] |> assertError
    "invalid size of argument 'terms', expected non-empty vector"
  solver.getSynthSolutions #[f] |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution

  solver.getSynthSolutions #[f] |> assertOkDiscard
  solver.getSynthSolutions #[f] |> assertOkDiscard

  solver.getSynthSolutions #[] |> assertError
    "invalid size of argument 'terms', expected non-empty vector"
  solver.getSynthSolutions #[nullTerm] |> assertError
    "invalid null term in 'terms' at index 0"
  solver.getSynthSolutions #[fls] |> assertError
    "synthesis solution not found for term at index 0"

  (← Solver.new tm).getSynthSolutions #[f] |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

test![TestApiBlackSolver, checkSynthNext] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let bool ← tm.getBooleanSort
  let f ← solver.synthFun "f" #[] bool

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution
  solver.getSynthSolutions #[f] |> assertOkDiscard
  let synthRes ← solver.checkSynthNext
  assertTrue synthRes.hasSolution
  solver.getSynthSolutions #[f] |> assertOkDiscard

test![TestApiBlackSolver, checkSynthNext2] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  solver.checkSynth |> assertOkDiscard
  solver.checkSynthNext |> assertError
    "cannot check for a next synthesis solution when not solving incrementally (use --incremental)"

test![TestApiBlackSolver, checkSynthNext3] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  solver.checkSynthNext |> assertError
    "Cannot check-synth-next unless immediately preceded \
    by a successful call to check-synth(-next)."

test![TestApiBlackSolver, findSynth] tm solver => do
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let start ← tm.mkVar bool
  let mut grammar ← solver.mkGrammar #[] #[start]
  solver.synthFun "f" #[] bool grammar |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"

  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  grammar ← grammar.addRule start tru
  grammar ← grammar.addRule start fls
  let _f ← solver.synthFun "f" #[] bool grammar

  -- should enumerate based on the grammar of the function to synthesize above
  let term ← solver.findSynth .ENUM
  assertFalse term.isNull
  assertTrue term.getSort.isBoolean

test![TestApiBlackSolver, findSynth2] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let bool ← tm.getBooleanSort
  let start ← tm.mkVar bool
  let mut grammar ← solver.mkGrammar #[] #[start]
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  grammar ← grammar.addRule start tru
  grammar ← grammar.addRule start fls

  -- should enumerate true/false
  let term ← solver.findSynth .ENUM grammar
  assertFalse term.isNull
  assertTrue term.getSort.isBoolean
  let term ← solver.findSynthNext
  assertFalse term.isNull
  assertTrue term.getSort.isBoolean
