/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/
import cvc5Test.Init

/-! # Black box testing of the guards of the Lean API functions

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_sort_black.cpp>
-/

namespace cvc5.Test

def createDatatypeSort (tm : TermManager) : Env cvc5.Sort := do
  let mut dtSpec ← tm.mkDatatypeDecl "list"
  let mut cons ← tm.mkDatatypeConstructorDecl "cons"
  cons ← cons.addSelector "head" (← tm.getIntegerSort)
  cons ← cons.addSelectorSelf "tail"
  dtSpec ← dtSpec.addConstructor cons
  let nil ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec ← dtSpec.addConstructor nil
  tm.mkDatatypeSort dtSpec

def createParamDatatypeSort (tm : TermManager) : Env cvc5.Sort := do
  let sort ← tm.mkParamSort "T"
  let mut paramDtSpec ← tm.mkDatatypeDecl "paramList" #[sort]
  let mut paramCons ← tm.mkDatatypeConstructorDecl "cons"
  let mut paramNil ← tm.mkDatatypeConstructorDecl "nil"
  paramCons ← paramCons.addSelector "head" sort
  paramDtSpec ← paramDtSpec.addConstructor paramCons
  paramDtSpec ← paramDtSpec.addConstructor paramNil
  tm.mkDatatypeSort paramDtSpec

test![TestApiBlackSort, hash] tm => do
  assertEq (← tm.getIntegerSort).hash (← tm.getIntegerSort).hash
  assertNe (← tm.getIntegerSort).hash (← tm.getStringSort).hash
  cvc5.Sort.null () |>.hash |> assertEq 0

test![TestApiBlackSort, operatorsComparison] tm => do
  assertFalse <| (← tm.getIntegerSort) == Sort.null ()
  assertTrue <| (← tm.getIntegerSort) != Sort.null ()
  assertFalse <| (← tm.getIntegerSort) < Sort.null ()
  assertFalse <| (← tm.getIntegerSort) ≤ Sort.null ()
  assertTrue <| (← tm.getIntegerSort) > Sort.null ()
  assertTrue <| (← tm.getIntegerSort) ≥ Sort.null ()

test![TestApiBlackSort, getKind] tm => do
  let b ← tm.getBooleanSort
  assertEq (← b.getKind) SortKind.BOOLEAN_SORT
  let dtSort ← createDatatypeSort tm
  assertEq SortKind.DATATYPE_SORT (← dtSort.getKind)
  let r ← tm.getRealSort
  let i ← tm.getIntegerSort
  let arr ← tm.mkArraySort r i
  assertEq SortKind.ARRAY_SORT (← arr.getKind)
  let fp ← tm.mkFloatingPointSort 8 24
  assertEq SortKind.FLOATINGPOINT_SORT (← fp.getKind)
  let bv ← tm.mkBitVectorSort 8
  assertEq SortKind.BITVECTOR_SORT (← bv.getKind)
  let abs ← tm.mkAbstractSort SortKind.BITVECTOR_SORT
  assertEq SortKind.ABSTRACT_SORT (← abs.getKind)
  -- not part of the original test
  let n := cvc5.Sort.null ()
  n.getKind |> assertError
    "invalid call to 'SortKind cvc5::Sort::getKind() const', expected non-null object"

test![TestApiBlackSort, hasGetSymbol] tm => do
  let n := cvc5.Sort.null ()
  let b ← tm.getBooleanSort
  let s0 ← tm.mkParamSort "s0"
  let s1 ← tm.mkParamSort "|s1\\|"

  n.hasSymbol |> assertError
    "invalid call to 'bool cvc5::Sort::hasSymbol() const', expected non-null object"
  assertFalse (← assertOk b.hasSymbol)
  assertTrue (← assertOk s0.hasSymbol)
  assertTrue (← assertOk s1.hasSymbol)

  n.getSymbol |> assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', expected non-null object"
  b.getSymbol |> assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', expected the sort to have a symbol."
  assertFalse (← assertOk b.hasSymbol)
  assertEq "s0" (← assertOk s0.getSymbol)
  assertEq "|s1\\|" (← assertOk s1.getSymbol)

test![TestApiBlackSort, isNull] tm => do
  let mut x := cvc5.Sort.null ()
  assertTrue x.isNull
  x ← tm.getBooleanSort
  assertFalse x.isNull

test![TestApiBlackSort, isBoolean] tm => do
  assertTrue (← tm.getBooleanSort).isBoolean
  cvc5.Sort.null () |>.isBoolean |> assertFalse

test![TestApiBlackSort, isInteger] tm => do
  assertTrue (← tm.getIntegerSort).isInteger
  assertFalse (← tm.getRealSort).isInteger
  cvc5.Sort.null () |>.isInteger |> assertFalse

test![TestApiBlackSort, isReal] tm => do
  assertTrue (← tm.getRealSort).isReal
  assertFalse (← tm.getIntegerSort).isReal
  cvc5.Sort.null () |>.isReal |> assertFalse

test![TestApiBlackSort, isString] tm => do
  assertTrue (← tm.getStringSort).isString
  cvc5.Sort.null () |>.isString |> assertFalse

test![TestApiBlackSort, isRegExp] tm => do
  assertTrue (← tm.getRegExpSort).isRegExp
  cvc5.Sort.null () |>.isRegExp |> assertFalse

test![TestApiBlackSort, isRoundingMode] tm => do
  assertTrue (← tm.getRoundingModeSort).isRoundingMode
  cvc5.Sort.null () |>.isRoundingMode |> assertFalse

test![TestApiBlackSort, isBitVector] tm => do
  assertTrue (← tm.mkBitVectorSort 8).isBitVector
  cvc5.Sort.null () |>.isBitVector |> assertFalse

test![TestApiBlackSort, isFiniteField] tm => do
  assertTrue (← tm.mkFiniteFieldSort 7).isFiniteField
  cvc5.Sort.null () |>.isFiniteField |> assertFalse

test![TestApiBlackSort, isFloatingPoint] tm => do
  assertTrue (← tm.mkFloatingPointSort 8 24).isFloatingPoint
  cvc5.Sort.null () |>.isFloatingPoint |> assertFalse

test![TestApiBlackSort, isDatatype] tm => do
  let dtSort ← createDatatypeSort tm
  assertTrue dtSort.isDatatype
  cvc5.Sort.null () |>.isDatatype |> assertFalse

test![TestApiBlackSort, isDatatypeConstructor] tm => do
  let dtSort ← createDatatypeSort tm
  let dt ← dtSort.getDatatype
  let consSort ← (← dt[0]!.getTerm).getSort
  assertEq none dt[3]?
  assertTrue consSort.isDatatypeConstructor
  cvc5.Sort.null () |>.isDatatypeConstructor |> assertFalse

test![TestApiBlackSort, isDatatypeSelector] tm => do
  let dtSort ← createDatatypeSort tm
  let dt ← dtSort.getDatatype
  let selSort ← (← dt[0]![1]!.getTerm).getSort
  assertEq none dt[0]![2]?
  assertTrue selSort.isDatatypeSelector
  cvc5.Sort.null () |>.isDatatypeSelector |> assertFalse

test![TestApiBlackSort, isDatatypeTester] tm => do
  let dtSort ← createDatatypeSort tm
  let dt ← dtSort.getDatatype
  let testerSort ← (← dt[0]!.getTesterTerm).getSort
  assertEq none dt[3]?
  assertTrue testerSort.isDatatypeTester
  cvc5.Sort.null () |>.isDatatypeTester |> assertFalse

test![TestApiBlackSort, isDatatypeUpdater] tm => do
  let dtSort ← createDatatypeSort tm
  let dt ← dtSort.getDatatype
  let updaterSort ← (← dt[0]![0]!.getUpdaterTerm).getSort
  assertEq none dt[3]?
  assertTrue updaterSort.isDatatypeUpdater
  cvc5.Sort.null () |>.isDatatypeUpdater |> assertFalse

test![TestApiBlackSort, isFunction] tm => do
  assertTrue (← tm.mkFunctionSort #[← tm.getBooleanSort] (← tm.getIntegerSort)).isFunction
  cvc5.Sort.null () |>.isFunction |> assertFalse

test![TestApiBlackSort, isPredicate] tm => do
  assertTrue (← tm.mkPredicateSort #[← tm.getRealSort]).isPredicate
  cvc5.Sort.null () |>.isPredicate |> assertFalse

test![TestApiBlackSort, isTuple] tm => do
  assertTrue (← tm.mkTupleSort #[← tm.getRealSort]).isTuple
  cvc5.Sort.null () |>.isTuple |> assertFalse

test![TestApiBlackSort, isNullable] tm => do
  assertTrue (← tm.mkNullableSort (← tm.getRealSort)).isNullable
  cvc5.Sort.null () |>.isNullable |> assertFalse

test![TestApiBlackSort, isRecord] tm => do
  assertTrue (← tm.mkRecordSort #[("asdf", ← tm.getRealSort)]).isRecord
  cvc5.Sort.null () |>.isRecord |> assertFalse

test![TestApiBlackSort, isArray] tm => do
  assertTrue (← tm.mkArraySort (← tm.getRealSort) (← tm.getIntegerSort)).isArray
  cvc5.Sort.null () |>.isArray |> assertFalse

test![TestApiBlackSort, isSet] tm => do
  assertTrue (← tm.mkSetSort (← tm.getRealSort)).isSet
  cvc5.Sort.null () |>.isSet |> assertFalse

test![TestApiBlackSort, isBag] tm => do
  assertTrue (← tm.mkBagSort (← tm.getRealSort)).isBag
  cvc5.Sort.null () |>.isBag |> assertFalse

test![TestApiBlackSort, isSequence] tm => do
  assertTrue (← tm.mkSequenceSort (← tm.getRealSort)).isSequence
  cvc5.Sort.null () |>.isSequence |> assertFalse

test![TestApiBlackSort, isAbstract] tm => do
  assertTrue (← tm.mkAbstractSort SortKind.BITVECTOR_SORT).isAbstract
  assertFalse (← tm.mkAbstractSort SortKind.ARRAY_SORT).isAbstract
  assertTrue (← tm.mkAbstractSort SortKind.ABSTRACT_SORT).isAbstract
  cvc5.Sort.null () |>.isAbstract |> assertFalse

test![TestApiBlackSort, isUninterpreted] tm => do
  assertTrue (← tm.mkUninterpretedSort "asdf").isUninterpretedSort
  cvc5.Sort.null () |>.isUninterpretedSort |> assertFalse

test![TestApiBlackSort, isUninterpretedSortConstructor] tm => do
  let scSort ← tm.mkUninterpretedSortConstructorSort 1 "asdf"
  assertTrue scSort.isUninterpretedSortConstructor
  let scSort2 ← tm.mkUninterpretedSortConstructorSort 2 "asdf"
  assertTrue scSort2.isUninterpretedSortConstructor

test![TestApiBlackSort, getDatatype] tm => do
  let dTypeSort ← createDatatypeSort tm
  assertOkDiscard dTypeSort.getDatatype
  -- create bv sort, check should fail
  let bvSort ← tm.mkBitVectorSort 32
  assertError "expected datatype sort." bvSort.getDatatype

test![TestApiBlackSort, datatypeSorts] tm => do
  let intSort ← tm.getIntegerSort
  let dTypeSort ← createDatatypeSort tm
  let dt ← dTypeSort.getDatatype
  assertFalse dTypeSort.isDatatypeConstructor
  dTypeSort.getDatatypeConstructorCodomainSort |> assertError "not a constructor sort: list"
  dTypeSort.getDatatypeConstructorDomainSorts |> assertError "not a constructor sort: list"
  dTypeSort.getDatatypeConstructorArity |> assertError "not a constructor sort: list"

  -- get constructor
  let dCons := dt[0]!
  let consTerm ← dCons.getTerm
  let consSort ← consTerm.getSort
  assertTrue consSort.isDatatypeConstructor
  assertFalse consSort.isDatatypeTester
  assertFalse consSort.isDatatypeSelector
  assertEq 2 (← consSort.getDatatypeConstructorArity)
  let consDomSorts ← consSort.getDatatypeConstructorDomainSorts
  assertEq (some intSort) consDomSorts[0]?
  assertEq (some dTypeSort) consDomSorts[1]?
  (← consSort.getDatatypeConstructorCodomainSort) |> assertEq dTypeSort

  -- get tester
  let testerTerm ← dCons.getTesterTerm
  assertTrue (← testerTerm.getSort).isDatatypeTester
  assertEq (← (← testerTerm.getSort).getDatatypeTesterDomainSort) dTypeSort
  let booleanSort ← tm.getBooleanSort
  assertEq (← (← testerTerm.getSort).getDatatypeTesterCodomainSort) booleanSort
  assertError "not a tester sort: Bool" booleanSort.getDatatypeTesterDomainSort
  assertError "not a tester sort: Bool" booleanSort.getDatatypeTesterCodomainSort

  -- get selector
  let dSelTail := dCons[1]!
  let tailTerm ← dSelTail.getTerm
  assertTrue (← tailTerm.getSort).isDatatypeSelector
  (← (← tailTerm.getSort).getDatatypeSelectorDomainSort) |> assertEq dTypeSort
  (← (← tailTerm.getSort).getDatatypeSelectorCodomainSort) |> assertEq dTypeSort
  assertError "not a selector sort: Bool" booleanSort.getDatatypeSelectorDomainSort
  assertError "not a selector sort: Bool" booleanSort.getDatatypeSelectorCodomainSort

test![TestApiBlackSort, instantiate] tm => do
  let int ← tm.getIntegerSort
  -- instantiate parametric datatype, check should not fail
  let paramDTypeSort ← createParamDatatypeSort tm
  assertOkDiscard (paramDTypeSort.instantiate #[int])
  -- instantiate non-parametric datatype sort, check should fail
  let mut dTypeSpec ← tm.mkDatatypeDecl "list"
  let mut cons ← tm.mkDatatypeConstructorDecl "cons"
  cons ← cons.addSelector "head" int
  dTypeSpec ← dTypeSpec.addConstructor cons
  let nil ← tm.mkDatatypeConstructorDecl "nil"
  dTypeSpec ← dTypeSpec.addConstructor nil
  let dTypeSort ← tm.mkDatatypeSort dTypeSpec
  dTypeSort.instantiate #[int] |> assertError
    "expected parametric datatype or sort constructor sort."
  -- instantiate uninterpreted sort constructor
  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 1 "s"
  assertOkDiscard (sortConsSort.instantiate #[← tm.getIntegerSort])

test![TestApiBlackSort, isInstantiated] tm => do
  let paramDTypeSort ← createParamDatatypeSort tm
  assertFalse paramDTypeSort.isInstantiated
  let instParamDTypeSort ← paramDTypeSort.instantiate #[← tm.getIntegerSort]
  assertTrue instParamDTypeSort.isInstantiated

  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 1 "s"
  assertFalse sortConsSort.isInstantiated
  let instSortConsSort ← sortConsSort.instantiate #[← tm.getIntegerSort]
  assertTrue instSortConsSort.isInstantiated

  assertFalse (← tm.getIntegerSort).isInstantiated
  assertFalse (← tm.mkBitVectorSort 32).isInstantiated

test![TestApiBlackSort, getInstantiatedParameters] tm => do
  let intSort ← tm.getIntegerSort
  let realSort ← tm.getRealSort
  let boolSort ← tm.getBooleanSort
  let bvSort ← tm.mkBitVectorSort 8

  -- parametric datatype instantiation
  let p1 ← tm.mkParamSort "p1"
  let p2 ← tm.mkParamSort "p2"
  let mut pSpec ← tm.mkDatatypeDecl "pdtype" #[p1, p2]
  let mut pCons1 ← tm.mkDatatypeConstructorDecl "cons1"
  let mut pCons2 ← tm.mkDatatypeConstructorDecl "cons2"
  let pNil ← tm.mkDatatypeConstructorDecl "nil"
  pCons1 ← pCons1.addSelector "sel" p1
  pCons2 ← pCons2.addSelector "sel" p2
  pSpec ← pSpec.addConstructor pCons1
  pSpec ← pSpec.addConstructor pCons2
  pSpec ← pSpec.addConstructor pNil
  let paramDTypeSort ← tm.mkDatatypeSort pSpec

  assertError "expected instantiated parametric sort" paramDTypeSort.getInstantiatedParameters

  let instParamDTypeSort ← paramDTypeSort.instantiate #[realSort, boolSort]

  let instSorts ← instParamDTypeSort.getInstantiatedParameters
  assertEq (some realSort) instSorts[0]?
  assertEq (some boolSort) instSorts[1]?

  -- uninterpreted sort constructor sort instantiation
  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 4 "s"
  assertError "expected instantiated parametric sort" sortConsSort.getInstantiatedParameters

  let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]

  let instSorts ← instSortConsSort.getInstantiatedParameters
  assertEq (some boolSort) instSorts[0]?
  assertEq (some intSort) instSorts[1]?
  assertEq (some bvSort) instSorts[2]?
  assertEq (some realSort) instSorts[3]?

  assertError "expected instantiated parametric sort" intSort.getInstantiatedParameters
  assertError "expected instantiated parametric sort" bvSort.getInstantiatedParameters

test![TestApiBlackSort, getUninterpretedSortConstructor] tm => do
  let intSort ← tm.getIntegerSort
  let realSort ← tm.getRealSort
  let boolSort ← tm.getBooleanSort
  let bvSort ← tm.mkBitVectorSort 8
  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 4 "s"
  sortConsSort.getUninterpretedSortConstructor
  |> assertError "expected instantiated uninterpreted sort."
  let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]
  assertEq sortConsSort (← instSortConsSort.getUninterpretedSortConstructor)

test![TestApiBlackSort, getFunctionArity] tm => do
  let funSort ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getIntegerSort)
  assertEq 1 (← funSort.getFunctionArity)
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionArity

test![TestApiBlackSort, getFunctionDomainSorts] tm => do
  let funSort ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getIntegerSort)
  assertOkDiscard funSort.getFunctionDomainSorts
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionDomainSorts

test![TestApiBlackSort, getFunctionCodomainSort] tm => do
  let funSort ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getIntegerSort)
  assertOkDiscard funSort.getFunctionCodomainSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort(_ BitVec 32)" bvSort.getFunctionCodomainSort

test![TestApiBlackSort, getArrayIndexSort] tm => do
  let elementSort ← tm.mkBitVectorSort 32
  let indexSort ← tm.mkBitVectorSort 32
  let arraySort ← tm.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayIndexSort
  assertError "not an array sort." indexSort.getArrayIndexSort

test![TestApiBlackSort, getArrayElementSort] tm => do
  let elementSort ← tm.mkBitVectorSort 32
  let indexSort ← tm.mkBitVectorSort 32
  let arraySort ← tm.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayElementSort
  assertError "not an array sort." indexSort.getArrayElementSort

test![TestApiBlackSort, getSetElementSort] tm => do
  let setSort ← tm.mkSetSort (← tm.getIntegerSort)
  let elementSort ← assertOk setSort.getSetElementSort
  assertEq elementSort (← tm.getIntegerSort)
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a set sort." bvSort.getSetElementSort

test![TestApiBlackSort, getBagElementSort] tm => do
  let bagSort ← tm.mkBagSort (← tm.getIntegerSort)
  let elementSort ← assertOk bagSort.getBagElementSort
  assertEq elementSort (← tm.getIntegerSort)
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a bag sort." bvSort.getBagElementSort

test![TestApiBlackSort, getSequenceElementSort] tm => do
  let seqSort ← tm.mkSequenceSort (← tm.getIntegerSort)
  let elementSort ← assertOk seqSort.getSequenceElementSort
  assertEq elementSort (← tm.getIntegerSort)
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a sequence sort." bvSort.getSequenceElementSort

test![TestApiBlackSort, getAbstractedKind] tm => do
  assertEq
    SortKind.BITVECTOR_SORT
    (← (← tm.mkAbstractSort SortKind.BITVECTOR_SORT).getAbstractedKind)
  -- `?Array` is syntax sugar for `(Array ? ?)`, thus the constructed sort is an `Array` sort, not
  -- an abstract sort and its abstract kind cannot be extracted
  assertError "not an abstract sort." (do
    let absSort ← tm.mkAbstractSort SortKind.ARRAY_SORT
    absSort.getAbstractedKind
  )
  assertEq
    SortKind.ABSTRACT_SORT
    (← (← tm.mkAbstractSort SortKind.ABSTRACT_SORT).getAbstractedKind)

test![TestApiBlackSort, getSymbol] tm => do
  let uSort ← tm.mkUninterpretedSort "u"
  assertEq "u" (← uSort.getSymbol)
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorName] tm => do
  let sSort ← tm.mkUninterpretedSortConstructorSort 2 "s"
  assertEq "s" (← sSort.getSymbol)
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorArity] tm => do
  let sSort ← tm.mkUninterpretedSortConstructorSort 2 "s"
  assertEq 2 (← sSort.getUninterpretedSortConstructorArity)
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "not a sort constructor sort."
    bvSort.getUninterpretedSortConstructorArity

test![TestApiBlackSort, getBitVectorSize] tm => do
  let bvSort ← tm.mkBitVectorSort 32
  assertEq 32 (← bvSort.getBitVectorSize)
  let setSort ← tm.mkSetSort (← tm.getIntegerSort)
  assertError "not a bit-vector sort." setSort.getBitVectorSize

test![TestApiBlackSort, getFiniteFieldSize] tm => do
  let ffSort ← tm.mkFiniteFieldSort 31
  assertOkDiscard ffSort.getFiniteFieldSize
  assertEq 31 (← ffSort.getFiniteFieldSize)
  (cvc5.Sort.null ()).getFiniteFieldSize |> assertError
    "invalid call to 'std::string cvc5::Sort::getFiniteFieldSize() const', \
    expected non-null object"

test![TestApiBlackSort, getFloatingPointExponentSize] tm => do
  let fpSort ← tm.mkFloatingPointSort 4 8
  assertEq 4 (← fpSort.getFloatingPointExponentSize)
  let setSort ← tm.mkSetSort (← tm.getIntegerSort)
  assertError "not a floating-point sort." setSort.getFloatingPointExponentSize

test![TestApiBlackSort, getFloatingPointSignificandSize] tm => do
  let fpSort ← tm.mkFloatingPointSort 4 8
  assertEq 8 (← fpSort.getFloatingPointSignificandSize)
  let setSort ← tm.mkSetSort (← tm.getIntegerSort)
  assertError "not a floating-point sort." setSort.getFloatingPointSignificandSize

test![TestApiBlackSort, getDatatypeArity] tm => do
  -- create datatype sort, check should not fail
  let mut dTypeSpec ← tm.mkDatatypeDecl "list"
  let mut cons ← tm.mkDatatypeConstructorDecl "cons"
  cons ← cons.addSelector "head" (← tm.getIntegerSort)
  dTypeSpec ← dTypeSpec.addConstructor cons
  let nil ← tm.mkDatatypeConstructorDecl "nil"
  dTypeSpec ← dTypeSpec.addConstructor nil
  let dTypeSort ← tm.mkDatatypeSort dTypeSpec
  assertOkDiscard dTypeSort.getDatatypeArity
  -- create bv sort, check should fail
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a datatype sort." bvSort.getDatatypeArity

test![TestApiBlackSort, getTupleLength] tm => do
  let tupleSort ← tm.mkTupleSort #[← tm.getIntegerSort, ← tm.getIntegerSort]
  assertEq 2 (← tupleSort.getTupleLength)
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleLength

test![TestApiBlackSort, getTupleSorts] tm => do
  let tupleSort ← tm.mkTupleSort #[← tm.getIntegerSort, ← tm.getIntegerSort]
  assertOkDiscard tupleSort.getTupleSorts
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleSorts

test![TestApiBlackSort, getNullableElementSort] tm => do
  let nullableSort ← tm.mkNullableSort (← tm.getIntegerSort)
  assertOkDiscard nullableSort.getNullableElementSort
  let elementSort ← nullableSort.getNullableElementSort
  assertEq elementSort (← tm.getIntegerSort)
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a nullable sort." bvSort.getNullableElementSort

test![TestApiBlackSort, sortCompare] tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  let bvSort2 ← tm.mkBitVectorSort 32
  assertTrue (bvSort ≥ bvSort2)
  assertTrue (bvSort ≤ bvSort2)
  assertTrue ((intSort > boolSort) ≠ (intSort < boolSort))
  assertTrue ((intSort > bvSort ∨ intSort == bvSort) = (intSort ≥ bvSort))

test![TestApiBlackSort, sortScopedToString] tm => do
  let name := "uninterp-sort"
  let bvSort8 ← tm.mkBitVectorSort 8
  let uSort ← tm.mkUninterpretedSort name
  -- repetition present in the original test
  assertEq "(_ BitVec 8)" bvSort8.toString
  assertEq uSort.toString name
  assertEq "(_ BitVec 8)" bvSort8.toString
  assertEq uSort.toString name

test![TestApiBlackSort, toString] do
  -- useless test here, as `toString` is not expected to fail at all
  assertOkDiscard (return (Sort.null ()).toString)

test![TestApiBlackSort, substitute] tm => do
  let sortVar0 ← tm.mkParamSort "T0"
  let sortVar1 ← tm.mkParamSort "T1"
  let intSort ← tm.getIntegerSort
  let realSort ← tm.getRealSort
  let arraySort0 ← tm.mkArraySort sortVar0 sortVar0
  let arraySort1 ← tm.mkArraySort sortVar0 sortVar1
  -- now create instantiations of the defined sorts
  assertOkDiscard
    (arraySort0.substitute #[sortVar0] #[intSort])
  assertOkDiscard
    (arraySort1.substitute #[sortVar0, sortVar1] #[intSort, realSort])
