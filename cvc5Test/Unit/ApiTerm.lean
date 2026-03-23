import cvc5Test.Init

/-! # Black box testing of the term manager

- <https://github.com/cvc5/cvc5/blob/e342ecb325520619db2a1f49e95f96ebca8029f2/test/unit/api/cpp/api_term_manager_black.cpp>
-/
namespace cvc5.Test

test![TestApiBlackTerm, equalHash] tm => do
  let uSort ← tm.mkUninterpretedSort "u"
  let x ← tm.mkVar uSort "x"
  let y ← tm.mkVar uSort "y"
  let z := Term.null ()

  assertTrue (x == x)
  assertFalse (x != x)
  assertFalse (x == y)
  assertTrue (x != y)
  assertFalse (x == z)
  assertTrue (x != z)

  assertEq x.hash x.hash
  assertNe x.hash y.hash
  assertEq 0 (Term.null ()).hash

test![TestApiBlackTerm, getId] tm => do
  let n := Term.null ()
  n.getId |> assertError
    "invalid call to 'uint64_t cvc5::Term::getId() const', expected non-null object"
  let x ← tm.mkVar (← tm.getIntegerSort) "x"
  x.getId |> assertOkDiscard
  let y := x
  assertEq (← x.getId) (← y.getId)

test![TestApiBlackTerm, getKind] tm => do
  let uSort ← tm.mkUninterpretedSort "u"
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[uSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  n.getKind |> assertError
    "invalid call to 'Kind cvc5::Term::getKind() const', expected non-null object"
  let x ← tm.mkVar uSort "x"
  x.getKind |> assertOkDiscard
  let y ← tm.mkVar uSort "y"
  y.getKind |> assertOkDiscard

  let f ← tm.mkVar funSort1 "f"
  f.getKind |> assertOkDiscard
  let p ← tm.mkVar funSort2 "p"
  p.getKind |> assertOkDiscard

  let zero ← tm.mkInteger 0
  zero.getKind |> assertOkDiscard

  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.getKind |> assertOkDiscard
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  f_y.getKind |> assertOkDiscard
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  sum.getKind |> assertOkDiscard
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.getKind |> assertOkDiscard
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  p_f_y.getKind |> assertOkDiscard

  let seqSort ← tm.mkSequenceSort intSort
  let s ← tm.mkConst seqSort "s"
  let ss ← tm.mkTerm Kind.SEQ_CONCAT #[s, s]
  assertEq Kind.SEQ_CONCAT (← ss.getKind)

test![TestApiBlackTerm, getSort] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  n.getSort |> assertError
    "invalid call to 'Sort cvc5::Term::getSort() const', expected non-null object"
  let x ← tm.mkVar bvSort "x"
  x.getSort |> assertOkDiscard
  assertEq bvSort (← x.getSort)
  let y ← tm.mkVar bvSort "y"
  y.getSort |> assertOkDiscard
  assertEq bvSort (← y.getSort)

  let f ← tm.mkVar funSort1 "f"
  f.getSort |> assertOkDiscard
  assertEq funSort1 (← f.getSort)
  let p ← tm.mkVar funSort2 "p"
  p.getSort |> assertOkDiscard
  assertEq funSort2 (← p.getSort)

  let zero ← tm.mkInteger 0
  zero.getSort |> assertOkDiscard
  assertEq intSort (← zero.getSort)

  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.getSort |> assertOkDiscard
  assertEq intSort (← f_x.getSort)
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  f_y.getSort |> assertOkDiscard
  assertEq intSort (← f_y.getSort)
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  sum.getSort |> assertOkDiscard
  assertEq intSort (← sum.getSort)
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.getSort |> assertOkDiscard
  assertEq boolSort (← p_0.getSort)
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  p_f_y.getSort |> assertOkDiscard
  assertEq boolSort (← p_f_y.getSort)

test![TestApiBlackTerm, getOp] tm => do
  let intSort ← tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 8
  let arrSort ← tm.mkArraySort bvSort intSort
  let funSort ← tm.mkFunctionSort #[intSort] bvSort

  let x ← tm.mkConst intSort "x"
  let a ← tm.mkConst arrSort "a"
  let b ← tm.mkConst bvSort "b"

  assertFalse x.hasOp
  x.getOp |> assertError "expected Term to have an Op when calling getOp()"

  let ab ← tm.mkTerm Kind.SELECT #[a, b]
  let ext ← tm.mkOp Kind.BITVECTOR_EXTRACT #[4, 0]
  let extb ← tm.mkTermOfOp ext #[b]

  assertTrue ab.hasOp
  assertFalse ab.getOp!.isIndexed
  -- can compare directly to a `Kind` (will invoke `Op` constructor)
  assertTrue extb.hasOp
  assertTrue extb.getOp!.isIndexed
  assertEq extb.getOp! ext

  let bit ← tm.mkOp Kind.BITVECTOR_BIT #[4]
  let bitb ← tm.mkTermOfOp bit #[b]
  assertEq Kind.BITVECTOR_BIT bitb.getKind!
  assertTrue bitb.hasOp
  assertEq bit bitb.getOp!
  assertTrue bitb.getOp!.isIndexed
  assertEq bit.getNumIndices 1
  assertEq (← tm.mkInteger 4) bit[0]!

  let f ← tm.mkConst funSort "f"
  let fx ← tm.mkTerm Kind.APPLY_UF #[f, x]

  assertFalse f.hasOp
  f.getOp |> assertError "expected Term to have an Op when calling getOp()"
  assertTrue fx.hasOp
  let children := fx.getChildren
  -- testing rebuild from op and children
  assertEq fx (← tm.mkTermOfOp fx.getOp! children)

  -- test datatype ops
  let sort ← tm.mkParamSort "T"
  let mut listDecl ← tm.mkDatatypeDecl "paramList" #[sort]
  let mut cons ← tm.mkDatatypeConstructorDecl "cons"
  let mut nil ← tm.mkDatatypeConstructorDecl "nil"
  cons ← cons.addSelector "head" sort
  cons ← cons.addSelectorSelf "tail"
  listDecl ← listDecl.addConstructor cons
  listDecl ← listDecl.addConstructor nil
  let listSort ← tm.mkDatatypeSort listDecl
  let intListSort ← listSort.instantiate #[← tm.getIntegerSort]
  let c ← tm.mkConst intListSort "c"
  let list ← listSort.getDatatype
  -- list datatype constructor and selector operator terms
  let consOpTerm ← (← list.getConstructor "cons").getTerm
  let nilOpTerm ← (← list.getConstructor "nil").getTerm
  let headOpTerm ← do
    let cs ← list.getConstructor "cons"
    let hd ← cs.getSelector "head"
    hd.getTerm
  let tailOpTerm ← do
    let cs ← list.getConstructor "cons"
    let hd ← cs.getSelector "tail"
    hd.getTerm

  let nilTerm ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[nilOpTerm]
  let consTerm ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[consOpTerm, ← tm.mkInteger 0, nilTerm]
  let headTerm ← tm.mkTerm Kind.APPLY_SELECTOR #[headOpTerm, consTerm]
  let tailTerm ← tm.mkTerm Kind.APPLY_SELECTOR #[tailOpTerm, consTerm]

  assertFalse c.hasOp
  assertTrue nilTerm.hasOp
  assertTrue consTerm.hasOp
  assertTrue headTerm.hasOp
  assertTrue tailTerm.hasOp

  -- test rebuilding
  let children := headTerm.getChildren
  assertEq headTerm (← tm.mkTermOfOp headTerm.getOp! children)

test![TestApiBlackTerm, hasGetSymbol] tm => do
  let n := Term.null ()
  let t ← tm.mkBoolean true
  let c ← tm.mkConst (← tm.getBooleanSort) "|\\|"

  n.hasSymbol |> assertError
    "invalid call to 'bool cvc5::Term::hasSymbol() const', expected non-null object"
  assertFalse (← t.hasSymbol)
  assertTrue (← c.hasSymbol)

  n.getSymbol |> assertError
    "invalid call to 'std::string cvc5::Term::getSymbol() const', expected non-null object"
  t.getSymbol |> assertError
    "invalid call to 'std::string cvc5::Term::getSymbol() const', \
    expected the term to have a symbol."
  assertEq "|\\|" (← c.getSymbol)

test![TestApiBlackTerm, isNull] tm => do
  let mut x := Term.null ()
  assertTrue x.isNull
  x ← tm.mkVar (← tm.mkBitVectorSort 4) "x"
  assertFalse x.isNull

test![TestApiBlackTerm, notTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  Term.null () |>.notTerm |> assertError
    "invalid call to 'Term cvc5::Term::notTerm() const', expected non-null object"
  let b ← tm.mkTrue
  b.notTerm |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.notTerm |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.notTerm |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.notTerm |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.notTerm |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.notTerm |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.notTerm |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.notTerm |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.notTerm |> assertOkDiscard

test![TestApiBlackTerm, andTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.andTerm b |> assertError
    "invalid call to 'Term cvc5::Term::andTerm(const Term &) const', expected non-null object"
  b.andTerm n |> assertError "invalid null argument for 't'"
  b.andTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.andTerm b |> assertError "expecting a Boolean subexpression"
  x.andTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.andTerm b |> assertError "expecting a Boolean subexpression"
  f.andTerm x |> assertError "expecting a Boolean subexpression"
  f.andTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.andTerm b |> assertError "expecting a Boolean subexpression"
  p.andTerm x |> assertError "expecting a Boolean subexpression"
  p.andTerm f |> assertError "expecting a Boolean subexpression"
  p.andTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.andTerm b |> assertError "expecting a Boolean subexpression"
  zero.andTerm x |> assertError "expecting a Boolean subexpression"
  zero.andTerm f |> assertError "expecting a Boolean subexpression"
  zero.andTerm p |> assertError "expecting a Boolean subexpression"
  zero.andTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.andTerm b |> assertError "expecting a Boolean subexpression"
  f_x.andTerm x |> assertError "expecting a Boolean subexpression"
  f_x.andTerm f |> assertError "expecting a Boolean subexpression"
  f_x.andTerm p |> assertError "expecting a Boolean subexpression"
  f_x.andTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.andTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.andTerm b |> assertError "expecting a Boolean subexpression"
  sum.andTerm x |> assertError "expecting a Boolean subexpression"
  sum.andTerm f |> assertError "expecting a Boolean subexpression"
  sum.andTerm p |> assertError "expecting a Boolean subexpression"
  sum.andTerm zero |> assertError "expecting a Boolean subexpression"
  sum.andTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.andTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.andTerm b |> assertOkDiscard
  p_0.andTerm x |> assertError "expecting a Boolean subexpression"
  p_0.andTerm f |> assertError "expecting a Boolean subexpression"
  p_0.andTerm p |> assertError "expecting a Boolean subexpression"
  p_0.andTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.andTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.andTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.andTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.andTerm b |> assertOkDiscard
  p_f_x.andTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm p_0 |> assertOkDiscard
  p_f_x.andTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, orTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.orTerm b |> assertError
    "invalid call to 'Term cvc5::Term::orTerm(const Term &) const', expected non-null object"
  b.orTerm n |> assertError "invalid null argument for 't'"
  b.orTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.orTerm b |> assertError "expecting a Boolean subexpression"
  x.orTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.orTerm b |> assertError "expecting a Boolean subexpression"
  f.orTerm x |> assertError "expecting a Boolean subexpression"
  f.orTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.orTerm b |> assertError "expecting a Boolean subexpression"
  p.orTerm x |> assertError "expecting a Boolean subexpression"
  p.orTerm f |> assertError "expecting a Boolean subexpression"
  p.orTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.orTerm b |> assertError "expecting a Boolean subexpression"
  zero.orTerm x |> assertError "expecting a Boolean subexpression"
  zero.orTerm f |> assertError "expecting a Boolean subexpression"
  zero.orTerm p |> assertError "expecting a Boolean subexpression"
  zero.orTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.orTerm b |> assertError "expecting a Boolean subexpression"
  f_x.orTerm x |> assertError "expecting a Boolean subexpression"
  f_x.orTerm f |> assertError "expecting a Boolean subexpression"
  f_x.orTerm p |> assertError "expecting a Boolean subexpression"
  f_x.orTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.orTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.orTerm b |> assertError "expecting a Boolean subexpression"
  sum.orTerm x |> assertError "expecting a Boolean subexpression"
  sum.orTerm f |> assertError "expecting a Boolean subexpression"
  sum.orTerm p |> assertError "expecting a Boolean subexpression"
  sum.orTerm zero |> assertError "expecting a Boolean subexpression"
  sum.orTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.orTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.orTerm b |> assertOkDiscard
  p_0.orTerm x |> assertError "expecting a Boolean subexpression"
  p_0.orTerm f |> assertError "expecting a Boolean subexpression"
  p_0.orTerm p |> assertError "expecting a Boolean subexpression"
  p_0.orTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.orTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.orTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.orTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.orTerm b |> assertOkDiscard
  p_f_x.orTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm p_0 |> assertOkDiscard
  p_f_x.orTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, xorTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.xorTerm b |> assertError
    "invalid call to 'Term cvc5::Term::xorTerm(const Term &) const', expected non-null object"
  b.xorTerm n |> assertError "invalid null argument for 't'"
  b.xorTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.xorTerm b |> assertError "expecting a Boolean subexpression"
  x.xorTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.xorTerm b |> assertError "expecting a Boolean subexpression"
  f.xorTerm x |> assertError "expecting a Boolean subexpression"
  f.xorTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.xorTerm b |> assertError "expecting a Boolean subexpression"
  p.xorTerm x |> assertError "expecting a Boolean subexpression"
  p.xorTerm f |> assertError "expecting a Boolean subexpression"
  p.xorTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.xorTerm b |> assertError "expecting a Boolean subexpression"
  zero.xorTerm x |> assertError "expecting a Boolean subexpression"
  zero.xorTerm f |> assertError "expecting a Boolean subexpression"
  zero.xorTerm p |> assertError "expecting a Boolean subexpression"
  zero.xorTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.xorTerm b |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm x |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm f |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm p |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.xorTerm b |> assertError "expecting a Boolean subexpression"
  sum.xorTerm x |> assertError "expecting a Boolean subexpression"
  sum.xorTerm f |> assertError "expecting a Boolean subexpression"
  sum.xorTerm p |> assertError "expecting a Boolean subexpression"
  sum.xorTerm zero |> assertError "expecting a Boolean subexpression"
  sum.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.xorTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.xorTerm b |> assertOkDiscard
  p_0.xorTerm x |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm f |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm p |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.xorTerm b |> assertOkDiscard
  p_f_x.xorTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm p_0 |> assertOkDiscard
  p_f_x.xorTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, eqTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.eqTerm b |> assertError
    "invalid call to 'Term cvc5::Term::eqTerm(const Term &) const', expected non-null object"
  b.eqTerm n |> assertError "invalid null argument for 't'"
  b.eqTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= x true)\nType 1: (_ BitVec 8)\nType 2: Bool\n"
  x.eqTerm x |> assertOkDiscard
  let f ← tm.mkVar funSort1 "f"
  f.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= f true)\nType 1: (-> (_ BitVec 8) Int)\nType 2: Bool\n"
  f.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= f x)\nType 1: (-> (_ BitVec 8) Int)\nType 2: (_ BitVec 8)\n"
  f.eqTerm f |> assertOkDiscard
  let p ← tm.mkVar funSort2 "p"
  p.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= p true)\nType 1: (-> Int Bool)\nType 2: Bool\n"
  p.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= p x)\nType 1: (-> Int Bool)\nType 2: (_ BitVec 8)\n"
  p.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= p f)\nType 1: (-> Int Bool)\nType 2: (-> (_ BitVec 8) Int)\n"
  p.eqTerm p |> assertOkDiscard
  let zero ← tm.mkInteger 0
  zero.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 true)\nType 1: Int\nType 2: Bool\n"
  zero.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 x)\nType 1: Int\nType 2: (_ BitVec 8)\n"
  zero.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 f)\nType 1: Int\nType 2: (-> (_ BitVec 8) Int)\n"
  zero.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 p)\nType 1: Int\nType 2: (-> Int Bool)\n"
  zero.eqTerm zero |> assertOkDiscard
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) true)\nType 1: Int\nType 2: Bool"
  f_x.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) x)\nType 1: Int\nType 2: (_ BitVec 8)\n"
  f_x.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) f)\nType 1: Int\nType 2: (-> (_ BitVec 8) Int)\n"
  f_x.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) p)\nType 1: Int\nType 2: (-> Int Bool)\n"
  f_x.eqTerm zero |> assertOkDiscard
  f_x.eqTerm f_x |> assertOkDiscard
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) true))\nType 1: Int\nType 2: Bool\n"
  sum.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) x))\nType 1: Int\nType 2: (_ BitVec 8)\n"
  sum.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) f))\nType 1: Int\n\
    Type 2: (-> (_ BitVec 8) Int)\n"
  sum.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) p))\nType 1: Int\nType 2: (-> Int Bool)\n"
  sum.eqTerm zero |> assertOkDiscard
  sum.eqTerm f_x |> assertOkDiscard
  sum.eqTerm sum |> assertOkDiscard
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.eqTerm b |> assertOkDiscard
  p_0.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) x)\nType 1: Bool\nType 2: (_ BitVec 8)\n"
  p_0.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) f)\nType 1: Bool\nType 2: (-> (_ BitVec 8) Int)\n"
  p_0.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) p)\nType 1: Bool\nType 2: (-> Int Bool)\n"
  p_0.eqTerm zero |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) 0)\nType 1: Bool\nType 2: Int\n"
  p_0.eqTerm f_x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) (f x))\nType 1: Bool\nType 2: Int\n"
  p_0.eqTerm sum |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (p 0) (+ _let_1 _let_1)))\nType 1: Bool\nType 2: Int\n"
  p_0.eqTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.eqTerm b |> assertOkDiscard
  p_f_x.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) x)\nType 1: Bool\nType 2: (_ BitVec 8)\n"
  p_f_x.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) f)\nType 1: Bool\nType 2: (-> (_ BitVec 8) Int)\n"
  p_f_x.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) p)\nType 1: Bool\nType 2: (-> Int Bool)\n"
  p_f_x.eqTerm zero |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) 0)\nType 1: Bool\nType 2: Int\n"
  p_f_x.eqTerm f_x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (p _let_1) _let_1))\nType 1: Bool\nType 2: Int\n"
  p_f_x.eqTerm sum |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (p _let_1) (+ _let_1 _let_1)))\nType 1: Bool\nType 2: Int\n"
  p_f_x.eqTerm p_0 |> assertOkDiscard
  p_f_x.eqTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, impTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.impTerm b |> assertError
    "invalid call to 'Term cvc5::Term::impTerm(const Term &) const', expected non-null object"
  b.impTerm n |> assertError "invalid null argument for 't'"
  b.impTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.impTerm b |> assertError "expecting a Boolean subexpression"
  x.impTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.impTerm b |> assertError "expecting a Boolean subexpression"
  f.impTerm x |> assertError "expecting a Boolean subexpression"
  f.impTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.impTerm b |> assertError "expecting a Boolean subexpression"
  p.impTerm x |> assertError "expecting a Boolean subexpression"
  p.impTerm f |> assertError "expecting a Boolean subexpression"
  p.impTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.impTerm b |> assertError "expecting a Boolean subexpression"
  zero.impTerm x |> assertError "expecting a Boolean subexpression"
  zero.impTerm f |> assertError "expecting a Boolean subexpression"
  zero.impTerm p |> assertError "expecting a Boolean subexpression"
  zero.impTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.impTerm b |> assertError "expecting a Boolean subexpression"
  f_x.impTerm x |> assertError "expecting a Boolean subexpression"
  f_x.impTerm f |> assertError "expecting a Boolean subexpression"
  f_x.impTerm p |> assertError "expecting a Boolean subexpression"
  f_x.impTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.impTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.impTerm b |> assertError "expecting a Boolean subexpression"
  sum.impTerm x |> assertError "expecting a Boolean subexpression"
  sum.impTerm f |> assertError "expecting a Boolean subexpression"
  sum.impTerm p |> assertError "expecting a Boolean subexpression"
  sum.impTerm zero |> assertError "expecting a Boolean subexpression"
  sum.impTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.impTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.impTerm b |> assertOkDiscard
  p_0.impTerm x |> assertError "expecting a Boolean subexpression"
  p_0.impTerm f |> assertError "expecting a Boolean subexpression"
  p_0.impTerm p |> assertError "expecting a Boolean subexpression"
  p_0.impTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.impTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.impTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.impTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.impTerm b |> assertOkDiscard
  p_f_x.impTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm p_0 |> assertOkDiscard
  p_f_x.impTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, iteTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.iteTerm b b |> assertError
    "invalid call to 'Term cvc5::Term::iteTerm(const Term &, const Term &) const', \
    expected non-null object"
  b.iteTerm n b |> assertError "invalid null argument for 'then_t'"
  b.iteTerm b n |> assertError "invalid null argument for 'else_t'"
  b.iteTerm b b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  b.iteTerm x x |> assertOkDiscard
  b.iteTerm b b |> assertOkDiscard -- also tested twice in the original test
  b.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  x.iteTerm x x |> assertError "condition of ITE is not Boolean"
  x.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let f ← tm.mkVar funSort1 "f"
  f.iteTerm b b |> assertError "condition of ITE is not Boolean"
  x.iteTerm b x |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: x\nits type   : (_ BitVec 8)\n"
  let p ← tm.mkVar funSort2 "p"
  p.iteTerm b b |> assertError "condition of ITE is not Boolean"
  p.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let zero ← tm.mkInteger 0
  zero.iteTerm x x |> assertError "condition of ITE is not Boolean"
  zero.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.iteTerm b b |> assertError "condition of ITE is not Boolean"
  f_x.iteTerm b x |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: x\nits type   : (_ BitVec 8)\n"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.iteTerm x x |> assertError "condition of ITE is not Boolean"
  sum.iteTerm b x |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: x\nits type   : (_ BitVec 8)\n"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.iteTerm b b |> assertOkDiscard
  p_0.iteTerm x x |> assertOkDiscard
  p_0.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.iteTerm b b |> assertOkDiscard
  p_f_x.iteTerm x x |> assertOkDiscard
  p_f_x.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"

test![TestApiBlackTerm, termAssignment] tm => do
  let t1 ← tm.mkInteger 1
  let mut t2 := t1
  t2 ← tm.mkInteger 2
  assertEq t1 (← tm.mkInteger 1)
  -- censoring *unused* warning
  let _ := t2

test![TestApiBlackTerm, termCompare] tm => do
  let t1 ← tm.mkInteger 1
  let t2 ← tm.mkTerm Kind.ADD #[← tm.mkInteger 2, ← tm.mkInteger 2]
  let t3 ← tm.mkTerm Kind.ADD #[← tm.mkInteger 2, ← tm.mkInteger 2]
  assertTrue (t2 ≥ t3)
  assertTrue (t2 ≤ t3)
  assertTrue <| (t1 > t2) != (t1 < t2)
  assertTrue <| (t1 > t2 || t1 == t2) == (t1 ≥ t2)

-- test![TestApiBlackTerm, termChildren] tm => do
--   -- simple term `2+3`
--   let two ← tm.mkInteger 2
--   let t1 ← tm.mkTerm Kind.ADD #[two, ← tm.mkInteger 3]
--   assertEq two t1[0]!
--   assertEq 2 t1.getNumChildren
--   let n := Term.null ()
--   n.getNumChildren |> assertError
