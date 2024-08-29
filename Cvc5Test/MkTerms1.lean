import Cvc5Test.Init

namespace cvc5.Test

test! tm => do

  let boolKind := Kind.CONST_BOOLEAN

  let (tru, fls) := (
    tm.mkBoolean true,
    tm.mkBoolean false,
  )
  assertEq tru.getKind boolKind
  assertEq tru.getSort.toString "Bool"
  assertEq fls.getKind boolKind
  assertEq fls.getSort.toString "Bool"

  let b ← tru.getBooleanValue |> assertOk
  assertEq b true
  let b ← fls.getBooleanValue |> assertOk
  assertEq b false
  fls.getIntegerValue
  |> assertError "\
invalid argument 'false' for '*d_node', \
expected Term to be an integer value when calling getIntegerValue()\
  "

  let intKind := Kind.CONST_INTEGER

  let (one, three, seven, eleven) := (
    tm.mkInteger! 1,
    tm.mkInteger! 3,
    tm.mkInteger! 7,
    tm.mkInteger! 11,
  )
  assertEq one.getKind intKind
  assertEq one.getSort.toString "Int"
  assertEq three.getKind intKind
  assertEq three.getSort.toString "Int"
  assertEq seven.getKind intKind
  assertEq seven.getSort.toString "Int"
  assertEq eleven.getKind intKind
  assertEq eleven.getSort.toString "Int"

  let val ← one.getIntegerValue |> assertOk
  assertEq val 1
  let val ← eleven.getIntegerValue |> assertOk
  assertEq val 11
  eleven.getBooleanValue
  |> assertError "\
invalid argument '11' for '*d_node', \
expected Term to be a Boolean value when calling getBooleanValue()\
  "
  eleven.getBitVectorValue
  |> assertError "\
invalid argument '11' for '*d_node', \
expected Term to be a bit-vector value when calling getBitVectorValue()\
  "

  let ite1 :=
    tm.mkTerm! Kind.ITE #[fls, three, seven]
  assertEq (toString ite1) "(ite false 3 7)"
  assertEq ite1.getKind Kind.ITE
  assertEq ite1.getSort.toString "Int"

  let eq1 :=
    tm.mkTerm! Kind.EQUAL #[ite1, eleven]
  assertEq eq1.getKind Kind.EQUAL
  assertEq (toString eq1) s!"(= {ite1} 11)"
  assertEq eq1.getSort.toString "Bool"

  let eq1' :=
    tm.mkTerm! Kind.EQUAL #[ite1, eleven, one]
  assertEq (toString eq1') s!"(and (= {ite1} 11) (= 11 1))"
  assertEq eq1'.getKind Kind.AND
  assertEq eq1'.getSort.toString "Bool"

  let ite2 :=
    tm.mkTerm! Kind.ITE #[tru, eq1, fls]
  assertEq (toString ite2) s!"(ite true {eq1} false)"
  assertEq ite2.getKind Kind.ITE
  assertEq ite2.getSort.toString "Bool"

  let ite3 ← ite2.substitute #[]
  assertEq (toString ite3) (toString ite2)
  assertEq ite3.getKind Kind.ITE
  assertEq ite3.getSort.toString "Bool"

  ite2.substitute #[(ite1, fls)]
  |> assertError "expecting terms of the same sort at index 0"

  let ite3 ← ite2.substitute #[(ite1, one)]
  assertEq (toString ite3) "(ite true (= 1 11) false)"
  assertEq ite3.getKind Kind.ITE
  assertEq ite3.getSort.toString "Bool"
  --
  assertEq (toString ite2) s!"(ite true {eq1} false)"
  assertEq ite2.getKind Kind.ITE
  assertEq ite2.getSort.toString "Bool"
