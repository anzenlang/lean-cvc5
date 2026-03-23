import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_op_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackOp, hash] tm => do
  let op1 ← tm.mkOp Kind.BITVECTOR_EXTRACT #[31, 1]
  let op2 ← tm.mkOp Kind.BITVECTOR_EXTRACT #[31, 2]
  assertEq op1.hash op1.hash
  assertNe op1.hash op2.hash
  Op.null () |>.hash |> assertEq 0

test![TestApiBlackOp, getKind] tm => do
  let x ← tm.mkOp Kind.BITVECTOR_EXTRACT #[31, 1]
  assertEq Kind.BITVECTOR_EXTRACT x.getKind

test![TestApiBlackOp, isNull] tm => do
  let x := Op.null ()
  assertEq x.isNull true
  let y ← tm.mkOp Kind.BITVECTOR_EXTRACT #[31, 1]
  assertEq y.isNull false
  assertNe x y

test![TestApiBlackOp, opFromKind] tm => do
  tm.mkOp Kind.ADD |> assertOkDiscard
  tm.mkOp Kind.BITVECTOR_EXTRACT |> assertError
    "invalid number of indices for operator BITVECTOR_EXTRACT, expected 2 but got 0."

test![TestApiBlackOp, getNumIndices] tm => do
  -- operators with 0 indices
  let plus ← tm.mkOp Kind.ADD |> assertOk

  assertEq 0 plus.getNumIndices

  -- operators with 1 index
  let divisible ← tm.mkOp Kind.DIVISIBLE #[4]
  let bvRepeat ← tm.mkOp Kind.BITVECTOR_REPEAT #[5]
  let bvZeroExtend ← tm.mkOp Kind.BITVECTOR_ZERO_EXTEND #[6]
  let bvSignExtend ← tm.mkOp Kind.BITVECTOR_SIGN_EXTEND #[7]
  let bvRotateLeft ← tm.mkOp Kind.BITVECTOR_ROTATE_LEFT #[8]
  let bvRotateRight ← tm.mkOp Kind.BITVECTOR_ROTATE_RIGHT #[9]
  let intToBv ← tm.mkOp Kind.INT_TO_BITVECTOR #[10]
  let iand ← tm.mkOp Kind.IAND #[11]
  let fpToUbv ← tm.mkOp Kind.FLOATINGPOINT_TO_UBV #[12]
  let fpToSbv ← tm.mkOp Kind.FLOATINGPOINT_TO_SBV #[13]

  assertEq 1 divisible.getNumIndices
  assertEq 1 bvRepeat.getNumIndices
  assertEq 1 bvZeroExtend.getNumIndices
  assertEq 1 bvSignExtend.getNumIndices
  assertEq 1 bvRotateLeft.getNumIndices
  assertEq 1 bvRotateRight.getNumIndices
  assertEq 1 intToBv.getNumIndices
  assertEq 1 iand.getNumIndices
  assertEq 1 fpToUbv.getNumIndices
  assertEq 1 fpToSbv.getNumIndices

  -- operators with 2 indices
  let bvExtract ← tm.mkOp Kind.BITVECTOR_EXTRACT #[1, 0]
  let toFpFromIeeeBv ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV #[3, 2]
  let toFpFromFp ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_FP #[5, 4]
  let toFpFromReal ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_REAL #[7, 6]
  let toFpFromSbv ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_SBV #[9, 8]
  let toFpFromUbv ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_UBV #[11, 10]
  let regexpLoop ← tm.mkOp Kind.REGEXP_LOOP #[15, 14]

  assertEq 2 bvExtract.getNumIndices
  assertEq 2 toFpFromIeeeBv.getNumIndices
  assertEq 2 toFpFromFp.getNumIndices
  assertEq 2 toFpFromReal.getNumIndices
  assertEq 2 toFpFromSbv.getNumIndices
  assertEq 2 toFpFromUbv.getNumIndices
  assertEq 2 regexpLoop.getNumIndices

  -- operators with n indices
  let indices := #[0, 3, 2, 0, 1, 2];
  let tupleProject ← tm.mkOp Kind.TUPLE_PROJECT indices;
  assertEq tupleProject.getNumIndices indices.size

  let relationProject ← tm.mkOp Kind.RELATION_PROJECT indices
  assertEq relationProject.getNumIndices indices.size

  let tableProject ← tm.mkOp Kind.TABLE_PROJECT indices
  assertEq tableProject.getNumIndices indices.size

test![TestApiBlackOp, subscriptOperator] tm => do
  -- operators with 0 indices
  let plus ← tm.mkOp Kind.ADD |> assertOk

  assertEq false plus.isIndexed
  assertEq 0 plus.getNumIndices
  assertEq none plus[0]?

  -- helper for 1/n-indexed operators
  let check (op : Op) (idx : Nat) (intValue : Int) : cvc5.Env Unit :=
    if _ : idx < op.getNumIndices then
      assertEq op[idx].getIntegerValue! intValue
    else fail "illegal op index `{idx}` for {op}"

  -- operators with 1 index
  let divisible ← tm.mkOp Kind.DIVISIBLE #[4]
  let bvRepeat ← tm.mkOp Kind.BITVECTOR_REPEAT #[5]
  let bvZeroExtend ← tm.mkOp Kind.BITVECTOR_ZERO_EXTEND #[6]
  let bvSignExtend ← tm.mkOp Kind.BITVECTOR_SIGN_EXTEND #[7]
  let bvRotateLeft ← tm.mkOp Kind.BITVECTOR_ROTATE_LEFT #[8]
  let bvRotateRight ← tm.mkOp Kind.BITVECTOR_ROTATE_RIGHT #[9]
  let intToBv ← tm.mkOp Kind.INT_TO_BITVECTOR #[10]
  let iand ← tm.mkOp Kind.IAND #[11]
  let fpToUbv ← tm.mkOp Kind.FLOATINGPOINT_TO_UBV #[12]
  let fpToSbv ← tm.mkOp Kind.FLOATINGPOINT_TO_SBV #[13]

  check divisible 0 4
  check bvRepeat 0 5
  check bvZeroExtend 0 6
  check bvSignExtend 0 7
  check bvRotateLeft 0 8
  check bvRotateRight 0 9
  check intToBv 0 10
  check iand 0 11
  check fpToUbv 0 12
  check fpToSbv 0 13

  -- operators with 2 indices
  let bvExtract ← tm.mkOp Kind.BITVECTOR_EXTRACT #[1, 0]
  let toFpFromIeeeBv ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV #[3, 2]
  let toFpFromFp ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_FP #[5, 4]
  let toFpFromReal ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_REAL #[7, 6]
  let toFpFromSbv ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_SBV #[9, 8]
  let toFpFromUbv ← tm.mkOp Kind.FLOATINGPOINT_TO_FP_FROM_UBV #[11, 10]
  let regexpLoop ← tm.mkOp Kind.REGEXP_LOOP #[15, 14]

  check bvExtract 0 1
  check bvExtract 1 0
  check toFpFromIeeeBv 0 3
  check toFpFromIeeeBv 1 2
  check toFpFromFp 0 5
  check toFpFromFp 1 4
  check toFpFromReal 0 7
  check toFpFromReal 1 6
  check toFpFromSbv 0 9
  check toFpFromSbv 1 8
  check toFpFromUbv 0 11
  check toFpFromUbv 1 10
  check regexpLoop 0 15
  check regexpLoop 1 14

  -- operators with n indices
  let indices := #[0, 3, 2, 0, 1, 2];
  let tupleProject ← tm.mkOp Kind.TUPLE_PROJECT indices;
  for idx in [0 : indices.size] do
    check tupleProject idx indices[idx]!

test![TestApiBlackOp, opScopingToString] tm => do
  let bvRepeatOp ← tm.mkOp Kind.BITVECTOR_REPEAT #[5]
  let opRepr := bvRepeatOp.toString
  assertEq opRepr bvRepeatOp.toString
  -- the assertion above is a tautology:
  have : opRepr = bvRepeatOp.toString := rfl
