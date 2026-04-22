import cvc5
import cvc5Test.Init



namespace cvc5



structure TermsAndIndices (α β : Type) where
  terms : α
  indices : β

namespace Kind

abbrev Sig : Kind → Type
| .EQUAL | .DISTINCT
| .APPLY_UF
| .AND | .IMPLIES | .OR | .XOR | .ADD | .MULT | .SUB
| .DIVISION | .DIVISION_TOTAL | .INTS_DIVISION | .INTS_DIVISION_TOTAL
| .BITVECTOR_CONCAT | .BITVECTOR_AND | .BITVECTOR_OR | .BITVECTOR_XOR
| .BITVECTOR_MULT | .BITVECTOR_ADD | .BITVECTOR_SUB
| .FINITE_FIELD_ADD | .FINITE_FIELD_BITSUM | .FINITE_FIELD_MULT
=> Term × Term × Array Term

| .LT | .LEQ | .GT | .GEQ
-- -- pretends to be
-- => Term × Term × Array Term
-- but seems to actually be
=> Term × Term

| .SEXPR
| .BITVECTOR_FROM_BOOLS
=> Term × Array Term

| .NOT
| .POW2 | .LOG2
| .NEG
| .ABS
| .EXPONENTIAL
| .SINE | .COSINE | .TANGENT | .COSECANT | .SECANT | .COTANGENT
| .ARCSINE | .ARCCOSINE | .ARCTANGENT | .ARCCOSECANT | .ARCSECANT | .ARCCOTANGENT
| .SQRT
| .DIVISIBLE
| .IS_INTEGER | .TO_INTEGER
| .TO_REAL
| .BITVECTOR_NOT | .BITVECTOR_NEG | .BITVECTOR_REDOR | .BITVECTOR_REDAND | .BITVECTOR_NEGO
| .BITVECTOR_TO_NAT | .BITVECTOR_UBV_TO_INT | .BITVECTOR_SBV_TO_INT
| .FINITE_FIELD_NEG
| .FLOATINGPOINT_ABS | .FLOATINGPOINT_NEG
| .FLOATINGPOINT_IS_NORMAL | .FLOATINGPOINT_IS_SUBNORMAL | .FLOATINGPOINT_IS_ZERO
| .FLOATINGPOINT_IS_INF | .FLOATINGPOINT_IS_NAN | .FLOATINGPOINT_IS_NEG | .FLOATINGPOINT_IS_POS
| .FLOATINGPOINT_TO_REAL
=> Term

| .LAMBDA
| .HO_APPLY
| .IAND
| .INTS_MODULUS
| .INTS_MODULUS_TOTAL
| .POW
| .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR | .BITVECTOR_COMP
| .BITVECTOR_UDIV | .BITVECTOR_UREM
| .BITVECTOR_SDIV | .BITVECTOR_SREM | .BITVECTOR_SMOD
| .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR
| .BITVECTOR_ULT | .BITVECTOR_ULE | .BITVECTOR_UGT | .BITVECTOR_UGE
| .BITVECTOR_SLT | .BITVECTOR_SLE | .BITVECTOR_SGT | .BITVECTOR_SGE
| .BITVECTOR_ULTBV | .BITVECTOR_SLTBV
| .BITVECTOR_UADDO | .BITVECTOR_SADDO | .BITVECTOR_UMULO | .BITVECTOR_SMULO
| .BITVECTOR_USUBO | .BITVECTOR_SSUBO | .BITVECTOR_SDIVO
| .FLOATINGPOINT_EQ | .FLOATINGPOINT_REM | .FLOATINGPOINT_RTI
| .FLOATINGPOINT_LEQ | .FLOATINGPOINT_LT | .FLOATINGPOINT_GEQ | .FLOATINGPOINT_GT
| .SELECT
| .CONST_ARRAY
=> Term × Term

| .WITNESS
| .ITE
| .PIAND
| .BITVECTOR_ITE
| .FLOATINGPOINT_FP
| .STORE
=> Term × Term × Term

| .FLOATINGPOINT_SQRT | .FLOATINGPOINT_MIN | .FLOATINGPOINT_MAX
=> RoundingMode × Term

| .FLOATINGPOINT_ADD | .FLOATINGPOINT_SUB | .FLOATINGPOINT_MULT | .FLOATINGPOINT_DIV
=> RoundingMode × Term × Term

| .FLOATINGPOINT_FMA
=> RoundingMode × Term × Term × Term

| .BITVECTOR_REPEAT
| .BITVECTOR_ZERO_EXTEND
| .BITVECTOR_SIGN_EXTEND
| .BITVECTOR_ROTATE_LEFT
| .BITVECTOR_ROTATE_RIGHT
| .INT_TO_BITVECTOR
| .BITVECTOR_BIT
=> TermsAndIndices Term Term

| .BITVECTOR_EXTRACT
| .FLOATINGPOINT_TO_FP_FROM_IEEE_BV
=> TermsAndIndices Term (Term × Term)

| .FLOATINGPOINT_TO_UBV | .FLOATINGPOINT_TO_SBV
=> TermsAndIndices (RoundingMode × Term) Term

| .FLOATINGPOINT_TO_FP_FROM_FP | .FLOATINGPOINT_TO_FP_FROM_REAL | .FLOATINGPOINT_TO_FP_FROM_SBV
| .FLOATINGPOINT_TO_FP_FROM_UBV
=> TermsAndIndices (RoundingMode × Term) (Term × Term)

| .CONSTANT
| .VARIABLE
=> String

| .CONST_BOOLEAN
=> Bool

| .CONST_INTEGER
=> Int

| .CONST_RATIONAL
=> Rat

| .CONST_BITVECTOR
=> String

| .CONST_FLOATINGPOINT
=> UInt32 × UInt32 × Term

| .CONST_ROUNDINGMODE
 => RoundingMode

| .PI
| .CONST_FINITE_FIELD
=> Unit

| .SKOLEM
| .CARDINALITY_CONSTRAINT
=> Empty

| .INTERNAL_KIND
| .UNDEFINED_KIND
| .NULL_TERM
| .UNINTERPRETED_SORT_VALUE
| _
=> Empty

end Kind



namespace Term

def decompose (t : Term) : Env ((k : Kind) × k.Sig) := do
  let kind ← t.getKind
  match h : kind with
  | .EQUAL | .DISTINCT
  | .APPLY_UF
  | .AND | .IMPLIES | .OR | .XOR | .ADD | .MULT | .SUB
  | .DIVISION | .DIVISION_TOTAL | .INTS_DIVISION | .INTS_DIVISION_TOTAL
  | .BITVECTOR_CONCAT | .BITVECTOR_AND | .BITVECTOR_OR | .BITVECTOR_XOR
  | .BITVECTOR_MULT | .BITVECTOR_ADD | .BITVECTOR_SUB
  | .FINITE_FIELD_ADD | .FINITE_FIELD_BITSUM | .FINITE_FIELD_MULT =>
    return ⟨kind, h ▸ (← array2)⟩
  | .LT | .LEQ | .GT | .GEQ =>
    return ⟨kind, h ▸ (← term2)⟩
  | .SEXPR
  | .BITVECTOR_FROM_BOOLS =>
    return ⟨kind, h ▸ (← array1)⟩
  | .NOT
  | .POW2 | .LOG2
  | .NEG
  | .ABS
  | .EXPONENTIAL
  | .SINE | .COSINE | .TANGENT | .COSECANT | .SECANT | .COTANGENT
  | .ARCSINE | .ARCCOSINE | .ARCTANGENT | .ARCCOSECANT | .ARCSECANT | .ARCCOTANGENT
  | .SQRT
  | .DIVISIBLE
  | .IS_INTEGER | .TO_INTEGER
  | .TO_REAL
  | .BITVECTOR_NOT | .BITVECTOR_NEG | .BITVECTOR_REDOR | .BITVECTOR_REDAND | .BITVECTOR_NEGO
  | .BITVECTOR_TO_NAT | .BITVECTOR_UBV_TO_INT | .BITVECTOR_SBV_TO_INT
  | .FINITE_FIELD_NEG
  | .FLOATINGPOINT_ABS | .FLOATINGPOINT_NEG
  | .FLOATINGPOINT_IS_NORMAL | .FLOATINGPOINT_IS_SUBNORMAL | .FLOATINGPOINT_IS_ZERO
  | .FLOATINGPOINT_IS_INF | .FLOATINGPOINT_IS_NAN | .FLOATINGPOINT_IS_NEG | .FLOATINGPOINT_IS_POS
  | .FLOATINGPOINT_TO_REAL =>
    return ⟨kind, h ▸ (← term1)⟩
  | .LAMBDA
  | .HO_APPLY
  | .IAND
  | .INTS_MODULUS
  | .INTS_MODULUS_TOTAL
  | .POW
  | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR | .BITVECTOR_COMP
  | .BITVECTOR_UDIV | .BITVECTOR_UREM
  | .BITVECTOR_SDIV | .BITVECTOR_SREM | .BITVECTOR_SMOD
  | .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR
  | .BITVECTOR_ULT | .BITVECTOR_ULE | .BITVECTOR_UGT | .BITVECTOR_UGE
  | .BITVECTOR_SLT | .BITVECTOR_SLE | .BITVECTOR_SGT | .BITVECTOR_SGE
  | .BITVECTOR_ULTBV | .BITVECTOR_SLTBV
  | .BITVECTOR_UADDO | .BITVECTOR_SADDO | .BITVECTOR_UMULO | .BITVECTOR_SMULO
  | .BITVECTOR_USUBO | .BITVECTOR_SSUBO | .BITVECTOR_SDIVO
  | .FLOATINGPOINT_EQ | .FLOATINGPOINT_REM | .FLOATINGPOINT_RTI
  | .FLOATINGPOINT_LEQ | .FLOATINGPOINT_LT | .FLOATINGPOINT_GEQ | .FLOATINGPOINT_GT
  | .SELECT
  | .CONST_ARRAY =>
    return ⟨kind, h ▸ (← term2)⟩
  | .WITNESS
  | .ITE
  | .PIAND
  | .BITVECTOR_ITE
  | .FLOATINGPOINT_FP
  | .STORE =>
    return ⟨kind, h ▸ (← term3)⟩
  | .FLOATINGPOINT_SQRT | .FLOATINGPOINT_MIN | .FLOATINGPOINT_MAX =>
    return ⟨kind, h ▸ (← roundingTerm1)⟩
  | .FLOATINGPOINT_ADD | .FLOATINGPOINT_SUB | .FLOATINGPOINT_MULT | .FLOATINGPOINT_DIV =>
    return ⟨kind, h ▸ (← roundingTerm2)⟩
  | .FLOATINGPOINT_FMA =>
    return ⟨kind, h ▸ (← roundingTerm3)⟩
  | .BITVECTOR_REPEAT
  | .BITVECTOR_ZERO_EXTEND
  | .BITVECTOR_SIGN_EXTEND
  | .BITVECTOR_ROTATE_LEFT
  | .BITVECTOR_ROTATE_RIGHT
  | .INT_TO_BITVECTOR
  | .BITVECTOR_BIT =>
    return ⟨kind, h ▸ (← term1Index1)⟩
  | .BITVECTOR_EXTRACT
  | .FLOATINGPOINT_TO_FP_FROM_IEEE_BV =>
    return ⟨kind, h ▸ (← term1Index2)⟩
  | .FLOATINGPOINT_TO_UBV | .FLOATINGPOINT_TO_SBV =>
    return ⟨kind, h ▸ (← roundingTermIndex1)⟩
  | .FLOATINGPOINT_TO_FP_FROM_FP | .FLOATINGPOINT_TO_FP_FROM_REAL | .FLOATINGPOINT_TO_FP_FROM_SBV
  | .FLOATINGPOINT_TO_FP_FROM_UBV =>
    return ⟨kind, h ▸ (← roundingTermIndex2)⟩
  -- | .CONSTANT => sorry
  -- | .VARIABLE => sorry
  | .CONST_BOOLEAN => return ⟨kind, h ▸ (← t.getBooleanValue)⟩
  | .CONST_INTEGER => return ⟨kind, h ▸ (← t.getIntegerValue)⟩
  | .CONST_RATIONAL => return ⟨kind, h ▸ (← t.getRationalValue)⟩
  | .CONST_BITVECTOR => return ⟨kind, h ▸ (← t.getBitVectorValue 10)⟩
  | .CONSTANT | .VARIABLE => return ⟨kind, h▸ (← t.getSymbol)⟩

  | _ => throw <| Error.error "unimplemented"
where
  array2 : Env (Term × Term × Array Term) := do
    let kids := t.getChildren
    if h : 2 ≤ kids.size then return (kids[0], kids[1], kids.drop 2) else
    throw <| Error.error s!"expected at least 2 children in term `{t}` | {kids}"
  array1 : Env (Term × Array Term) := do
    let kids := t.getChildren
    if h : 1 ≤ kids.size then return (kids[0], kids.drop 1) else
    throw <| Error.error s!"expected at least 1 children in term `{t}` | {kids}"
  term1 : Env Term := do
    let kids := t.getChildren
    if h : kids.size = 1 then return kids[0] else
    throw <| Error.error s!"expected exactly 1 child in term `{t}` | {kids}"
  term2 : Env (Term × Term) := do
    let kids := t.getChildren
    if h : kids.size = 2 then return (kids[0], kids[1]) else
    throw <| Error.error s!"expected exactly 2 children in term `{t}` | {kids}"
  term3 : Env (Term × Term × Term) := do
    let kids := t.getChildren
    if h : kids.size = 3 then return (kids[0], kids[1], kids[2]) else
    throw <| Error.error s!"expected exactly 3 children in term `{t}` | {kids}"
  roundingTerm1 : Env (RoundingMode × Term) := do
    let kids := t.getChildren
    if h : kids.size = 2 then
      let rm ← kids[0].getRoundingModeValue
      return (rm, kids[1])
    else throw <| Error.error s!"expected exactly 2 children in term `{t}` | {kids}"
  roundingTerm2 : Env (RoundingMode × Term × Term) := do
    let kids := t.getChildren
    if h : kids.size = 3 then
      let rm ← kids[0].getRoundingModeValue
      return (rm, kids[1], kids[2])
    else throw <| Error.error s!"expected exactly 3 children in term `{t}` | {kids}"
  roundingTerm3 : Env (RoundingMode × Term × Term × Term) := do
    let kids := t.getChildren
    if h : kids.size = 4 then
      let rm ← kids[0].getRoundingModeValue
      return (rm, kids[1], kids[2], kids[3])
    else throw <| Error.error s!"expected exactly 4 children in term `{t}` | {kids}"
  term1Index1 : Env (TermsAndIndices Term Term) := do
    let kid ← term1
    let op ← t.getOp
    if h : op.getNumIndices = 1 then return ⟨kid, op[0]⟩ else
    throw <| Error.error s!"expected exactly 1 index in term `{t}` | {op}"
  term1Index2 : Env (TermsAndIndices Term (Term × Term)) := do
    let kid ← term1
    let op ← t.getOp
    if h : op.getNumIndices = 2 then return ⟨kid, (op[0], op[1])⟩ else
    throw <| Error.error s!"expected exactly 2 indices in term `{t}` | {op}"
  roundingTermIndex1 : Env (TermsAndIndices (RoundingMode × Term) Term) := do
    let (rm, kid) ← roundingTerm1
    let op ← t.getOp
    if h : op.getNumIndices = 1 then return ⟨(rm ,kid), op[0]⟩ else
    throw <| Error.error s!"expected exactly 1 index in term `{t}` | {op}"
  roundingTermIndex2 : Env (TermsAndIndices (RoundingMode × Term) (Term × Term)) := do
    let (rm, kid) ← roundingTerm1
    let op ← t.getOp
    if h : op.getNumIndices = 2 then return ⟨(rm ,kid), (op[0], op[1])⟩ else
    throw <| Error.error s!"expected exactly 2 index in term `{t}` | {op}"

end Term

namespace Test

partial def indentDecompose (t : Term) (indent := "") : Env Unit := do
  let ⟨kind, kids⟩ ← try t.decompose catch e =>
    println! "{indent}{e}"
    return ()
  println! "{indent}{kind}"
  match kind with
  | .EQUAL | .DISTINCT
  | .APPLY_UF
  | .AND | .IMPLIES | .OR | .XOR | .ADD | .MULT | .SUB
  | .DIVISION | .DIVISION_TOTAL | .INTS_DIVISION | .INTS_DIVISION_TOTAL
  | .BITVECTOR_CONCAT | .BITVECTOR_AND | .BITVECTOR_OR | .BITVECTOR_XOR
  | .BITVECTOR_MULT | .BITVECTOR_ADD | .BITVECTOR_SUB
  | .FINITE_FIELD_ADD | .FINITE_FIELD_BITSUM | .FINITE_FIELD_MULT =>
    let (lhs, rhs, tail) := kids
    let indent' := indent ++ "  "
    println! "{indent}- {lhs}"
    indentDecompose lhs indent'
    println! "{indent}- {rhs}"
    indentDecompose rhs indent'
    for kid in tail do
      println! "{indent}- {kid}"
      indentDecompose kid indent'
  | .LT | .LEQ | .GT | .GEQ =>
    let (lhs, rhs) := kids
    let indent' := indent ++ "  "
    println! "{indent}- {lhs}"
    indentDecompose lhs indent'
    println! "{indent}- {rhs}"
    indentDecompose rhs indent'
  | .WITNESS | .ITE | .PIAND | .BITVECTOR_ITE | .FLOATINGPOINT_FP | .STORE =>
    let (t1, t2, t3) := kids
    let indent' := indent ++ "  "
    println! "{indent}- {t1}"
    indentDecompose t1 indent'
    println! "{indent}- {t2}"
    indentDecompose t2 indent'
    println! "{indent}- {t3}"
    indentDecompose t3 indent'
  | .NOT
  | .POW2 | .LOG2
  | .NEG
  | .ABS
  | .EXPONENTIAL
  | .SINE | .COSINE | .TANGENT | .COSECANT | .SECANT | .COTANGENT
  | .ARCSINE | .ARCCOSINE | .ARCTANGENT | .ARCCOSECANT | .ARCSECANT | .ARCCOTANGENT
  | .SQRT
  | .DIVISIBLE
  | .IS_INTEGER | .TO_INTEGER
  | .TO_REAL
  | .BITVECTOR_NOT | .BITVECTOR_NEG | .BITVECTOR_REDOR | .BITVECTOR_REDAND | .BITVECTOR_NEGO
  | .BITVECTOR_TO_NAT | .BITVECTOR_UBV_TO_INT | .BITVECTOR_SBV_TO_INT
  | .FINITE_FIELD_NEG
  | .FLOATINGPOINT_ABS | .FLOATINGPOINT_NEG
  | .FLOATINGPOINT_IS_NORMAL | .FLOATINGPOINT_IS_SUBNORMAL | .FLOATINGPOINT_IS_ZERO
  | .FLOATINGPOINT_IS_INF | .FLOATINGPOINT_IS_NAN | .FLOATINGPOINT_IS_NEG | .FLOATINGPOINT_IS_POS
  | .FLOATINGPOINT_TO_REAL =>
    let kid := kids
    let indent' := indent ++ "  "
    println! "{indent}- {kid}"
    indentDecompose kid indent'
  | .CONST_BOOLEAN =>
    let val : Bool := kids
    println! "{indent}- {val} : Bool"
  | .CONST_INTEGER =>
    let val : Int := kids
    println! "{indent}- {val} : Int"
  | .CONST_RATIONAL =>
    let val : Rat := kids
    println! "{indent}- {val} : Rat"
  | .CONST_BITVECTOR =>
    let val : String := kids
    println! "{indent}- {val} : String (BV)"
  | .CONSTANT | .VARIABLE =>
    let sym : String := kids
    println! "{indent}- {sym} : String (symbol)"
  | _ => println! "{indent}unsuported kind {kind}"
  return ()

/-- info:
(and (<= (ite b1 (+ n1 0 3) n2) 0) (<= 0 3))
AND
- lhs → (<= (ite b1 (+ n1 0 3) n2) 0)
  LEQ
  - lhs → (ite b1 (+ n1 0 3) n2)
    ITE
    - cnd → b1
    - thn → (+ n1 0 3)
    - els → n2
  - rhs → 0
- rhs → (<= 0 3)

(and (and (<= (ite b1 (+ n1 0 3) n2) 0) (<= 0 3)) b1 b2)
AND
- (and (<= (ite b1 (+ n1 0 3) n2) 0) (<= 0 3))
  AND
  - (<= (ite b1 (+ n1 0 3) n2) 0)
    LEQ
    - (ite b1 (+ n1 0 3) n2)
      ITE
      - b1
        CONSTANT
        - b1 : String (symbol)
      - (+ n1 0 3)
        ADD
        - n1
          CONSTANT
          - n1 : String (symbol)
        - 0
          CONST_INTEGER
          - 0 : Int
        - 3
          CONST_INTEGER
          - 3 : Int
      - n2
        CONSTANT
        - n2 : String (symbol)
    - 0
      CONST_INTEGER
      - 0 : Int
  - (<= 0 3)
    LEQ
    - 0
      CONST_INTEGER
      - 0 : Int
    - 3
      CONST_INTEGER
      - 3 : Int
- b1
  CONSTANT
  - b1 : String (symbol)
- b2
  CONSTANT
  - b2 : String (symbol)

(fp #b0 #b000 #b0000)
(fp.sqrt roundTowardZero (fp #b0 #b000 #b0000))
  rm → RTZ
  t1 → (fp #b0 #b000 #b0000)
-/
test![test, test] tm => do
  let bool ← tm.getBooleanSort
  let b1 ← tm.mkConst bool "b1"
  let b2 ← tm.mkConst bool "b2"
  let int ← tm.getIntegerSort
  let n1 ← tm.mkConst int "n1"
  let n2 ← tm.mkConst int "n2"
  let int0 ← tm.mkInteger 0
  let int3 ← tm.mkInteger 3

  let add ← tm.mkTerm .ADD #[n1, int0, int3]
  let ite ← tm.mkTerm .ITE #[b1, add, n2]
  let leq ← tm.mkTerm .LEQ #[ite, int0, int3]

  println! ""
  println! "{leq}"
  if let ⟨.AND, (lhs, rhs, tail)⟩ ← leq.decompose then
    println! "AND"
    println! "- lhs → {lhs}"
    if let ⟨.LEQ, (lhs, rhs)⟩ ← lhs.decompose then
      println! "  LEQ"
      println! "  - lhs → {lhs}"
      if let ⟨.ITE, (cnd, thn, els)⟩ ← lhs.decompose then
        println! "    ITE"
        println! "    - cnd → {cnd}"
        println! "    - thn → {thn}"
        println! "    - els → {els}"
      else println! "expected LEQ kind"
      println! "  - rhs → {rhs}"
    else println! "expected LEQ kind"
    println! "- rhs → {rhs}"
    let mut count := 1
    for kid in tail do
      count := count + 1
      println! "- kid[{count}] → {kid}"
  else println! "expected AND kind"

  println! ""
  let and ← tm.mkTerm .AND #[leq, b1, b2]
  println! "{and}"
  indentDecompose and

  println! ""
  let t1 ← tm.mkBitVector 8
  let fp ← tm.mkFloatingPoint 3 5 t1
  println! "{fp}"
  let sqrt ← tm.mkTerm .FLOATINGPOINT_SQRT #[← tm.mkRoundingMode .ROUND_TOWARD_ZERO, fp]
  println! "{sqrt}"
  if let ⟨.FLOATINGPOINT_SQRT, (rm, t1)⟩ ← sqrt.decompose then
    println! "  rm → {rm}"
    println! "  t1 → {t1}"
  else println! "expected floating point sqrt"
