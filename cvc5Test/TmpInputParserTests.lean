import cvc5Test.Init




namespace cvc5.Test



def showErrorIn (blah : String) (code : Env Unit) : Env Unit := do
  if ¬ blah.isEmpty then println! "{blah}:"
  try code ; println! "‼️ expected an error" catch e => println! "{e}"

/-- info:
parsed terms := #[(and (not false) b), (=> true b), false, 5]
parsed nothing := #[]
parsed not_b := (not b)
unsat:
(
(declare-const b Bool)
(assume @p1 b)
(assume @p2 (not b))
(step @p3 false :rule contra :premises (@p1 @p2))
)
-/
test! tm => do
  let solver ← tm.newSolver

  solver.parseCommands "
(set-logic QF_LIA)
(set-option :produce-proofs true)

(declare-fun b () Bool)
  "

  let terms ← solver.parseTerms "
(and (not false) b)
(=> true b)
false
5
  "
  println! "parsed terms := {terms}"

  let nothing ← solver.parseTerms ""
  println! "parsed nothing := {nothing}"

  let not_b ← solver.parseTerm "(not b)"
  println! "parsed not_b := {not_b}"

  solver.parseCheck
    "
(assert b)
(assert (not b))
    "
    (ifSat := println! "sat")
    (ifUnsat := do
      println! "unsat:"
      let proofs ← solver.getProof
      for proof in proofs do
        println! "{← solver.proofToString proof}")
    (ifUnknown := println! "unknown")

/-- info:
declared terms:
- b
- n
model:
- b ↦ true
- n ↦ 53
sorts:
- u
-/
test! tm => do
  let solver ← tm.newSolver

  solver.parseCommands "
(set-logic AUFLIA)
(set-option :produce-proofs true)
(set-option :produce-models true)

(declare-sort u 0)

(declare-fun b () Bool)
(declare-fun n () Int)

(assert b)
(assert (< 52 n))
  "
  let res ← solver.checkSat
  if ¬ res.isSat then
    println! "expected sat"

  let terms ← solver.getParserDeclaredTerms
  println! "declared terms:"
  for term in terms do
    println! "- {term}"

  let model ← solver.getParserModel
  println! "model:"
  for (var, val) in model do
    println! "- {var} ↦ {val}"

  let sorts ← solver.getParserDeclaredSorts
  println! "sorts:"
  for sort in sorts do
    println! "- {sort}"

/-- info:
model:
- b ↦ true
- n ↦ 53
-/
test! tm => do
  let solver ← tm.newSolver
  solver.setOption "produce-models" "true"

  let model? ← solver.parseAndGetModel? "
(set-logic AUFLIA)

(declare-sort u 0)

(declare-fun b () Bool)
(declare-fun n () Int)

(assert b)
(assert (< 52 n))
  "

  match model? with
  | none => println! "unsat"
  | some model =>
    println! "model:"
    for (var, val) in model do
      println! "- {var} ↦ {val}"

  -- making sure having a check-sat in there is okay
  let _ ← solver.parseAndGetModel? "(assert true)(check-sat)"



/-- info:
ill-formed command:
cvc5.Error.error "Expected a RPAREN_TOK, got `` (EOF_TOK)."
ill-formed terms:
cvc5.Error.error "Expected SMT-LIBv2 term, got `` (EOF_TOK)."
unknown symbol:
cvc5.Error.error "Symbol 'b' not declared as a variable"
more than one term to parse:
cvc5.Error.error "expected exactly one term, got 2: #[(not false), true]"
-/
test! tm => do
  let solver ← tm.newSolver

  showErrorIn "ill-formed command" do
    solver.parseCommands "(set-logic ALL)(declare-fun babB () Bool"

  showErrorIn "ill-formed terms" do
    let _ ← solver.parseTerms "true (not"

  showErrorIn "unknown symbol" do
    let _ ← solver.parseTerm "(not b)"

  showErrorIn "more than one term to parse" do
    let _ ← solver.parseTerm "(not false) true"
