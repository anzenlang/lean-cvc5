import cvc5



namespace Cvc5.Monadic

namespace Term

variable [Monad m] [MonadLiftT (Env ω) m]

def mkAnd : (terms : Array (Term ω)) → m (Term ω) := mk .AND
def mkOr : (terms : Array (Term ω)) → m (Term ω) := mk .OR

def mk1 (op : cvc5.Kind) (term : Term ω) : m (Term ω) := mk op #[term]
def mk2 (op : cvc5.Kind) (lft rgt : Term ω) : m (Term ω) := mk op #[lft, rgt]
def mk3 (op : cvc5.Kind) (t1 t2 t3 : Term ω) : m (Term ω) := mk op #[t1, t2, t3]

def mkNot : Term ω → m (Term ω) := mk1 .NOT

def mkEq : Term ω → Term ω → m (Term ω) := mk2 .EQUAL
def mkImplies : Term ω → Term ω → m (Term ω) := mk2 .IMPLIES
def mkLt : Term ω → Term ω → m (Term ω) := mk2 .LT
def mkLe : Term ω → Term ω → m (Term ω) := mk2 .LEQ
def mkEq0 (term : Term ω) : m (Term ω) := mkInt 0 >>= mkEq term
def mkAdd : Term ω → Term ω → m (Term ω) := mk2 .ADD
def mkSub : Term ω → Term ω → m (Term ω) := mk2 .SUB
def mkIte : Term ω → Term ω → Term ω → m (Term ω) := mk3 .ITE

end Term



namespace Solver

def check (assuming : Array (Term ω) := #[]) (solver : Solver ω) : Env ω Bool := do
  let res ← solver.checkSatAssuming assuming
  if res.isSat then return true
  if res.isUnsat then return false
  throw <| cvc5.Error.error s!"unexpected *unknown* check-sat result"

end Solver

end Cvc5.Monadic



namespace Test.Monadic

open Cvc5.Monadic (EnvIO Env Term Solver Srt)



structure TSys.Spec (ω : Type) (SVars : Type → Type) where
  sVarsAt (k : Nat) : EnvIO ω (SVars ω)
  sVarsToString : (SVars ω) → Array String
  init : (SVars ω) → EnvIO ω (Term ω)
  step : (curr : (SVars ω)) → (next : (SVars ω)) → EnvIO ω (Term ω)
  getValues : Solver ω → (SVars ω) → EnvIO ω (SVars ω)
  candidate : (SVars ω) → EnvIO ω (Term ω)

inductive Result (SVars : Type)
| safe (k : Nat) | cex (trace : Array SVars) | unknown

namespace Result

def isUnknown : Result SVars → Bool
| .unknown => true | _ => false

end Result

structure TSys (ω : Type) (SVars : Type → Type) extends TSys.Spec ω SVars where private mk' ::
  sVars : SVars ω × List (SVars ω)
  baseSolver : Solver ω
  stepSolver : Solver ω

namespace TSys

def mk (spec : Spec ω SVars) : EnvIO ω (TSys ω SVars) := do
  let sVars0 ← spec.sVarsAt 0
  let init0 ← spec.init sVars0
  let baseSolver ← Solver.mk
  baseSolver.setOption "produce-models" "true"
  baseSolver.assert init0
  let stepSolver ← Solver.mk
  stepSolver.setOption "produce-models" "true"
  let candidate0 ← spec.candidate sVars0
  stepSolver.assert candidate0
  return ⟨spec, (sVars0, []), baseSolver, stepSolver⟩

def negCandidate (sVars : SVars ω) (sys : TSys ω SVars) : EnvIO ω (Term ω) := do
  sys.candidate sVars >>= Term.mkNot

def currK (sys : TSys ω SVars) : Nat := sys.sVars.snd.length
def currSVars (sys : TSys ω SVars) : SVars ω := sys.sVars.fst
def allPreSVars (sys : TSys ω SVars) : List (SVars ω) := sys.sVars.snd
def stageNextSVars (sys : TSys ω SVars) : EnvIO ω (SVars ω × TSys ω SVars) := do
  let next ← sys.sVarsAt sys.currK.succ
  let sVars := (next, sys.currSVars :: sys.allPreSVars)
  return (next, {sys with sVars})

abbrev Trace (_ : TSys ω SVars) := Array (SVars ω)
abbrev Trace? (sys : TSys ω SVars) := Option sys.Trace
protected abbrev Result (_ : TSys ω SVars) := Result (SVars ω)

def printTrace (sys : TSys ω SVars) (trace : sys.Trace) (pref := "") : EnvIO ω Unit := do
  let mut cnt := 0
  let k := sys.currK
  for sVars in trace do
    let k := k - cnt
    cnt := cnt + 1
    let lines := sys.sVarsToString sVars
    println! "{pref}- at {k}"
    for line in lines do
      println! "{pref}  {line}"

def getCex (solver : Solver ω) (sys : TSys ω SVars) : EnvIO ω sys.Trace := do
  let mut trace := Array.mkEmpty sys.sVars.snd.length
  trace := trace.push (← sys.getValues solver sys.currSVars)
  for sVars in sys.allPreSVars do
    trace := trace.push (← sys.getValues solver sVars)
  return trace

def getBaseCex (sys : TSys ω SVars) : EnvIO ω sys.Trace :=
  sys.getCex sys.baseSolver

def getStepCex (sys : TSys ω SVars) : EnvIO ω sys.Trace :=
  sys.getCex sys.stepSolver

def getCex? (solver : Solver ω) (sys : TSys ω SVars)
: EnvIO ω sys.Trace? := do
  let bad ← sys.negCandidate sys.currSVars
  let isSat ← solver.check #[bad]
  if isSat then sys.getCex solver else return none

def getBaseCex? (sys : TSys ω SVars) : EnvIO ω sys.Trace? := do
  sys.getCex? sys.baseSolver

def getStepCex? (sys : TSys ω SVars) : EnvIO ω sys.Trace? := do
  sys.getCex? sys.stepSolver

def unroll (sys : TSys ω SVars) : EnvIO ω (TSys ω SVars) := do
  let curr := sys.currSVars
  let currCandidate ← sys.candidate curr
  let (next, sys) ← sys.stageNextSVars
  let step ← sys.step curr next
  sys.baseSolver.assert step
  sys.stepSolver.assert currCandidate
  sys.stepSolver.assert step
  return sys

def checkBaseUnrollCheckStep (sys : TSys ω SVars) : EnvIO ω (sys.Result × TSys ω SVars) := do
  if let some baseCex ← sys.getBaseCex? then
    return (.cex baseCex, sys)
  else
    let sys ← sys.unroll
    if let some _stepCex ← sys.getStepCex? then
      println! "step cex at {sys.currK}"
      -- sys.printTrace stepCex
      return (.unknown, sys)
    else
      return (.safe sys.currK, sys)


def check' (sys : TSys ω SVars) : (maxK : Nat := 5) → EnvIO ω (sys.Result × TSys ω SVars)
| 0 => return (.unknown, sys)
| maxK + 1 => do
  let (res, sys) ← sys.checkBaseUnrollCheckStep
  if res.isUnknown then sys.check' maxK else return (res, sys)

def check (sys : TSys ω SVars) (maxK : Nat := 5) : EnvIO ω sys.Result :=
  Prod.fst <$> sys.check' maxK

end TSys



namespace Sw

structure SVars (ω : Type) where
  startStop : (Term ω)
  reset : (Term ω)
  isCounting : (Term ω)
  counter : (Term ω)

def Spec (candidate : {ω : Type} → SVars ω → EnvIO ω (Term ω)) : TSys.Spec ω SVars where
  sVarsAt k := do
    let bool ← Srt.getBool
    let int ← Srt.getInt
    return ⟨
      ← Term.mkConst s!"startStop@{k}" bool,
      ← Term.mkConst s!"reset@{k}" bool,
      ← Term.mkConst s!"isCounting@{k}" bool,
      ← Term.mkConst s!"counter@{k}" int,
    ⟩
  getValues solver vars := return ⟨
    ← solver.getValue vars.startStop,
    ← solver.getValue vars.reset,
    ← solver.getValue vars.isCounting,
    ← solver.getValue vars.counter,
  ⟩
  sVarsToString vals := #[
    s!"counter = {vals.counter}, isCounting = {vals.isCounting}",
    s!"startStop = {vals.startStop}, reset = {vals.reset}",
  ]
  init vars := do
    let zero ← Term.mkInt 0
    let notCounting ← vars.isCounting.mkNot
    let counterGe0 ← zero.mkLe vars.counter
    let onReset ← vars.reset.mkImplies (← vars.counter.mkEq zero)
    let init ← Term.mkAnd #[notCounting, counterGe0, onReset ]
    return init
  step curr next := do
    let isCountingDef ←
      next.startStop.mkIte (← curr.isCounting.mkNot) curr.isCounting
    let counterIncIfCounting ←
      curr.counter.mkAdd (← next.isCounting.mkIte (← Term.mkInt 1) (← Term.mkInt 0))
    let counterDef ←
      next.reset.mkIte (← Term.mkInt 0) counterIncIfCounting
    Term.mkAnd #[
      ← next.isCounting.mkEq isCountingDef,
      ← next.counter.mkEq counterDef,
    ]
  candidate

def counterPos (vars : SVars ω) : EnvIO ω (Term ω) := do
  (← Term.mkInt 0) |>.mkLe vars.counter

def counterNotMinus7 (vars : SVars ω) : EnvIO ω (Term ω) := do
  let eqM7 ← vars.counter.mkEq (← Term.mkInt (-7))
  eqM7.mkNot

def resetImpliesCounterIs0 (vars : SVars ω) : EnvIO ω (Term ω) := do
  let notReset ← vars.reset.mkNot
  let counterIs0 ← vars.counter.mkEq (← Term.mkInt 0)
  Term.mkOr #[notReset, counterIs0]

def allCandidates (vars : SVars ω) : EnvIO ω (Term ω) := do Term.mkAnd #[
  ← counterPos vars,
  ← counterNotMinus7 vars,
  ← resetImpliesCounterIs0 vars,
]

def test (candidate : {ω : Type} → SVars ω → EnvIO ω (Term ω)) : IO Unit :=
  Cvc5.Monadic.Env.run fun _ω => do
    let sys ← TSys.mk <| Sw.Spec candidate
    let (res, sys) ← sys.check'
    match res with
    | .safe k =>
      println! "candidate is {k}-inductive"
    | .cex trace =>
      println! "found a counterexample"
      sys.printTrace trace
    | .unknown =>
      println! "could not reach a conclusion"


/-- info:
candidate is 1-inductive
-/
#guard_msgs in #eval test counterPos

/-- info:
step cex at 1
step cex at 2
step cex at 3
step cex at 4
step cex at 5
could not reach a conclusion
-/
#guard_msgs in #eval test counterNotMinus7

/-- info:
candidate is 1-inductive
-/
#guard_msgs in #eval test resetImpliesCounterIs0

/-- info:
candidate is 1-inductive
-/
#guard_msgs in #eval test allCandidates



/-- error: application type mismatch
  pure __do_lift✝
argument
  __do_lift✝
has type
  Option (Term _ω) : Type
but is expected to have type
  Option (Term ω) : Type
-/
#guard_msgs in
def test' (candidate : {ω : Type} → SVars ω → EnvIO ω (Term ω)) : IO (Option (Term ω)) :=
  Cvc5.Monadic.Env.run fun _ω => do
    let sys ← TSys.mk <| Sw.Spec candidate
    let (res, sys) ← sys.check'
    match res with
    | .safe k =>
      println! "candidate is {k}-inductive"
      return ← some <$> sys.candidate sys.currSVars -- ‼️ error here
    | .cex trace =>
      println! "found a counterexample"
      sys.printTrace trace
      return none
    | .unknown =>
      println! "could not reach a conclusion"
      return none

end Sw



def solveConstraints (constraints : Array (Term ω)) : EnvIO ω Bool := do
  let solver ← Solver.mk
  for constraint in constraints do
    solver.assert constraint
  let res ← solver.checkSat
  if res.isSat then return true
  else if res.isUnsat then return false
  else throw <| cvc5.Error.error "unexpected unknown result"

def run1 : IO Unit :=
  Cvc5.Monadic.Env.run fun _ω => do
    let int ← Srt.getInt
    let x ← Term.mkConst "x" int
    let zero ← Term.mkInt 0
    let three ← Term.mkInt 3
    let seven ← Term.mkInt 7
    let xEq lhs := Term.mk .EQUAL #[x, lhs]
    let xEqZero ← xEq zero
    let xEqThree ← xEq three
    let xEqSeven ← xEq seven

    let res1 ← solveConstraints #[xEqZero]
    println! "res1 is sat = {res1}"

    let res2 ← solveConstraints #[xEqThree, xEqSeven]
    println! "res2 is sat = {res2}"

/-- info:
res1 is sat = true
res2 is sat = false
-/
#guard_msgs in #eval run1


structure CSolver (ω : Type) where
private mk' ::
  solver : Solver ω
  satisfiable : Array (Term ω)

namespace CSolver

def mk (ω : Type) : Env ω (CSolver ω) := do
  let solver ← Solver.mk
  return ⟨solver, #[]⟩

/-- Returns `true` and registers `constraint` if it is satisfiable with the current constraints. -/
def addConstraint? (cs : CSolver ω) (constraint : Term ω) : Env ω (Bool × CSolver ω) := do
  let res ← cs.solver.checkSatAssuming #[constraint]
  if res.isSat then
    cs.solver.assert constraint
    return (true, {cs with satisfiable := cs.satisfiable.push constraint})
  else if res.isUnsat then
    return (false, cs)
  else
    throw <| cvc5.Error.error "unexpected unknown result"

end CSolver

def extractSatisfiableConstraints (constraints : Array (Term ω)) : EnvIO ω (Array (Term ω)) := do
  let mut cs ← CSolver.mk ω
  for constraint in constraints do
    println! "current constraint: {constraint}"
    let (added, cs') ← cs.addConstraint? constraint
    cs := cs'
    if added then println! "→ satisfiable with current constraints, added 😺"
    else println! "→ not satisfiable with current constraints, ignored 😿"
    println! ""
  println! "done, extracted {cs.satisfiable.size} satisfiable constraints"
  return cs.satisfiable

def run2 : IO Unit :=
  Cvc5.Monadic.Env.run fun _ω => do
    let int ← Srt.getInt
    let x ← Term.mkConst "x" int
    let zero ← Term.mkInt 0
    let three ← Term.mkInt 3
    let seven ← Term.mkInt 7
    let xEq lhs := Term.mk .EQUAL #[x, lhs]
    let xEqZero ← xEq zero
    let xEqThree ← xEq three
    let xEqSeven ← xEq seven
    let xLe lhs := Term.mk .LEQ #[x, lhs]
    let xLeZero ← xLe zero
    let xLeThree ← xLe three
    let xLeSeven ← xLe seven
    let xGe lhs := Term.mk .GEQ #[x, lhs]
    let xGeZero ← xGe zero
    let xGeThree ← xGe three
    let xGeSeven ← xGe seven

    let constraints := #[
      xGeThree, xEqSeven, xLeThree, xGeZero, xEqZero, xEqThree, xGeSeven, xLeZero, xLeSeven
    ]
    let satisfiable ← extractSatisfiableConstraints constraints

    for term in satisfiable do
      println! "- {term}"

/-- info:
current constraint: (>= x 3)
→ satisfiable with current constraints, added 😺

current constraint: (= x 7)
→ satisfiable with current constraints, added 😺

current constraint: (<= x 3)
→ not satisfiable with current constraints, ignored 😿

current constraint: (>= x 0)
→ satisfiable with current constraints, added 😺

current constraint: (= x 0)
→ not satisfiable with current constraints, ignored 😿

current constraint: (= x 3)
→ not satisfiable with current constraints, ignored 😿

current constraint: (>= x 7)
→ satisfiable with current constraints, added 😺

current constraint: (<= x 0)
→ not satisfiable with current constraints, ignored 😿

current constraint: (<= x 7)
→ satisfiable with current constraints, added 😺

done, extracted 5 satisfiable constraints
- (>= x 3)
- (= x 7)
- (>= x 0)
- (>= x 7)
- (<= x 7)
-/
#guard_msgs in #eval run2

end Test.Monadic
