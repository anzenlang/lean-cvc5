import cvc5



namespace Cvc5.Term

def mkAnd : (terms : Array Term) → Env Term := mk .AND
def mkOr : (terms : Array Term) → Env Term := mk .OR

def mk1 (op : cvc5.Kind) (term : Term) : Env Term := mk op #[term]
def mk2 (op : cvc5.Kind) (lft rgt : Term) : Env Term := mk op #[lft, rgt]
def mk3 (op : cvc5.Kind) (t1 t2 t3 : Term) : Env Term := mk op #[t1, t2, t3]

def mkNot : Term → Env Term := mk1 .NOT

def mkEq : Term → Term → Env Term := mk2 .EQUAL
def mkLt : Term → Term → Env Term := mk2 .LT
def mkLe : Term → Term → Env Term := mk2 .LEQ
def mkEq0 (term : Term) : Env Term := mkInt 0 >>= mkEq term
def mkLt0 (term : Term) : Env Term := mkInt 0 >>= mkLt term
def mkLe0 (term : Term) : Env Term := mkInt 0 >>= mkLe term
def mkAdd : Term → Term → Env Term := mk2 .ADD
def mkSub : Term → Term → Env Term := mk2 .SUB
def mkIte : Term → Term → Term → Env Term := mk3 .ITE

end Cvc5.Term



namespace Cvc5.Solver

def check (assuming : Array Term := #[]) (solver : Solver) : Env Bool := do
  let res ← solver.checkSatAssuming assuming
  if res.isSat then return true
  if res.isUnsat then return false
  throw <| cvc5.Error.error s!"unexpected *unknown* check-sat result"

end Cvc5.Solver



namespace Test.Monadic

open Cvc5 (EnvIO Term Solver Srt)



structure TSys.Spec (SVars : Type) where
  sVarsAt (k : Nat) : EnvIO SVars
  sVarsToString : SVars → Array String
  init : SVars → EnvIO Term
  step : (curr : SVars) → (next : SVars) → EnvIO Term
  getValues : Solver → SVars → EnvIO SVars
  candidate : SVars → EnvIO Term

inductive Result (SVars : Type)
| safe (k : Nat) | cex (trace : Array SVars) | unknown

namespace Result

def isUnknown : Result SVars → Bool
| .unknown => true | _ => false

end Result

structure TSys (SVars : Type) extends TSys.Spec SVars where private mk' ::
  sVars : SVars × List SVars
  baseSolver : Solver
  stepSolver : Solver

namespace TSys

def mk (spec : Spec SVars) : EnvIO (TSys SVars) := do
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

def negCandidate (sVars : SVars) (sys : TSys SVars) : EnvIO Term := do
  sys.candidate sVars >>= liftM ∘ Term.mkNot

def currK (sys : TSys SVars) : Nat := sys.sVars.snd.length
def currSVars (sys : TSys SVars) : SVars := sys.sVars.fst
def allPreSVars (sys : TSys SVars) : List SVars := sys.sVars.snd
def stageNextSVars (sys : TSys SVars) : EnvIO (SVars × TSys SVars) := do
  let next ← sys.sVarsAt sys.currK.succ
  let sVars := (next, sys.currSVars :: sys.allPreSVars)
  return (next, {sys with sVars})

abbrev Trace (_ : TSys SVars) := Array SVars
abbrev Trace? (sys : TSys SVars) := Option sys.Trace
protected abbrev Result (_ : TSys SVars) := Result SVars

def printTrace (sys : TSys SVars) (trace : sys.Trace) (pref := "") : EnvIO Unit := do
  let mut cnt := 0
  let k := sys.currK
  for sVars in trace do
    let k := k - cnt
    cnt := cnt + 1
    let lines := sys.sVarsToString sVars
    println! "{pref}- at {k}"
    for line in lines do
      println! "{pref}  {line}"

def getCex (solver : Solver) (sys : TSys SVars) : EnvIO sys.Trace := do
  let mut trace := Array.mkEmpty sys.sVars.snd.length
  trace := trace.push (← sys.getValues solver sys.currSVars)
  for sVars in sys.allPreSVars do
    trace := trace.push (← sys.getValues solver sVars)
  return trace

def getBaseCex (sys : TSys SVars) : EnvIO sys.Trace :=
  sys.getCex sys.baseSolver

def getStepCex (sys : TSys SVars) : EnvIO sys.Trace :=
  sys.getCex sys.stepSolver

def getCex? (solver : Solver) (sys : TSys SVars)
: EnvIO sys.Trace? := do
  let bad ← sys.negCandidate sys.currSVars
  let isSat ← solver.check #[bad]
  if isSat then sys.getCex solver else return none

def getBaseCex? (sys : TSys SVars) : EnvIO sys.Trace? := do
  sys.getCex? sys.baseSolver

def getStepCex? (sys : TSys SVars) : EnvIO sys.Trace? := do
  sys.getCex? sys.stepSolver

def unroll (sys : TSys SVars) : EnvIO (TSys SVars) := do
  let curr := sys.currSVars
  let currCandidate ← sys.candidate curr
  let (next, sys) ← sys.stageNextSVars
  let step ← sys.step curr next
  sys.baseSolver.assert step
  sys.stepSolver.assert currCandidate
  sys.stepSolver.assert step
  return sys

def checkBaseUnrollCheckStep (sys : TSys SVars) : EnvIO (sys.Result × TSys SVars) := do
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


def check' (sys : TSys SVars) : (maxK : Nat := 5) → EnvIO (sys.Result × TSys SVars)
| 0 => return (.unknown, sys)
| maxK + 1 => do
  let (res, sys) ← sys.checkBaseUnrollCheckStep
  if res.isUnknown then sys.check' maxK else return (res, sys)

def check (sys : TSys SVars) (maxK : Nat := 5) : EnvIO sys.Result :=
  Prod.fst <$> sys.check' maxK

end TSys



namespace Sw

structure SVars where
  startStop : Term
  reset : Term
  isCounting : Term
  counter : Term

def Spec (candidate : SVars → EnvIO Term) : TSys.Spec SVars where
  sVarsAt k := do
    let bool ← Srt.getBool
    let int ← Srt.getInt
    return ⟨
      ← Cvc5.Term.mkConst s!"startStop@{k}" bool,
      ← Cvc5.Term.mkConst s!"reset@{k}" bool,
      ← Cvc5.Term.mkConst s!"isCounting@{k}" bool,
      ← Cvc5.Term.mkConst s!"counter@{k}" int,
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
    let notCounting ← vars.reset.mkNot
    let counterGe0 ← (← Term.mkInt 0) |>.mkLe vars.counter
    let init ← Term.mkAnd #[notCounting, counterGe0]
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

def counterPos (vars : SVars) : EnvIO Term := do
  (← Term.mkInt 0) |>.mkLe vars.counter

def counterNotMinus7 (vars : SVars) : EnvIO Term := do
  let eqM7 ← vars.counter.mkEq (← Term.mkInt (-7))
  eqM7.mkNot

def resetImpliesCounterIs0 (vars : SVars) : EnvIO Term := do
  let notReset ← vars.reset.mkNot
  let counterIs0 ← vars.counter.mkEq (← Term.mkInt 0)
  Term.mkOr #[notReset, counterIs0]

def allCandidates (vars : SVars) : EnvIO Term := do Term.mkAnd #[
  ← counterPos vars,
  ← counterNotMinus7 vars,
  ← resetImpliesCounterIs0 vars,
]

def test' (candidate : SVars → EnvIO Term) : IO (Option Term) := Cvc5.Env.run do
  let sys ← TSys.mk <| Sw.Spec candidate
  let (res, sys) ← sys.check'
  match res with
  | .safe k =>
    println! "candidate is {k}-inductive"
    return ← sys.candidate sys.currSVars
  | .cex trace =>
    println! "found a counterexample"
    sys.printTrace trace
    return none
  | .unknown =>
    println! "could not reach a conclusion"
    return none

def test (candidate : SVars → EnvIO Term) : IO Unit := Cvc5.Env.run do
  let _ ← test' candidate
  return ()


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


def run (candidate : SVars → EnvIO Term) : IO Unit := do
  if let some invariant ← test' candidate then
    let _ ← test fun vars => do
      let other ← counterPos vars
      Term.mkAnd #[invariant, other]
  else println! "no invariant found"


/-- info:
candidate is 1-inductive
error: cvc5.Error.error "invalid term in 'children' at index 0, expected a term associated with this term manager"
error: cvc5.Error.error
  "cvc5.Error.error \"invalid term in 'children' at index 0, expected a term associated with this term manager\""
---
error: cvc5.Error.error
  "cvc5.Error.error \"invalid term in 'children' at index 0, expected a term associated with this term manager\""
-/
#guard_msgs in #eval run counterPos
