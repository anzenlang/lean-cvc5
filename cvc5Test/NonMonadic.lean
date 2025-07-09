import cvc5



namespace Cvc5.NonMonadic

namespace Term.Manager variable (manager : Term.Manager ω)

def mkAnd : (terms : Array (Term ω)) → Res (Term ω) := manager.mkTerm .AND
def mkOr : (terms : Array (Term ω)) → Res (Term ω) := manager.mkTerm .OR

def mk1 (op : cvc5.Kind) (term : Term ω) : Res (Term ω) := manager.mkTerm op #[term]
def mk2 (op : cvc5.Kind) (lft rgt : Term ω) : Res (Term ω) := manager.mkTerm op #[lft, rgt]
def mk3 (op : cvc5.Kind) (t1 t2 t3 : Term ω) : Res (Term ω) := manager.mkTerm op #[t1, t2, t3]

def mkNot : Term ω → Res (Term ω) := manager.mk1 .NOT

def mkEq : Term ω → Term ω → Res (Term ω) := manager.mk2 .EQUAL
def mkImplies : Term ω → Term ω → Res (Term ω) := manager.mk2 .IMPLIES
def mkLt : Term ω → Term ω → Res (Term ω) := manager.mk2 .LT
def mkLe : Term ω → Term ω → Res (Term ω) := manager.mk2 .LEQ
def mkEq0 (term : Term ω) : Res (Term ω) := manager.mkEq (manager.mkInt 0) term
def mkAdd : Term ω → Term ω → Res (Term ω) := manager.mk2 .ADD
def mkSub : Term ω → Term ω → Res (Term ω) := manager.mk2 .SUB
def mkIte : Term ω → Term ω → Term ω → Res (Term ω) := manager.mk3 .ITE

end Term.Manager

end Cvc5.NonMonadic



namespace Test.Monadic

open Cvc5.NonMonadic


def checkSat (assuming : Array (Term ω) := #[]) : SolverM ω Bool := do
  let res ← checkSatAssuming assuming
  if res.isSat then return true
  if res.isUnsat then return false
  throw <| cvc5.Error.error s!"unexpected *unknown* check-sat result"


structure TSys.Spec (ω : Type) (SVars : Type → Type) where
  sVarsAt (manager : Term.Manager ω) (k : Nat) : Res (SVars ω)
  sVarsToString : (SVars ω) → Array String
  init (manager : Term.Manager ω) : (SVars ω) → Res (Term ω)
  step (manager : Term.Manager ω) : (curr : SVars ω) → (next : SVars ω) → Res (Term ω)
  getValues : (SVars ω) → SolverM ω (SVars ω)
  candidate (manager : Term.Manager ω) : (SVars ω) → Res (Term ω)

inductive Result (SVars : Type)
| safe (k : Nat) | cex (trace : Array SVars) | unknown

namespace Result

def isUnknown : Result SVars → Bool
| .unknown => true | _ => false

instance : ToString (Result α) := ⟨fun
  | safe k => s!"{k}-invariant"
  | cex trace => s!"cex of length {trace.size}"
  | unknown => "unknown"
⟩

end Result



-- structure TSys (ω : Type) (SVars : Type → Type) extends TSys.Spec ω SVars where private mk' ::
--   manager : Term.Manager ω
--   sVars : SVars ω × List (SVars ω)
--   baseSolver : Solver ω
--   stepSolver : Solver ω

-- namespace TSys

-- def mk (spec : Spec ω SVars) (manager : Term.Manager ω) : ResIO (TSys ω SVars) := do
--   let sVars0 ← spec.sVarsAt manager 0

--   let baseSolver := Solver.mk manager
--   println! "base"
--   let init0 ← spec.init manager sVars0
--   println! "  init@0 = {init0}"
--   baseSolver.setOption "produce-models" "true"
--   baseSolver.assert init0
--   println! "  checking..."
--   let _ ← baseSolver.check

--   let stepSolver := Solver.mk manager
--   stepSolver.setLogic "QF_LIA"
--   println! "step"
--   stepSolver.setOption "produce-models" "true"
--   let candidate0 ← spec.candidate manager sVars0
--   println! "candidate@0 = {candidate0}"
--   stepSolver.assert candidate0
--   println! "  checking..."
--   let _ ← stepSolver.check

--   println! "base again\n  checking..."
--   let _ ← baseSolver.check
--   return ⟨spec, manager, (sVars0, []), baseSolver, stepSolver⟩

-- def negCandidate (sVars : SVars ω) (sys : TSys ω SVars) : Res (Term ω) := do
--   sys.candidate sys.manager sVars >>= sys.manager.mkNot

-- def currK (sys : TSys ω SVars) : Nat := sys.sVars.snd.length
-- def currSVars (sys : TSys ω SVars) : SVars ω := sys.sVars.fst
-- def allPreSVars (sys : TSys ω SVars) : List (SVars ω) := sys.sVars.snd
-- def stageNextSVars (sys : TSys ω SVars) : Res (SVars ω × TSys ω SVars) := do
--   let next ← sys.sVarsAt sys.manager sys.currK.succ
--   let sVars := (next, sys.currSVars :: sys.allPreSVars)
--   return (next, {sys with sVars})

-- abbrev Trace (_ : TSys ω SVars) := Array (SVars ω)
-- abbrev Trace? (sys : TSys ω SVars) := Option sys.Trace
-- protected abbrev Result (_ : TSys ω SVars) := Result (SVars ω)

-- def printTrace (sys : TSys ω SVars) (trace : sys.Trace) (pref := "") : ResIO Unit := do
--   let mut cnt := 0
--   let k := sys.currK
--   for sVars in trace do
--     let k := k - cnt
--     cnt := cnt + 1
--     let lines := sys.sVarsToString sVars
--     println! "{pref}- at {k}"
--     for line in lines do
--       println! "{pref}  {line}"

-- def getCex (solver : Solver ω) (sys : TSys ω SVars) : Res sys.Trace := do
--   let mut trace := Array.mkEmpty sys.sVars.snd.length
--   trace := trace.push (← sys.getValues solver sys.currSVars)
--   for sVars in sys.allPreSVars do
--     trace := trace.push (← sys.getValues solver sVars)
--   return trace

-- def getBaseCex (sys : TSys ω SVars) : Res sys.Trace :=
--   sys.getCex sys.baseSolver

-- def getStepCex (sys : TSys ω SVars) : Res sys.Trace :=
--   sys.getCex sys.stepSolver

-- def getCex? (solver : Solver ω) (sys : TSys ω SVars) : ResIO sys.Trace? := do
--   let bad ← sys.negCandidate sys.currSVars
--   println! "bad = {bad}"
--   let isSat ← solver.check #[bad]
--   if isSat then sys.getCex solver else return none

-- def getBaseCex? (sys : TSys ω SVars) : ResIO sys.Trace? :=
--   sys.getCex? sys.baseSolver

-- def getStepCex? (sys : TSys ω SVars) : ResIO sys.Trace? :=
--   sys.getCex? sys.stepSolver

-- def unroll (sys : TSys ω SVars) : ResIO (TSys ω SVars) := do
--   let curr := sys.currSVars
--   let currCandidate ← sys.candidate sys.manager curr
--   println! "current candidate = {currCandidate}"
--   let (next, sys) ← sys.stageNextSVars
--   let step ← sys.step sys.manager curr next
--   println! "step = {step}"
--   sys.baseSolver.assert step
--   sys.stepSolver.assert currCandidate
--   sys.stepSolver.assert step
--   return sys

-- def checkBaseUnrollCheckStep (sys : TSys ω SVars) : ResIO (sys.Result × TSys ω SVars) := do
--   println! "checking base at {sys.currK}"
--   if let some baseCex ← sys.getBaseCex? then
--     return (.cex baseCex, sys)
--   else
--     println! "unrolling..."
--     let sys ← sys.unroll
--     println! "checking step at {sys.currK}"
--     if let some _stepCex ← sys.getStepCex? then
--       println! "step cex at {sys.currK}"
--       -- sys.printTrace stepCex
--       return (.unknown, sys)
--     else
--       return (.safe sys.currK, sys)


-- def check' (sys : TSys ω SVars) : (maxK : Nat := 5) → ResIO (sys.Result × TSys ω SVars)
-- | 0 => return (.unknown, sys)
-- | maxK + 1 => do
--   let (res, sys) ← sys.checkBaseUnrollCheckStep
--   if res.isUnknown then sys.check' maxK else return (res, sys)

-- def check (sys : TSys ω SVars) (maxK : Nat := 5) : ResIO sys.Result :=
--   Prod.fst <$> sys.check' maxK

-- end TSys



-- namespace Sw

-- structure SVars (ω : Type) where
--   startStop : (Term ω)
--   reset : (Term ω)
--   isCounting : (Term ω)
--   counter : (Term ω)

-- def Spec
--   (candidate : {ω : Type} → Term.Manager ω → SVars ω → Res (Term ω))
-- : TSys.Spec ω SVars where
--   sVarsAt manager k := do
--     let bool := manager.getBoolSrt
--     let int := manager.getIntSrt
--     return ⟨
--       manager.freshConst s!"startStop@{k}" bool,
--       manager.freshConst s!"reset@{k}" bool,
--       manager.freshConst s!"isCounting@{k}" bool,
--       manager.freshConst s!"counter@{k}" int,
--     ⟩
--   getValues solver vars := return ⟨
--     ← solver.getValue vars.startStop,
--     ← solver.getValue vars.reset,
--     ← solver.getValue vars.isCounting,
--     ← solver.getValue vars.counter,
--   ⟩
--   sVarsToString vals := #[
--     s!"counter = {vals.counter}, isCounting = {vals.isCounting}",
--     s!"startStop = {vals.startStop}, reset = {vals.reset}",
--   ]
--   init manager vars := do
--     let notCounting ← manager.mkNot vars.isCounting
--     let counterGe0 ← manager.mkLe (manager.mkInt 0) vars.counter
--     let onReset ← manager.mkImplies vars.reset (← manager.mkEq0 vars.counter)
--     let init ← manager.mkAnd #[notCounting, counterGe0, onReset]
--     return init
--   step manager curr next := do
--     let isCountingDef ←
--       manager.mkIte next.startStop (← manager.mkNot curr.isCounting) curr.isCounting
--     let counterIncIfCounting ←
--       manager.mkAdd curr.counter
--         (← manager.mkIte next.isCounting (manager.mkInt 1) (manager.mkInt 0))
--     let counterDef ← manager.mkIte next.reset (manager.mkInt 0) counterIncIfCounting
--     manager.mkAnd #[
--       ← manager.mkEq next.isCounting isCountingDef,
--       ← manager.mkEq next.counter counterDef,
--     ]
--   candidate

-- section variable (manager : Term.Manager ω)

-- def counterPos(vars : SVars ω) : Res (Term ω) := do
--   manager.mkLe (manager.mkInt 0) vars.counter

-- def counterNotMinus7 (vars : SVars ω) : Res (Term ω) := do
--   let eqM7 ← manager.mkEq vars.counter (manager.mkInt (-7))
--   manager.mkNot eqM7

-- def resetImpliesCounterIs0 (vars : SVars ω) : Res (Term ω) := do
--   let notReset ← manager.mkNot vars.reset
--   let counterIs0 ← manager.mkEq vars.counter (manager.mkInt 0)
--   manager.mkOr #[notReset, counterIs0]

-- def allCandidates (vars : SVars ω) : Res (Term ω) := do manager.mkAnd #[
--   ← counterPos manager vars,
--   ← counterNotMinus7 manager vars,
--   ← resetImpliesCounterIs0 manager vars,
-- ]

-- /--

-- Can write this function, but the output `Term ω` is only useable inside a `Cvc5.Env.run`.

-- See `run` below.

-- -/
-- def test
--   (candidate : {ω : Type} → Term.Manager ω → SVars ω → Res (Term ω))
-- : IO Unit := do
--   let manager : Term.Manager Unit ← Term.Manager.mk
--   let code : ResIO Unit := do
--     let sys ← TSys.mk (Sw.Spec candidate) manager
--     let (res, sys) ← sys.check'
--     match res with
--     | .safe k =>
--       println! "candidate is {k}-inductive"
--     | .cex trace =>
--       println! "found a counterexample"
--       sys.printTrace trace
--     | .unknown =>
--       println! "could not reach a conclusion"
--   if let .error e ← code.toIO then
--     println! "error: {e}"


-- /-- info:
-- candidate is 1-inductive
-- -/
-- #guard_msgs in #eval test counterPos

-- #eval test (fun manager _ => return manager.mkBool false)

-- /-- info:
-- step cex at 1
-- step cex at 2
-- step cex at 3
-- step cex at 4
-- step cex at 5
-- could not reach a conclusion
-- -/
-- #guard_msgs in #eval test counterNotMinus7

-- /-- info:
-- candidate is 1-inductive
-- -/
-- #guard_msgs in #eval test resetImpliesCounterIs0

-- /-- info:
-- candidate is 1-inductive
-- -/
-- #guard_msgs in #eval test allCandidates

-- /--

-- Can write this function, but the output `Term ω` is only useable inside a `Cvc5.Env.run`.

-- See `run` below.

-- -/
-- def test'
--   (candidate : {ω : Type} → Term.Manager ω → SVars ω → Res (Term ω))
-- : ResIO (Option (Term ω)) := do
--   let manager ← Term.Manager.mk
--   let sys ← TSys.mk (Sw.Spec candidate) manager
--   let (res, sys) ← sys.check'
--   match res with
--   | .safe k =>
--     println! "candidate is {k}-inductive"
--     return ← some <$> sys.candidate manager sys.currSVars
--   | .cex trace =>
--     println! "found a counterexample"
--     sys.printTrace trace
--     return none
--   | .unknown =>
--     println! "could not reach a conclusion"
--     return none



-- /-- error:
-- invalid match-expression, type of pattern variable 'invariant' contains metavariables
--   Term ?m.20261
-- -/
-- #guard_msgs in def run (candidate : {ω : Type} → SVars ω → EnvIO ω (Term ω)) : IO Unit := do
--   if let some invariant ← test' candidate then
--     println! "found an invariant: {invariant}"
--     test fun _ => return invariant
--   else println! "no invariant found"
