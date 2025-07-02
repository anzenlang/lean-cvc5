import cvc5



namespace cvc5.Test



namespace RaceCondition

def context (blah : String) (code : ReaderT σ (EST Error ω) α) : ReaderT σ (EST Error ω) α :=
  fun state world =>
    match code state world with
    | .ok res state => .ok res state
    | .error Error.missingValue state => .error (Error.error s!"{blah}\nmissing value") state
    | .error (Error.error err) state
    | .error (Error.recoverable err) state
    | .error (Error.option err) state
    | .error (Error.unsupported err) state => .error (Error.error s!"{blah}\n{err}") state


def Mem (ω : Type) (α : Type) [BEq α] [Hashable α] := ST.Ref ω (Std.HashSet α)

namespace Mem variable [BEq α] [Hashable α]

protected abbrev IO := Mem IO.RealWorld

def empty : BaseIO (Mem.IO α) := ST.mkRef <| Std.HashSet.emptyWithCapacity 1000

def insert (i : α) (mem : Mem ω α) : ST ω Unit := do
  mem.modifyGet fun set => ((), set.insert i)

def checkVals (f : α → ExceptT String IO Unit) (mem : Mem.IO α) : ExceptT String IO Unit := do
  let map ← mem.get
  for val in map do f val

end Mem

def mkNeInt (term : Term) (val : Int) : Term.Env ω Term := do
  let sortKind := term.getSort.getKind
  if sortKind != .INTEGER_SORT then
    throw <| Error.error s!"term `{term}` has type `{term.getSort}`, expected `Int`"
  let rhs : Term ← Term.Manager.mkInteger! val |> context s!"mkInteger! {val}"
  let eqTerm ← Term.Manager.mkTerm .EQUAL #[term, rhs] |> context s!"mkTerm .EQUAL .."
  Term.Manager.mkTerm .NOT #[eqTerm] |> context s!"mkTerm .NOT .."

def randInt (normMax : Nat := 1000) : BaseIO Int := do
  let n ← IO.rand 0 normMax
  let neg ← (· == 1) <$> IO.rand 0 1
  return if neg then - n else n

def genTerm (lhs : Term) (valMem : Mem.IO Int) (normMax : Nat := 1000) : Term.Env.IO Term := do
  let i ← randInt normMax
  valMem.insert i
  mkNeInt lhs i

def genTerms (n : Nat) (lhs : Term)
  (valMem : Mem.IO Int) (termMem : Mem.IO Term) (normMax : Nat := 1000)
: Term.Env.IO Unit := do
  for _ in [0:n] do
    let term ← genTerm lhs valMem normMax |> context "during term gen"
    termMem.insert term



def runTest (taskCount : Nat) (genCount : Nat) (normMax : Nat := 1000) : IO Unit := do
  -- stores `Int` values
  let valMem ← Mem.empty
  -- stores `Term` values
  let termMem ← Mem.empty

  let manager ← Term.mkManager

  let x ← manager.run! do
    let intSort ← Term.Manager.getIntegerSort
    Term.Manager.mkConst intSort "x"
  println! "created `{x} : {x.getSort}`"

  println! "spawning {taskCount} tasks to `{x} ≠ i` terms for {genCount} random values of `i : Int`"
  let mut termTasks := Array.emptyWithCapacity taskCount
  for n in [0:taskCount] do
    let task ← IO.asTask do
      manager.run! (genTerms genCount x valMem termMem normMax)
      println! "  thread #{n.succ} is done"
    termTasks := termTasks.push task
  println! "waiting for tasks to finish"
  for task in termTasks do
    match task.get with
    | .ok () => pure ()
    | .error e =>
      println! "an error occurred"
      println! "  {e}"
      return ()

  let valCount := (← valMem.get).size
  let termCount := (← termMem.get).size
  println! "created {termCount} different term(s) --- {valCount} different value(s)"

  let solver ← manager.mkSolver

  solver.run! (Cvc.setOption "produce-models" "true")

  println! "asserting all terms"
  -- let mut assertTasks := Array.emptyWithCapacity taskCount
  let mut cnt := 0
  for term in ← termMem.get do
    let n := cnt
    cnt := cnt + 1
    -- let task ← IO.asTask do
    solver.run! (Cvc.assertFormula term)
    println! "  thread #{n.succ} is done"
    -- assertTasks := assertTasks.push task
  -- wait for tasks to finish
  -- for task in assertTasks do
  --   match task.get with
  --   | .ok () => pure ()
  --   | .error e => throw e
  println! "all assertion tasks done"

  -- done, get a value for `x`
  let value ← solver.run! do
    let result ← Cvc.checkSat
    if ¬ result.isSat then
      throw <| Error.error "expected sat result 🙀"
    let value ← Cvc.getValue x
    if let some value := value.getIntegerValue?
    then pure value
    else throw <| Error.error s!"unexpected value for `x`: `{value}`"

  println! "got a value for `x`: `{value}`"
  -- if everything went fine, `value` should be different from all `Int`s in `valMem`
  let ok? ← valMem.checkVals fun i => do
    if i = value then .error s!"`valMem` indicates value `{value}` is impossible for `x`"
    else
      println! "- confirmed ≠ {i}"
      pure ()
  if let .error e := ok? then
    println! "❌ something went wrong:"
    println! "{e}"
  else
    println! "✅ all good"

  println! "done"



-- #eval runTest 10 300

def _root_.main : IO Unit :=
  cvc5.Test.RaceCondition.runTest 10 10 100_000
