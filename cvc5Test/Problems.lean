import cvc5



/-- Helper function. -/
def Except.expect [ToString ε] [Inhabited α] (s : String) : Except ε α → IO α
  | .ok a => return a
  | .error e => do
    println! s!"cannot unwrap `ExceptT.error` value\n{s}\nerror: {e}"
    return default

namespace cvc5

def run1 : IO Term := do
  let tm ← TermManager.new
  let zero := tm.mkInteger 0
  let seven := tm.mkInteger 7
  tm.mkTerm .EQUAL #[zero, seven] |>.expect "[run1] mkTerm .EQUAL"

def run2 (term : Term) : IO Term := do
  let tm ← TermManager.new
  let tru := tm.mkBoolean true
  tm.mkTerm .AND #[term, tru] |>.expect "[run2] mkTerm .AND"

/--
```
can use terms after their manager's death: (= 0 7)
cannot unwrap `ExceptT.error` value
[run2] mkTerm .AND
error: cvc5.Error.error "invalid term in 'children' at index 0, expected a term associated with this term manager"
no problem using terms from a manager with a different manager: null
```
-/
def testCrossTm : IO Unit := do
  let term1 ← run1
  println! "can use terms after their manager's death: {term1}"
  let term2 ← run2 term1
  println! "no problem using terms from a manager with a different manager: {term2}"



def runParallel (tm : TermManager) : Array Term := Id.run do
  let mut tasks := #[]
  for n in [0:100000] do
    tasks := tasks.push <| Task.spawn fun () => tm.mkInteger n
  let mut terms := #[]
  for task in tasks do
    terms := terms.push task.get
  return terms

/--
Non-deterministic, `#eval`-ing this function crashes the lean LSP server
-/
def testPara : IO Unit := do
  let tm ← TermManager.new
  let terms := runParallel tm
  println! "done building {terms.size} terms"
