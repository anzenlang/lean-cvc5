import Cvc5Test.Init

namespace cvc5.Test

/-- info:
max = (lambda ((x Int) (y Int)) (ite (<= x y) y x))
min = (lambda ((x Int) (y Int)) (ite (<= x y) x y))
-/
test! tm => do
  -- from <https://github.com/cvc5/cvc5/blob/22f661b69ec1e56dc35f80a7c2c939bf09e14871/examples/api/cpp/sygus-fun.cpp>

  Solver.setOption "sygus" "true"
  Solver.setOption "incremental" "false"

  Solver.setLogic "LIA"

  let int := tm.getIntegerSort
  let bool := tm.getBooleanSort

  -- declare input variables for the functions-to-synthesize
  let x := tm.mkVar int "x"
  let y := tm.mkVar int "y"

  -- declare the grammar non-terminals
  let start := tm.mkVar int "Start"
  let startBool := tm.mkVar bool "StartBool"

  -- define the rules
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1

  let plus ← tm.mkTerm .ADD #[start, start]
  let minus ← tm.mkTerm .SUB #[start, start]
  let ite ← tm.mkTerm .ITE #[startBool, start, start]

  let and ← tm.mkTerm .AND #[startBool, startBool]
  let not ← tm.mkTerm .NOT #[startBool]
  let leq ← tm.mkTerm .LEQ #[start, start]

  -- create the grammar object
  let grammar ← Solver.mkGrammar #[x, y] #[start, startBool]

  -- bind each non-terminal to its rules
  let grammar' := grammar.addRules start #[zero, one, x, y, plus, minus, ite]
  let grammar'' := grammar'.addRules startBool #[and, not, leq]

  -- declare the functions-to-synthesize. Optionally, provide the grammar constraints
  let max ← Solver.synthFunWith "max" #[x, y] int grammar''
  let min ← Solver.synthFun "min" #[x, y] int

  -- declare universal variables
  let varX ← Solver.declareSygusVar "x" int
  let varY ← Solver.declareSygusVar "y" int

  let max_x_y ← tm.mkTerm .APPLY_UF #[max, varX, varY]
  let min_x_y ← tm.mkTerm .APPLY_UF #[min, varX, varY]

  -- add semantic constraints
  -- `max x y ≥ x`
  Solver.addSygusConstraint (← tm.mkTerm .GEQ #[max_x_y, varX])
  -- `max x y ≥ y`
  Solver.addSygusConstraint (← tm.mkTerm .GEQ #[max_x_y, varY])
  -- `(x = max x y) ∨ (y = max x y)`
  Solver.addSygusConstraint (← tm.mkTerm .OR #[
    ← tm.mkTerm .EQUAL #[max_x_y, varX],
    ← tm.mkTerm .EQUAL #[max_x_y, varY]
  ])
  -- `(max x y) + (min x y) = x + y`
  Solver.addSygusConstraint (← tm.mkTerm .EQUAL #[
    ← tm.mkTerm .ADD #[max_x_y, min_x_y],
    ← tm.mkTerm .ADD #[varX, varY]
  ])

  -- print solutions if available
  if (← Solver.checkSynth).hasSolution then
    let solutions ← Solver.getSynthSolutions #[max, min]
    println! "max = {solutions.get! 0}"
    println! "min = {solutions.get! 1}"
  else
    println! "unexpected: synthesis problem has no solution"
