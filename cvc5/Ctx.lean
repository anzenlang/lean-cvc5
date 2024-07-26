/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Init
import cvc5.Term.Manager
import cvc5.Solver



namespace cvc5

/-- A cvc5 context: a `Term.Manager` and a `Solver`. -/
structure Ctx where private mkRaw ::
  private termManager : Term.Manager
  private solver : Solver

/-- Cvc5 context error-state monad transformer. -/
abbrev CtxT M := ExceptT Error (StateT Ctx M)

/-- Cvc5 context errot-state IO monad. -/
abbrev CtxM := CtxT IO



namespace Ctx

/-- Constructor. -/
def mk [Monad M] [MonadLiftT BaseIO M] : M Ctx := do
  let tm ← Term.Manager.mk
  let solver := Solver.mk tm
  return ⟨tm, solver⟩

/-- Runs some monadic `Ctx` code. -/
def run
  [instMonad : Monad M] [MonadLiftT BaseIO M]
  (code : CtxT M α)
: ExceptT Error M α := do
  let ctx ← mk
  match ← code ctx with
  | (.ok res, _) => instMonad.pure (.ok res)
  | (.error err, _) => instMonad.pure (.error err)

/-- Runs some monadic `Ctx` code, `panic!`-s on errors. -/
def run!
  [Inhabited α]
  [Monad M] [MonadLiftT BaseIO M]
  (code : CtxT M α)
: M α := do
  match ← run code with
  | Except.ok res => return res
  | .error err => panic! s!"error: {err}"



variable [instMonad : Monad M]



def solverRun (code : SolverT M α) : CtxT M α :=
  fun ctx => do
    let (res, solver) ← code ctx.solver
    return (res, {ctx with solver})

instance instMonadLiftSolverT : MonadLift (SolverT M) (CtxT M) :=
  ⟨solverRun⟩



/-! ## `Term.Manager`/`Solver` access and manipulation -/

private def getTerm.Manager : CtxT M Term.Manager :=
  fun ctx => return (.ok ctx.termManager, ctx)

private def termManagerDoM (f : Term.Manager → CtxT M α) : CtxT M α :=
  fun ctx => f ctx.termManager ctx

private def termManagerDo (f : Term.Manager → α) : CtxT M α :=
  fun ctx => return (.ok <| f ctx.termManager, ctx)

private def getSolver : CtxT M Solver :=
  fun ctx => return (.ok ctx.solver, ctx)



/-! ## `Term.Manager` monadic functions -/

@[inherit_doc Term.Manager.mkBoolean]
def mkBool (b : Bool) : CtxT M Term :=
  termManagerDo fun tm => tm.mkBoolean b

@[inherit_doc Term.Manager.mkInteger]
def mkInt (i : Int) : CtxT M Term :=
  termManagerDo fun tm => tm.mkInteger i

@[inherit_doc Term.Manager.mkTerm]
def mkTerm (k : Kind) (kids : Array Term := #[]) : CtxT M Term :=
  termManagerDo fun tm => tm.mkTerm k kids

@[inherit_doc Term.Manager.mkIte]
def mkIte (cnd thn els : Term) : CtxT M Term :=
  termManagerDo fun tm => tm.mkIte cnd thn els

@[inherit_doc Term.Manager.mkEqualN]
def mkEqualN (terms : Array Term) (h : 1 < terms.size := by simp_arith) : CtxT M Term :=
  termManagerDo fun tm => tm.mkEqualN terms h

@[inherit_doc Term.Manager.mkEqual]
def mkEqual (lft rgt : Term) : CtxT M Term :=
  termManagerDo fun tm => tm.mkEqual lft rgt



/-! ## `Solver` monadic functions -/

@[inherit_doc Solver.getVersion]
def getVersion : CtxT M String :=
  Solver.getVersion
  |> solverRun

@[inherit_doc Solver.setOption]
def setOption (option value : String) : CtxT M Unit :=
  Solver.setOption option value
  |> solverRun

@[inherit_doc Solver.setLogic]
def setLogic (logic : String) : CtxT M Unit :=
  Solver.setLogic logic
  |> solverRun

@[inherit_doc Solver.getOption]
def getOption (option : String) : CtxT M String :=
  Solver.getOption option
  |> solverRun

@[inherit_doc Solver.assertFormula]
def assertFormula (term : Term) : CtxT M Unit :=
  Solver.assertFormula term
  |> solverRun

@[inherit_doc Solver.checkSat]
def checkSat : CtxT M Result :=
  Solver.checkSat
  |> solverRun

@[inherit_doc Solver.getProof]
def getProof : CtxT M (Array Proof) :=
  Solver.getProof
  |> solverRun

@[inherit_doc Solver.proofToString]
def proofToString (proof : Proof) : CtxT M String :=
  Solver.proofToString proof
  |> solverRun

@[inherit_doc Solver.parse]
def parse (smtLib : String) : CtxT M Unit :=
  Solver.parse smtLib
  |> solverRun



@[inherit_doc Solver.declareFun]
def declareFun
  (symbol : String)
  (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
  (fresh : Bool := false)
: CtxT M Term :=
  Solver.declareFun symbol in_sorts out_sort fresh
  |> solverRun

@[inherit_doc Solver.declareFreshFun]
def declareFreshFun
  (symbol : String) (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
: CtxT M Term :=
  Solver.declareFreshFun symbol in_sorts out_sort
  |> solverRun

@[inherit_doc Solver.declareSort]
def declareSort
  (symbol : String) (arity: Nat) (fresh : Bool := false)
: CtxT M Sort :=
  Solver.declareSort symbol arity fresh
  |> solverRun

@[inherit_doc Solver.declareFreshSort]
def declareFreshSort (symbol : String) (arity : Nat) : CtxT M Sort :=
  Solver.declareFreshSort symbol arity
  |> solverRun



@[inherit_doc Solver.getAssertions]
def getAssertions : CtxT M (Array Term) :=
  Solver.getAssertions
  |> solverRun

@[inherit_doc Solver.getUnsatAssumptions]
def getUnsatAssumptions : CtxT M (Array Term) :=
  Solver.getUnsatAssumptions
  |> solverRun

@[inherit_doc Solver.getUnsatCore]
def getUnsatCore : CtxT M (Array Term) :=
  Solver.getUnsatCore
  |> solverRun

@[inherit_doc Solver.getUnsatCoreLemmas]
def getUnsatCoreLemmas : CtxT M (Array Term) :=
  Solver.getUnsatCoreLemmas
  |> solverRun

@[inherit_doc Solver.getInfo]
def getInfo (flag : String) : CtxT M String :=
  Solver.getInfo flag
  |> solverRun

@[inherit_doc Solver.getOptionNames]
def getOptionNames : CtxT M (Array String) :=
  Solver.getOptionNames
  |> solverRun



@[inherit_doc Solver.getValue]
def getValue (term : Term) : CtxT M Term :=
  Solver.getValue term
  |> solverRun

@[inherit_doc Solver.getValues]
def getValues (terms : Array Term) : CtxT M (Array Term) :=
  Solver.getValues terms
  |> solverRun
