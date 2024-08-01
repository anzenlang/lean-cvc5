/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Smt.Basic



namespace cvc5

namespace Safe

/-- This type is meant as a parameter for `Smt` and its related monads.

However we need a custom (error-)state monad for that since we need to be able to transition from a
`Smt k` to `Smt k'`. Maybe, I'm not sure it would be very ergonomic.
-/
inductive Kind
| noLogic
| sat
| unsat
| unknown

/-- A cvc5 context: a `Term.Manager` and a `Solver`. -/
structure Smt where private mkRaw ::
  private toSmt : cvc5.Smt

/-- Cvc5 context error-state monad transformer. -/
abbrev SmtT m := ExceptT Error (StateT Smt m)

instance [Monad m] : MonadExceptOf Error (SmtT m) where
  throw e smt := return (.error e, smt)
  tryCatch code errorDo smt := do
    match ← code smt with
    | (.ok res, smt) => return (.ok res, smt)
    | (.error err, smt) => errorDo err smt

/-- Cvc5 context errot-state IO monad. -/
abbrev SmtM := SmtT IO
end Safe

/-- Safe version of `Smt`, only provides safe term/solver functions. -/
def Smt.toSafe (smt : Smt) : Safe.Smt :=
  ⟨smt⟩


structure SmtSat where private mkRaw ::
  private toSmt : Smt

abbrev SmtSatT m := ExceptT Error (StateT SmtSat m)

instance [Monad m] : MonadExceptOf Error (SmtSatT m) where
  throw e smt := return (.error e, smt)
  tryCatch code errorDo smtSat := do
    match ← code smtSat with
    | (.ok res, smtSat) => return (.ok res, smtSat)
    | (.error err, smtSat) => errorDo err smtSat

def SmtSat.unexpected [Monad m] : SmtSatT m α := do
  throw (.userError "unexpected check-sat result: *sat*")

private instance [Monad m] : MonadLift (SmtSatT m) (SmtT m) where
  monadLift smtSatT smt := do
    let (res, smtSat) ← smtSatT ⟨smt⟩
    return (res, smtSat.toSmt)

instance [Monad m] : MonadLift (SmtT m) (SmtSatT m) where
  monadLift smtSatT smtSat := do
    let (res, smt) ← smtSatT smtSat.toSmt
    return (res, ⟨smt⟩)



structure SmtUnsat where private mkRaw ::
  private toSmt : Smt

abbrev SmtUnsatT m := ExceptT Error (StateT SmtUnsat m)

instance [Monad m] : MonadExceptOf Error (SmtUnsatT m) where
  throw e smt := return (.error e, smt)
  tryCatch code errorDo smtUnsat := do
    match ← code smtUnsat with
    | (.ok res, smtUnsat) => return (.ok res, smtUnsat)
    | (.error err, smtUnsat) => errorDo err smtUnsat

def SmtUnsat.unexpected [Monad m] : SmtUnsatT m α := do
  throw (.userError "unexpected check-sat result: *unsat*")

private instance [Monad m] : MonadLift (SmtUnsatT m) (SmtT m) where
  monadLift smtUnsatT smt := do
    let (res, smtUnsat) ← smtUnsatT ⟨smt⟩
    return (res, smtUnsat.toSmt)

instance [Monad m] : MonadLift (SmtT m) (SmtUnsatT m) where
  monadLift smtUnsatT smtUnsat := do
    let (res, smt) ← smtUnsatT smtUnsat.toSmt
    return (res, ⟨smt⟩)



structure SmtUnknown where private mkRaw ::
  private toSmt : Smt

abbrev SmtUnknownT m := ExceptT Error (StateT SmtUnknown m)

instance [Monad m] : MonadExceptOf Error (SmtUnknownT m) where
  throw e smt := return (.error e, smt)
  tryCatch code errorDo smtUnknown := do
    match ← code smtUnknown with
    | (.ok res, smtUnknown) => return (.ok res, smtUnknown)
    | (.error err, smtUnknown) => errorDo err smtUnknown

def SmtUnknown.unexpected [Monad m] : SmtUnknownT m α := do
  throw (.userError "unexpected check-sat result: *unknown*")

private instance [Monad m] : MonadLift (SmtUnknownT m) (SmtT m) where
  monadLift smtUnknownT smt := do
    let (res, smtUnknown) ← smtUnknownT ⟨smt⟩
    return (res, smtUnknown.toSmt)

instance [Monad m] : MonadLift (SmtT m) (SmtUnknownT m) where
  monadLift smtUnknownT smtUnknown := do
    let (res, smt) ← smtUnknownT smtUnknown.toSmt
    return (res, ⟨smt⟩)



namespace Safe
namespace Smt

/-- Turns a `cvc5.Safe.Smt` into a `cvc5.Smt`. -/
def toUnsafe (smt : Smt) : cvc5.Smt :=
  smt.toSmt

/-- Constructor. -/
def mk [Monad m] [MonadLiftT BaseIO m] : m Smt := do
  let smt ← cvc5.Smt.mk
  return Smt.mkRaw smt

/-- Runs some monadic `Safe.Smt` code. -/
def run
  [instMonad : Monad m] [MonadLiftT BaseIO m]
  (code : SmtT m α)
: ExceptT Error m α := do
  let smt ← mk
  match ← code smt with
  | (.ok res, _) => instMonad.pure (.ok res)
  | (.error err, _) => instMonad.pure (.error err)

/-- Runs some monadic `Safe.Smt` code, `panic!`-s on errors by default. -/
def run!
  [Inhabited α]
  [Monad m] [MonadLiftT BaseIO m]
  (code : SmtT m α)
  (handleError : Error → m α := (panic! s!"error: {·}"))
: m α := do
  match ← run code with
  | Except.ok res => return res
  | .error err => handleError err



variable [instMonad : Monad m]



/-! # Underlying `Smt` access and lift -/

@[default_instance]
private instance instMonadLiftSmtT : MonadLift (cvc5.SmtT m) (SmtT m) where
  monadLift smtT safe := do
    let (res, toSmt) ← smtT safe.toSmt
    return (res, ⟨toSmt⟩)



/-! ## `Term.Manager`/`Solver` access and manipulation -/

private instance instMonadLiftSolverT : MonadLift (SolverT m) (SmtT m) where
  monadLift solverT safe := do
    let (res, toSmt) ← safe.toSmt.solverRun solverT
    return (res, ⟨toSmt⟩)

private def termManagerDo (f : Term.Manager → α) : SmtT m α :=
  (cvc5.Smt.termManagerDo f : cvc5.SmtT m α)

structure Term (_ : Type) : Type where
private mk ::
  toTerm : cvc5.Term

namespace Term

private instance instCoeTermSafeTerm : Coe cvc5.Term (Term α) :=
  ⟨Term.mk⟩

variable (self : Term α)

protected def toString : String :=
  self.toTerm.toString

instance : ToString (Term α) :=
  ⟨Term.toString⟩

end Term


/-! ## `Term.Manager` monadic functions -/

@[inherit_doc Term.Manager.mkBoolean]
def mkBool (b : Bool) : SmtT m (Term Bool) :=
  termManagerDo fun tm => tm.mkBoolean b

@[inherit_doc Term.Manager.mkInteger]
def mkInt (i : Int) : SmtT m (Term Int) :=
  termManagerDo fun tm => tm.mkInteger i

@[inherit_doc Term.Manager.mkTerm]
private def mkTerm (k : cvc5.Kind) (kids : Array cvc5.Term := #[]) : SmtT m cvc5.Term :=
  termManagerDo fun tm => tm.mkTerm k kids

@[inherit_doc Term.Manager.mkIte]
def mkIte (cnd : Term Bool) (thn els : Term α) : SmtT m (Term α) :=
  termManagerDo fun tm => tm.mkIte cnd.toTerm thn.toTerm els.toTerm

@[inherit_doc Term.Manager.mkEqualN]
def mkEqualN
  (terms : Array (Term α))
  (h : 1 < terms.size := by simp_arith)
: SmtT m (Term Bool) :=
  termManagerDo fun tm => tm.mkEqualN (terms.map Term.toTerm) (by simp [h])

@[inherit_doc Term.Manager.mkEqual]
def mkEqual (lft rgt : Term α) : SmtT m (Term Bool) :=
  termManagerDo fun tm => tm.mkEqual lft.toTerm rgt.toTerm

@[inherit_doc Term.Manager.mkNot]
def mkNot (t : Term Bool) : SmtT m (Term Bool) :=
  termManagerDo fun tm => tm.mkNot t.toTerm

@[inherit_doc Term.Manager.mkImplies]
def mkImplies (lhs rhs : Term Bool) : SmtT m (Term Bool) :=
  termManagerDo fun tm => tm.mkImplies lhs.toTerm rhs.toTerm



@[inherit_doc Term.Manager.mkSort]
def mkSort (α : Type) [ToCvc5Sort α] : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSort α

@[inherit_doc Term.Manager.mkSortBool]
def mkSortBool : SmtT m cvc5.Sort :=
  mkSort Bool

@[inherit_doc Term.Manager.mkSortInt]
def mkSortInt : SmtT m cvc5.Sort :=
  mkSort Int

@[inherit_doc Term.Manager.mkSortReal]
def mkSortReal : SmtT m cvc5.Sort :=
  mkSort Lean.Rat

@[inherit_doc Term.Manager.mkSortRegExp]
def mkSortRegExp : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortRegExp

@[inherit_doc Term.Manager.mkSortString]
def mkSortString : SmtT m cvc5.Sort :=
  mkSort String

@[inherit_doc Term.Manager.mkSortArray]
def mkSortArray (α : Type) [ToCvc5Sort α] : SmtT m cvc5.Sort :=
  mkSort (Array α)

@[inherit_doc Term.Manager.mkSortBitVec]
def mkSortBitVec (size : Nat) : SmtT m cvc5.Sort :=
  mkSort (BitVec size)




/-! ## `Solver` monadic functions -/

@[inherit_doc Solver.getVersion]
def getVersion : SmtT m String :=
  Solver.getVersion (m := m)

@[inherit_doc Solver.setOption]
def setOption (option value : String) : SmtT m Unit :=
  Solver.setOption option value (m := m)

@[inherit_doc Solver.setLogic]
def setLogic (logic : String) : SmtT m Unit :=
  Solver.setLogic logic (m := m)

@[inherit_doc Solver.getOption]
def getOption (option : String) : SmtT m String :=
  Solver.getOption option (m := m)

@[inherit_doc Solver.assertFormula]
def assertFormula (term : Term Bool) : SmtT m Unit :=
  Solver.assertFormula term.toTerm (m := m)

@[inherit_doc Solver.checkSat]
def checkSat
  (onSat : SmtSatT m α := SmtSat.unexpected)
  (onUnsat : SmtUnsatT m α := SmtUnsat.unexpected)
  (onUnknown : SmtUnknownT m α := SmtUnknown.unexpected)
: SmtT m α := do
  match ← cvc5.Smt.checkSat? (m := m) with
  | some true => onSat
  | some false => onUnsat
  | none => onUnknown

@[inherit_doc Solver.getProof]
def getProof : SmtUnsatT m (Array Proof) :=
  Solver.getProof (m := m)

@[inherit_doc Solver.proofToString]
def proofToString (proof : Proof) : SmtUnsatT m String :=
  Solver.proofToString proof (m := m)



@[inherit_doc Solver.declareFun]
def declareFun
  (symbol : String)
  (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
  (fresh : Bool := false)
: SmtT m cvc5.Term :=
  Solver.declareFun symbol in_sorts out_sort fresh (m := m)

@[inherit_doc Solver.declareFreshFun]
def declareFreshFun
  (symbol : String) (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
: SmtT m cvc5.Term :=
  Solver.declareFreshFun symbol in_sorts out_sort (m := m)

def declareConst (symbol : String) (α : Type) [ToCvc5Sort α] : SmtT m (Term α) := do
  let sort ← mkSort α
  declareFun symbol #[] sort

@[inherit_doc Solver.declareSort]
def declareSort
  (symbol : String) (arity: Nat) (fresh : Bool := false)
: SmtT m Sort :=
  Solver.declareSort symbol arity fresh (m := m)

@[inherit_doc Solver.declareFreshSort]
def declareFreshSort (symbol : String) (arity : Nat) : SmtT m Sort :=
  Solver.declareFreshSort symbol arity (m := m)



@[inherit_doc Solver.getAssertions]
def getAssertions : SmtT m (Array (Term Bool)) :=
  (Array.map Term.mk) <$> Solver.getAssertions (m := m)

@[inherit_doc Solver.getUnsatAssumptions]
def getUnsatAssumptions : SmtUnsatT m (Array (Term Bool)) :=
  (Array.map Term.mk) <$> Solver.getUnsatAssumptions (m := m)

@[inherit_doc Solver.getUnsatCore]
def getUnsatCore : SmtT m (Array (Term Bool)) :=
  (Array.map Term.mk) <$> Solver.getUnsatCore (m := m)

@[inherit_doc Solver.getUnsatCoreLemmas]
def getUnsatCoreLemmas : SmtT m (Array (Term Bool)) :=
  (Array.map Term.mk) <$> Solver.getUnsatCoreLemmas (m := m)

@[inherit_doc Solver.getInfo]
def getInfo (flag : String) : SmtT m String :=
  Solver.getInfo flag (m := m)

@[inherit_doc Solver.getOptionNames]
def getOptionNames : SmtT m (Array String) :=
  Solver.getOptionNames (m := m)



@[inherit_doc Solver.getValue]
def getValue (term : (Term α)) : SmtSatT m (Term α) :=
  Solver.getValue term.toTerm (m := m)

@[inherit_doc Solver.getValues]
def getValues (terms : Array (Term α)) : SmtSatT m (Array (Term α)) :=
  terms.mapM getValue



/-- # TODO

Technically unsafe when in a `SmtSat` or `SmtUnsat`.
-/
-- @[inherit_doc Solver.resetAssertions]
def resetAssertions : SmtT m Unit :=
  Solver.resetAssertions (m := m)
