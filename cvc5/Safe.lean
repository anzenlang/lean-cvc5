/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Basic
import cvc5.Extended



/-! # Safe cvc5 API -/
namespace cvc5.Safe



/-! ## Safe terms and term manager -/



/-- Dependent term type. -/
structure Term (_ : Type) : Type where
private ofUnsafe ::
  toUnsafe : cvc5.Term

namespace Term

private instance instCoeTermSafeTerm : Coe cvc5.Term (Term α) :=
  ⟨Term.ofUnsafe⟩

variable (self : Term α)

protected def toString : String :=
  self.toUnsafe.toString

instance : ToString (Term α) :=
  ⟨Term.toString⟩

def ofProof : Proof → Term Bool :=
  ofUnsafe ∘ Proof.getResult



/-! ### Term manager. -/

/-- Safe term manager, wrapper around `cvc5.Term.Manager`. -/
structure Manager : Type where
ofUnsafe ::
  toUnsafe : cvc5.Term.Manager



protected class ToCvc5H (α : Type) (β : outParam Type) extends ToCvc5Sort α where
  toCvc5 : Manager → α → Term β

protected class ToCvc5 (α : Type) extends Term.ToCvc5H α α



namespace Manager

def mk [Monad m] [MonadLiftT BaseIO m] : m Manager := do
  let tm ← cvc5.Term.Manager.mk
  return ofUnsafe tm

variable (self : Manager)

/-- Creates a term from a value of a type that can be converted to cvc5. -/
def mkTerm [Term.ToCvc5H α β] (val : α) : Term β :=
  ToCvc5H.toCvc5 self val

@[inherit_doc cvc5.Term.Manager.mkBoolean]
def mkBool : Bool → Term Bool :=
  Term.ofUnsafe ∘ self.toUnsafe.mkBoolean

instance : Term.ToCvc5 Bool where
  toCvc5 := mkBool

@[inherit_doc cvc5.Term.Manager.mkInteger]
def mkInt : Int → Term Int :=
  Term.ofUnsafe ∘ self.toUnsafe.mkInteger

instance : Term.ToCvc5H Nat Int where
  toCvc5 m := m.mkInt ∘ Int.ofNat

instance : Term.ToCvc5 Int where
  toCvc5 := mkInt

/-- If-then-else constructor. -/
def mkIte (cnd : Term Bool) (thn els : Term α) : Term α :=
  self.toUnsafe.mkIte cnd.toUnsafe thn.toUnsafe els.toUnsafe
  |> Term.ofUnsafe

/-- N-ary equality constructor. -/
def mkEqualN
  (terms : Array (Term α))
  (valid : 1 < terms.size := by simp_arith)
: Term Bool :=
  let unsafeTerms := terms.map Term.toUnsafe
  let valid : 1 < unsafeTerms.size := by simp [unsafeTerms, valid]
  self.toUnsafe.mkEqualN unsafeTerms valid

/-- Binary equality constructor. -/
def mkEqual (lft rgt : Term α) : Term Bool :=
  self.toUnsafe.mkEqual lft.toUnsafe rgt.toUnsafe

/-- Negation constructor. -/
def mkNot (t : Term Bool) : Term Bool :=
  self.toUnsafe.mkNot t.toUnsafe

/-- Implication constructor. -/
def mkImplies (lhs rhs : Term Bool) : Term Bool :=
  self.toUnsafe.mkImplies lhs.toUnsafe rhs.toUnsafe

end Manager

end Term



end Safe



/-! ## `Proof`-related safe functions -/
namespace Proof
/-- Boolean term corresponding to a proof. -/
def getBoolResult : Proof → Safe.Term Bool :=
  Safe.Term.ofProof

@[inherit_doc getBoolResult]
abbrev getBoolTerm := getBoolResult
end Proof



/-! ## Safe SMT state and monad -/
namespace Safe



/-- This type is meant as a parameter for `Smt` and its related monads.

However we need a custom (error-)state monad for that since we need to be able to transition from a
`Smt k` to `Smt k'`. Maybe, I'm not sure it would be very ergonomic.
-/
inductive Smt.Kind
| noLogic
| sat
| unsat
| unknown

/-- A cvc5 context: a `Term.Manager` and a `Solver`. -/
structure Smt where private ofUnsafe ::
  private toUnsafe : cvc5.Smt

/-- Cvc5 context error-state monad transformer. -/
abbrev SmtT m := ExceptT Error (StateT Smt m)

/-- `SmtT` for typed terms.  -/
protected abbrev Smt.Term (m : Type → Type) (α : Type) : Type :=
  SmtT m (Term α)

def SmtT.toUnsafe [Monad m] (code : SmtT m α) : cvc5.SmtT m α :=
  fun smt => do
    let (res, safe) ← code (Smt.ofUnsafe smt)
    return (res, safe.toUnsafe)

private def SmtT.ofUnsafe [Monad m] (code : cvc5.SmtT m α) : SmtT m α :=
  fun safe => do
    let (res, smt) ← code safe.toUnsafe
    return (res, Smt.ofUnsafe smt)

private def _root_.cvc5.SmtT.toSafe := @Safe.SmtT.ofUnsafe

instance [Monad m] : MonadExceptOf Error (SmtT m) where
  throw e smt := return (.error e, smt)
  tryCatch code errorDo smt := do
    match ← code smt with
    | (.ok res, smt) => return (.ok res, smt)
    | (.error err, smt) => errorDo err smt

/-- Cvc5 context errot-state IO monad. -/
abbrev SmtM := SmtT IO



/-- Safe version of `Smt`, only provides safe term/solver functions. -/
def _root_.cvc5.Smt.toSafe (smt : cvc5.Smt) : Safe.Smt :=
  ⟨smt⟩



namespace Smt



/-- Safe solver, *sat* mode. -/
structure Sat where
private ofSmt ::
  private toSmt : Smt

/-- Sat error-state monad transformer. -/
abbrev SatT m := ExceptT Error (StateT Sat m)

def Sat.unexpected [Monad m] : SatT m α := do
  throw (.userError "unexpected check-sat result: *sat*")



/-- Safe solver, *unsat* mode. -/
structure Unsat where
private ofSmt ::
  private toSmt : Smt

/-- Unsat error-state monad transformer. -/
abbrev UnsatT m := ExceptT Error (StateT Unsat m)

def Unsat.unexpected [Monad m] : UnsatT m α := do
  throw (.userError "unexpected check-sat result: *unsat*")



/-- Safe solver, *unknown* mode. -/
structure Unknown where
private ofSmt ::
  private toSmt : Smt

/-- Unknown error-state monad transformer. -/
abbrev UnknownT m := ExceptT Error (StateT Unknown m)

def Unknown.unexpected [Monad m] : UnknownT m α := do
  throw (.userError "unexpected check-sat result: *unknown*")



variable [Monad m]

/-- Constructor from a term manager. -/
def ofTermManager (tm : Term.Manager) (logic : Logic) : ExceptT Error m Smt := do
  let smt := cvc5.Smt.ofTermManager tm.toUnsafe
  let _ ← smt.setLogic' logic
  return ofUnsafe smt

/-- Constructor. -/
def mk [MonadLiftT BaseIO m] (logic : Logic) : ExceptT Error m Smt := do
  Term.Manager.mk >>= (ofTermManager · logic)



@[inherit_doc cvc5.Smt.runWith]
def runWith
  (tm : Term.Manager) (logic : Logic) (query : SmtT m α)
: ExceptT Error m α := do
  let smt ← ofTermManager tm logic
  let (res, _) ← query smt
  res

@[inherit_doc cvc5.Smt.runWithOr]
def runWithOr
  (tm : Term.Manager)
  (logic : Logic)
  (query : SmtT m α)
  (handleError : Error → m α)
: m α := do
  match ← runWith tm logic query with
  | .ok res => return res
  | .error e => handleError e

@[inherit_doc cvc5.Smt.runWith!]
def runWith! [Inhabited α]
  (tm : Term.Manager)
  (logic : Logic)
  (query : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"[cvc5.Safe.Smt] {e}")
: m α := do
  runWithOr tm logic query handleError

@[inherit_doc cvc5.Smt.run]
def run [MonadLiftT BaseIO m]
  (logic : Logic)
  (query : SmtT m α)
: m (Except Error α) := do
  let tm ← Term.Manager.mk
  runWith tm logic query


@[inherit_doc cvc5.Smt.runOr]
def runOr [MonadLiftT BaseIO m]
  (logic : Logic)
  (query : SmtT m α)
  (handleError : Error → m α)
: m α := do
  let tm ← Term.Manager.mk
  runWithOr tm logic query handleError

@[inherit_doc cvc5.Smt.runOr]
def run! [MonadLiftT BaseIO m] [Inhabited α]
  (logic : Logic)
  (query : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"[cvc5.Safe.Smt] {e}")
: m α := do
  let tm ← Term.Manager.mk
  runWithOr tm logic query handleError



/-! ### Terms -/

protected def termManagerDo [Monad m] (f : Term.Manager → α) : SmtT m α :=
  fun smt => do
    let (res, uns) ← smt.toUnsafe.termManagerDo (f ∘ Term.Manager.ofUnsafe)
    return (res, ofUnsafe uns)

@[inherit_doc Term.Manager.mkTerm]
def mkTerm [Term.ToCvc5H α β] (val : α) : SmtT m (Term β) :=
  Smt.termManagerDo fun tm => tm.mkTerm val

@[inherit_doc Term.Manager.mkIte]
def mkIte (cnd : Term Bool) (thn els : Term α) : SmtT m (Term α) :=
  Smt.termManagerDo fun tm => tm.mkIte cnd thn els

@[inherit_doc Term.Manager.mkEqualN]
def mkEqualN
  (terms : Array (Term α))
  (valid : 1 < terms.size := by simp_arith)
: SmtT m (Term Bool) :=
  Smt.termManagerDo fun tm => tm.mkEqualN terms valid

@[inherit_doc Term.Manager.mkEqual]
def mkEqual (lhs rhs : Term α) : SmtT m (Term Bool) :=
  Smt.termManagerDo fun tm => tm.mkEqual lhs rhs

@[inherit_doc Term.Manager.mkNot]
def mkNot (term : Term Bool) : SmtT m (Term Bool) :=
  Smt.termManagerDo fun tm => tm.mkNot term

@[inherit_doc Term.Manager.mkImplies]
def mkImplies (lhs rhs : Term Bool) : SmtT m (Term Bool) :=
  Smt.termManagerDo fun tm => tm.mkImplies lhs rhs





/-! ### Solver information and options -/

@[inherit_doc cvc5.Smt.getVersion]
def getVersion : SmtT m String :=
  cvc5.Smt.getVersion.toSafe

@[inherit_doc cvc5.Smt.setOption]
def setOption (key val : String) : SmtT m Unit :=
  cvc5.Smt.setOption key val |>.toSafe

@[inherit_doc cvc5.Smt.getOption]
def getOption (key : String) : SmtT m String :=
  cvc5.Smt.getOption key |>.toSafe

@[inherit_doc cvc5.Smt.getOptionNames]
def getOptionNames : SmtT m (Array String) :=
  cvc5.Smt.getOptionNames |>.toSafe

@[inherit_doc cvc5.Smt.getInfo]
def getInfo (flag : String) : SmtT m String :=
  cvc5.Smt.getInfo flag |>.toSafe

@[inherit_doc cvc5.Smt.getAssertions]
def getAssertions : SmtT m (Array (Term Bool)) := do
  let assertions ← cvc5.Smt.getAssertions.toSafe
  return assertions.map Term.ofUnsafe



/-! ### Declare / define symbols -/

def declareConst (symbol : String) (α : Type) [ToCvc5Sort α] : SmtT m (Term α) :=
  cvc5.Smt.declareConst symbol α |>.toSafe



/-! ### Reset / incrementality -/

@[inherit_doc cvc5.Smt.resetAssertions]
def resetAssertions : SmtT m Unit :=
  cvc5.Smt.resetAssertions.toSafe



/-! ### Assert-like -/

def assertFormula (term : Term Bool) : SmtT m Unit :=
  cvc5.Smt.assertFormula term.toUnsafe |>.toSafe



/-! ### Checksat-like functions -/

section checkSat_proper

private scoped instance : MonadLift (SatT m) (SmtT m) where
  monadLift satT smt := do
    let (res, solverSat) ← satT (Sat.ofSmt smt)
    return (res, solverSat.toSmt)

private scoped instance : MonadLift (UnsatT m) (SmtT m) where
  monadLift unsatT solver := do
    let (res, solverUnsat) ← unsatT (Unsat.ofSmt solver)
    return (res, solverUnsat.toSmt)

private scoped instance : MonadLift (UnknownT m) (SmtT m) where
  monadLift unknownT solver := do
    let (res, solverUnknown) ← unknownT (Unknown.ofSmt solver)
    return (res, solverUnknown.toSmt)

def checkSat
  (onSat : SatT m α := Sat.unexpected)
  (onUnsat : UnsatT m α := Unsat.unexpected)
  (onUnknown : UnknownT m α := Unknown.unexpected)
: SmtT m α := do
  match ← cvc5.Smt.checkSat?.toSafe with
  | some true => onSat
  | some false => onUnsat
  | none => onUnknown

end checkSat_proper



/-! ### Sat-specific queries -/
section sat_queries

private scoped instance : MonadLift (cvc5.SmtT m) (SatT m) where
  monadLift smtT smtSat := do
    let (res, smt) ← smtT smtSat.toSmt.toUnsafe
    return (res, Sat.ofSmt smt.toSafe)

@[inherit_doc cvc5.Smt.getValue]
def getValue (term : Term α) : SatT m (Term α) :=
  cvc5.Smt.getValue (m := m) term.toUnsafe

@[inherit_doc cvc5.Smt.getValues]
def getValues (terms : Array (Term α)) : SatT m (Array (Term α)) :=
  Array.mkEmpty terms.size
  |> terms.foldlM fun array term =>
    return array.push (← getValue term)

end sat_queries



/-! ### Unsat-specific queries -/
section unsat_queries

private scoped instance : MonadLift (cvc5.SmtT m) (UnsatT m) where
  monadLift smtT smtUnsat := do
    let (res, smt) ← smtT smtUnsat.toSmt.toUnsafe
    return (res, Unsat.ofSmt smt.toSafe)

@[inherit_doc cvc5.Smt.getProof]
def getProof : UnsatT m (Array Proof) :=
  cvc5.Smt.getProof (m := m)

@[inherit_doc cvc5.Smt.proofToString]
def proofToString (p : Proof) : UnsatT m String :=
  cvc5.Smt.proofToString (m := m) p

@[inherit_doc cvc5.Smt.getUnsatAssumptions]
def getUnsatAssumptions : UnsatT m (Array (Term Bool)) := do
  let assumptions ← cvc5.Smt.getUnsatAssumptions (m := m)
  return assumptions.map Term.ofUnsafe

@[inherit_doc cvc5.Smt.getUnsatCore]
def getUnsatCore : UnsatT m (Array (Term Bool)) := do
  let assumptions ← cvc5.Smt.getUnsatCore (m := m)
  return assumptions.map Term.ofUnsafe

@[inherit_doc cvc5.Smt.getUnsatCore]
def getUnsatCoreLemmas : UnsatT m (Array (Term Bool)) := do
  let assumptions ← cvc5.Smt.getUnsatCoreLemmas (m := m)
  return assumptions.map Term.ofUnsafe

end unsat_queries



/-! ### Unknown-specific queries -/
section unknown_queries

private scoped instance : MonadLift (cvc5.SmtT m) (UnknownT m) where
  monadLift smtT smtUnknown := do
    let (res, smt) ← smtT smtUnknown.toSmt.toUnsafe
    return (res, Unknown.ofSmt smt.toSafe)

end unknown_queries
