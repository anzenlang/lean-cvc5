/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Elab.Command
import Lean.Expr
import Lean.Data.Rat

import cvc5.Kind
import cvc5.ProofRule
import cvc5.SkolemId

namespace cvc5

private opaque ResultImpl : NonemptyType.{0}

/-- Encapsulation of a three-valued solver result, with explanations. -/
def Result : Type := ResultImpl.type

instance Result.instNonemptyResult : Nonempty Result := ResultImpl.property

private opaque SortImpl : NonemptyType.{0}

end cvc5

/-- The sort of a cvc5 term. -/
def cvc5.Sort : Type := cvc5.SortImpl.type

namespace cvc5

instance Sort.instNonemptySort : Nonempty cvc5.Sort := SortImpl.property

private opaque OpImpl : NonemptyType.{0}

/-- A cvc5 operator.

An operator is a term that represents certain operators, instantiated with its required parameters,
*e.g.*, a `Term` of kind `Kind.BITVECTOR_EXTRACT`.
-/
def Op : Type := OpImpl.type

instance Op.instNonemptyOp : Nonempty Op := OpImpl.property

private opaque TermImpl : NonemptyType.{0}

/-- A cvc5 term. -/
def Term : Type := TermImpl.type

instance Term.instNonemptyTerm : Nonempty Term := TermImpl.property

private opaque ProofImpl : NonemptyType.{0}

/-- A cvc5 proof.

Proofs are trees and every proof object corresponds to the root step of a proof. The branches of the
root step are the premises of the step.
-/
def Proof : Type := ProofImpl.type

instance Proof.instNonemptyProof : Nonempty Proof := ProofImpl.property

private opaque GrammarImpl : NonemptyType.{0}

/-- A Sygus grammar.

This type can be used to define a context-free grammar of terms. Its interface coincides with the definition of grammars (`GrammarDef`) in the *SyGuS IF 2.1 standard*.
-/
def Grammar : Type := GrammarImpl.type

namespace Grammar
instance instNonEmpty : Nonempty Grammar := GrammarImpl.property

/-- Determine if this is the null grammar. -/
@[extern "grammar_isNull"]
opaque isNull : Grammar → Bool

/-- Add `rule` to the set of rules corresponding to `ntSymbol`.

- `ntSymbol`: The non-terminal to which the rule is added.
- `rule`: The rule to add.
-/
@[extern "grammar_addRule"]
opaque addRule : Grammar → (ntSymbol : Term) → (rule : Term) → Grammar

/-- Add `rules` to the set of rules corresponding to `ntSymbol`.

- `ntSymbol`: The non-terminal to which the rules are added.
- `rules`: The rules to add.
-/
def addRules (g : Grammar) (ntSymbol : Term) (rules : Array Term) : Grammar := Id.run do
  let mut g := g
  for rule in rules do
    g := g.addRule ntSymbol rule
  return g

/-- A string representation of this grammar. -/
@[extern "grammar_toString"]
protected opaque toString : Grammar → String

instance instToString : ToString Grammar := ⟨Grammar.toString⟩

end Grammar

private opaque SynthResultImpl : NonemptyType.{0}

/-- Encapsulation of a solver synth result.

This is the return value of the API functions `checkSynth` and `checkSynthNext` which we call
*"synthesis queries"*. This type indicates whether th esynthesis query has a solution, has no
solution, or is unknown.
-/
def SynthResult : Type := SynthResultImpl.type

namespace SynthResult
instance instNonEmpty : Nonempty SynthResult := SynthResultImpl.property

@[extern "synthResult_isNull"]
opaque isNull : SynthResult → Bool

@[extern "synthResult_hasSolution"]
opaque hasSolution : SynthResult → Bool

@[extern "synthResult_hasNoSolution"]
opaque hasNoSolution : SynthResult → Bool

@[extern "synthResult_isUnknown"]
opaque isUnknown : SynthResult → Bool

@[extern "synthResult_toString"]
protected opaque toString : SynthResult → String

instance instToString : ToString SynthResult := ⟨SynthResult.toString⟩

end SynthResult

private opaque FindSynthTargetImpl : NonemptyType.{0}

/-- Encapsulation of a solver synth result.

This is the return value of the API functions `checkSynth` and `checkSynthNext` which we call
*"synthesis queries"*. This type indicates whether th esynthesis query has a solution, has no
solution, or is unknown.

# TODO

There is currently no way to construct this type. It is an enumeration that we have to redefine at
lean-level.
-/
def FindSynthTarget : Type := FindSynthTargetImpl.type

namespace FindSynthTarget
instance instNonEmpty : Nonempty FindSynthTarget := FindSynthTargetImpl.property

@[extern "synthResult_isNull"]
opaque isNull : FindSynthTarget → Bool

end FindSynthTarget

private opaque TermManagerImpl : NonemptyType.{0}

/-- Manager for cvc5 terms. -/
def TermManager : Type := TermManagerImpl.type

instance TermManager.instNonemptyTermManager : Nonempty TermManager := TermManagerImpl.property

/-- Error type. -/
inductive Error where
  | missingValue
  | error (msg : String)
  | recoverable (msg : String)
  | unsupported (msg : String)
  | option (msg : String)
deriving Repr

/-- Only used by FFI to inject values. -/
@[export except_ok]
private def mkExceptOk {α : Type} : α → Except Error α :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_bool]
private def mkExceptOkBool : Bool → Except Error Bool :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u32]
private def mkExceptOkU32 : UInt32 → Except Error UInt32 :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u8]
private def mkExceptOkU8 : UInt8 → Except Error UInt8 :=
  .ok

/-- Only used by FFI to inject errors. -/
@[export except_err]
private def mkExceptErr {α : Type} : String → Except Error α :=
  .error ∘ Error.error

private opaque SolverImpl : NonemptyType.{0}

/-- A cvc5 solver. -/
def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

/-- Solver error/state-monad transformer. -/
abbrev SolverT m := ExceptT Error (StateT Solver m)

/-- Solver error/state-monad wrapped in `IO`. -/
abbrev SolverM := SolverT IO

namespace Error

/-- Panics on errors, otherwise yields the `ok` result. -/
def unwrap! [Inhabited α] : Except Error α → α
| .ok a => a
| .error (.error e) => panic! s!"error: {e}"
| .error (.recoverable e) => panic! s!"recoverable error: {e}"
| .error (.unsupported e) => panic! s!"unsupported: {e}"
| .error (.option e) => panic! s!"option error: {e}"
| .error .missingValue => panic! s!"missing value"

/-- String representation of an error. -/
protected def toString : Error → String :=
  toString ∘ repr

instance : ToString Error :=
  ⟨Error.toString⟩

end Error

namespace Result

/-- True if this result is from a satisfiable `checkSat` or `checkSatAssuming` query. -/
@[extern "result_isSat"]
opaque isSat : Result → Bool

/-- True if this result is from a unsatisfiable `checkSat` or `checkSatAssuming` query. -/
@[extern "result_isUnsat"]
opaque isUnsat : Result → Bool

/-- True if this result is from a `checkSat` or `checkSatAssuming` query and cvc5 was not able to
determine (un)satisfiability.
-/
@[extern "result_isUnknown"]
opaque isUnknown : Result → Bool

/-- A string representation of this result. -/
@[extern "result_toString"]
protected opaque toString : Result → String

instance : ToString Result := ⟨Result.toString⟩

end cvc5.Result

namespace cvc5.Sort

@[extern "sort_null"]
opaque null : Unit → cvc5.Sort

instance : Inhabited cvc5.Sort := ⟨null ()⟩

/-- Get the kind of this sort. -/
@[extern "sort_getKind"]
opaque getKind : cvc5.Sort → SortKind

/-- Comparison for structural equality. -/
@[extern "sort_beq"]
protected opaque beq : cvc5.Sort → cvc5.Sort → Bool

instance : BEq cvc5.Sort := ⟨Sort.beq⟩

/-- Hash function for cvc5 sorts. -/
@[extern "sort_hash"]
protected opaque hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

/-- Determine if this is a function sort. -/
@[extern "sort_isFunction"]
protected opaque isFunction : cvc5.Sort → Bool

/-- The domain sorts of a function sort. -/
@[extern "sort_getFunctionDomainSorts"]
opaque getFunctionDomainSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The codomain sort of a function sort. -/
@[extern "sort_getFunctionCodomainSort"]
opaque getFunctionCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- Get the symbol of this sort.

The symbol of this sort is the string that was provided when consrtucting it *via* one of
`Solver.mkUninterpretedSort`, `Solver.mkUnresolvedSort`, or
`Solver.mkUninterpretedSortConstructorSort`.
-/
@[extern "sort_getSymbol"]
opaque getSymbol : cvc5.Sort → Except Error String

/-- Determine if this is the integer sort (SMT-LIB: `Int`). -/
@[extern "sort_isInteger"]
opaque isInteger : cvc5.Sort → Bool

/-- The bit-width of the bit-vector sort. -/
@[extern "sort_getBitVectorSize"]
opaque getBitVectorSize : cvc5.Sort → Except Error UInt32

/-- A string representation of this sort. -/
@[extern "sort_toString"]
protected opaque toString : cvc5.Sort → String

instance : ToString cvc5.Sort := ⟨Sort.toString⟩
instance : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

end cvc5.Sort

namespace cvc5.Op

@[extern "op_null"]
opaque null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

/-- Syntactic equality operator. -/
@[extern "op_beq"]
protected opaque beq : Op → Op → Bool

instance : BEq Op := ⟨Op.beq⟩

/-- Get the kind of this operator. -/
@[extern "op_getKind"]
opaque getKind : Op → Kind

/-- Determine if this operator is nullary. -/
@[extern "op_isNull"]
opaque isNull : Op → Bool

/-- Determine if this operator is indexed. -/
@[extern "op_isIndexed"]
opaque isIndexed : Op → Bool

/-- Get the number of indices of this operator. -/
@[extern "op_getNumIndices"]
opaque getNumIndices : Op → Nat

/-- Get the index at position `i` of an indexed operator. -/
@[extern "op_get"]
protected opaque get : (op : Op) → (i : Fin op.getNumIndices) → Term

instance : GetElem Op Nat Term fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩

/-- Get the string representation of this operator. -/
@[extern "op_toString"]
protected opaque toString : Op → String

instance : ToString Op := ⟨Op.toString⟩

end Op

/-! ## DSL for definition DRY -/

declare_syntax_cat defsItem

scoped syntax (name := defsItemStx)
  declModifiers
  "def " ident ("(" "force" " := " str ")")? " : " term
  withPosition(ppLine "with "
    group(
      colGt
      docComment ?
      ident
    )*
  )?
  withPosition(ppLine "where "
    group(
      colGt
      docComment ?
      declId optDeclSig ":= " withPosition(group(colGe term))
    )*
  )?
: defsItem

def elabDefsItem (pref : String) : Lean.Elab.Command.CommandElab
| `(defsItem|
    $mods:declModifiers
    def $ident:ident $[(force := $forced:str)]? : $typ:term
    $[ with $[
        $[$autoDoc]?
        $autoId
    ]* ]?
    $[ where $[
        $[$subDoc]?
        $subId $subSig := $subDef
    ]* ]?
) => do
  let externName :=
    let id :=
      if let some forced := forced then
        forced.getString
      else
        ident.getId.toString
    pref ++ "_" ++ id |> Lean.Syntax.mkStrLit
  let mods ←
    match mods with
    | `(Lean.Parser.Command.declModifiersT|
      $[$doc:docComment]? $[@[ $[ $attrs ],* ]]? $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
    ) => do
      let ext ← `(Lean.Parser.Term.attrInstance| extern $externName:str)
      let attrs := attrs.getD #[] |>.push ext
      `(Lean.Parser.Command.declModifiersT|
        $[$doc:docComment]? @[ $[$attrs],* ] $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
      )
    | _ => Lean.Elab.throwUnsupportedSyntax
  let mainDef ←`(
    $(⟨mods⟩):declModifiers
    opaque $ident:declId : $typ:term
  )
  Lean.Elab.Command.elabCommand mainDef

  let define doc? id sig? (body : Lean.Syntax.Term) : Lean.Elab.Command.CommandElabM _ := do
    if let some doc := doc? then
      `(command|
        $doc:docComment
        def $id:declId $sig?:optDeclSig := $body
      )
    else
      `(command|
        @[inherit_doc $ident]
        def $id:declId $sig?:optDeclSig := $body
      )

  if let (some autoDoc?, some autoId) := (autoDoc, autoId) then
    for (autoDoc?, autoId) in autoDoc?.zip autoId do
      let id : String := autoId.getId.toString
      let body ←
        if id.endsWith "!" then
          `(cvc5.Error.unwrap! ∘ $ident)
        else if id.endsWith "?" then
          `(Except.toOption ∘ $ident)
        else
          Lean.throwError s!"unexpected auto function name `{id}`"
      Lean.Elab.Command.elabCommand
        (← define autoDoc? autoId (← `(optDeclSig|)) body)

  if let
    (some subDoc?, some subId, some subSig, some subDef)
    := (subDoc, subId, subSig, subDef)
  then
    let all := subDoc?.zip subId |>.zip subSig |>.zip subDef
    for (((subDoc?, subId), subSig), subDef) in all do
      Lean.Elab.Command.elabCommand
        (← define subDoc? subId subSig subDef)
| _ => Lean.Elab.throwUnsupportedSyntax

/-- Defines similar functions realized by `extern`.

```
defs "prefix"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.

  Will create an opaque definition with `[@extern extStr]` where
  `extStr = "prefix" ++ _ ++ "myFunction"`.
  -/
  def myFunction : Term → Except Error Op
  with
    endsWithBang!
    endWithQuestion?
  where
    myOtherFunction : Term → Op :=
      Error.unwrap! ∘ myFunction
    /-- Optional function docstring: if none, inherit from the main function. -/
    yetAnotherFunction : Term → Option Op :=
      Except.toOption ∘ myFunction
```

- `with ...`: takes a sequence of identifiers, each generate a function that
  - unwraps the result if `!`-ended;
  - turns a result into an option if `?`-ended;
  - fails otherwise.

- supports `declModifiers` on the main (`def`) function `myFunction` such as `private`...
- accepts a list of main (`def`) functions, each with `with` and/or `where` clauses.
-/
scoped syntax (name := multidefs)
  withPosition("defs! " str ppLine group(colGt defsItem)+)
: command

@[inherit_doc multidefs, command_elab multidefs]
def multidefsImpl : Lean.Elab.Command.CommandElab
| `(command|
  defs! $pref:str $[$defsItems]*
) => do
  let pref := pref.getString
  for defsItem in defsItems do
    elabDefsItem pref defsItem
| _ => Lean.Elab.throwUnsupportedSyntax

namespace Term

@[extern "term_null"]
opaque null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

/-- Determine if this term is nullary. -/
@[extern "term_isNull"]
opaque isNull : Term → Bool

/-- Get the kind of this term. -/
@[extern "term_getKind"]
opaque getKind : Term → Kind

/-- Determine if this term has an operator. -/
@[extern "term_hasOp"]
opaque hasOp : Term → Bool

defs! "term"
  /-- Get the operator of a term with an operator.

  Requires that this term has an operator (see `hasOp`).
  -/
  def getOp : Term → Except Error Op
  with getOp! getOp?

  /-- Get the sort of this term. -/
  def getSort : Term → cvc5.Sort

  /-- Unsafe version of `substitute`. -/
  private def substituteUnsafe (force := "substitute")
  : Term → Array Term → Array Term → Except Error Term
  where
    /-- Simultaneously replaces terms in `term`.

    - `substs`: list of `(subTerm, replacement)` pairs instructing to replace `subTerm` by
      `replacement`.

    This replacement is applied during a pre-order traversal and only once (it is not run until
    fixed point).
    -/
    substitute (term : Term) (substs : Array (Term × Term)) : Except Error Term :=
      let (terms, replacements) :=
        (Array.mkEmpty substs.size, Array.mkEmpty substs.size)
        |> substs.foldl fun (ts, rs) (t, r) => (ts.push t, rs.push r)
      substituteUnsafe term terms replacements

/-- Syntactic equality operator. -/
@[extern "term_beq"]
protected opaque beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

/-- Hash function for terms. -/
@[extern "term_hash"]
protected opaque hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

defs! "term"
  /-- Get the value of a Boolean term as a native Boolean value.

  Requires `term` to have sort Bool.
  -/
  def getBooleanValue : (term : Term) → Except Error Bool
  with getBooleanValue! getBooleanValue?

  /-- Get the string representation of a bit-vector value.

  Requires `term` to have a bit-vector sort.

  - `base`: `2` for binary, `10` for decimal, and `16` for hexadecimal.
  -/
  def getBitVectorValue : (term : Term) → Except Error String
  with getBitVectorValue? getBitVectorValue!

  /-- Get the native integral value of an integral value. -/
  def getIntegerValue : Term → (base : UInt32 := 2) → Except Error Int
  with getIntegerValue? getIntegerValue!

  /-- Get the native rational value of a real, rational-compatible value. -/
  def getRationalValue : Term → (base : UInt32 := 2) → Except Error Lean.Rat
  with getRationalValue? getRationalValue!

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
@[extern "term_hasSymbol"]
opaque hasSymbol : Term → Bool

defs! "term"
  /-- Get the symbol of this term.

  Requires that this term has a symbol (see `hasSymbol`).

  The symbol of the term is the string that was provided when constructing it *via*
  `TermManager.mkConst` or `TermManager.mkVar`.
  -/
  def getSymbol : Term → Except Error String
  with getSymbol? getSymbol!

/-- Get the id of this term. -/
@[extern "term_getId"]
opaque getId : Term → Nat

/-- Get the number of children of this term. -/
@[extern "term_getNumChildren"]
opaque getNumChildren : Term → Nat

/-- Is this term a skolem? -/
@[extern "term_isSkolem"]
opaque isSkolem : Term → Bool

defs! "term"
  /-- Get skolem identifier of this term.

  Requires `isSkolem`.
  -/
  def getSkolemId : Term → Except Error SkolemId
  with getSkolemId? getSkolemId!

  /-- Get the skolem indices of this term.

  Requires `isSkolem`.

  Returns the skolem indices of this term. This is a list of terms that the skolem function is
  indexed by. For example, the array diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two arrays.
  -/
  def getSkolemIndices : Term → Except Error (Array Term)
  with getSkolemIndices? getSkolemIndices!

/-- Get the child term of this term at a given index. -/
@[extern "term_get"]
protected opaque get : (t : Term) → Fin t.getNumChildren → Term

instance : GetElem Term Nat Term fun t i => i < t.getNumChildren where
  getElem t i h := t.get ⟨i, h⟩

/-- Monadic for-loop as required by `ForIn`. -/
protected def forIn {β : Type u} [Monad m] (t : Term) (b : β) (f : Term → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ t.getNumChildren) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < t.getNumChildren := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : t.getNumChildren - 1 < t.getNumChildren := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : t.getNumChildren - 1 - i < t.getNumChildren := Nat.lt_of_le_of_lt (Nat.sub_le (t.getNumChildren - 1) i) this
      match (← f t[t.getNumChildren - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop t.getNumChildren (Nat.le_refl _) b

instance : ForIn m Term Term where
  forIn := Term.forIn

/-- Get the children of a term. -/
def getChildren (t : Term) : Array Term := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

/-- Boolean negation. -/
@[extern "term_not"]
protected opaque not : Term → Term

/-- Boolean and. -/
@[extern "term_and"]
protected opaque and : Term → Term → Term

/-- Boolean or. -/
@[extern "term_or"]
protected opaque or : Term → Term → Term

/-- A string representation of this term. -/
@[extern "term_toString"]
protected opaque toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term

namespace Proof

@[extern "proof_null"]
opaque null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

/-- The proof rule used by the root step of the proof. -/
@[extern "proof_getRule"]
opaque getRule : Proof → ProofRule

/-- The proof rewrite rule used by the root step of the proof. -/
@[extern "proof_getRewriteRule"]
opaque getRewriteRule : Proof → ProofRewriteRule

/-- The conclusion of the root step of the proof. -/
@[extern "proof_getResult"]
opaque getResult : Proof → Term

/-- The premises of the root step of the proof. -/
@[extern "proof_getChildren"]
opaque getChildren : Proof → Array Proof

/-- The arguments of the root step of the proof as a vector of terms.

Some of those terms might be strings.
-/
@[extern "proof_getArguments"]
opaque getArguments : Proof → Array Term

/-- Operator overloading for referential equality of two proofs. -/
@[extern "proof_beq"]
protected opaque beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

/-- Hash function for proofs. -/
@[extern "proof_hash"]
protected opaque hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩

end Proof

namespace TermManager

defs! "termManager"

  /-- Constructor. -/
  def new : BaseIO TermManager

  /-- Get the Boolean sort. -/
  def getBooleanSort : TermManager → cvc5.Sort

  /-- Get the Integer sort. -/
  def getIntegerSort : TermManager → cvc5.Sort

  /-- Get the Real sort. -/
  def getRealSort : TermManager → cvc5.Sort

  /-- Get the regular expression sort. -/
  def getRegExpSort : TermManager → cvc5.Sort

  /-- Get the rounding mode sort. -/
  def getRoundingModeSort : TermManager → cvc5.Sort

  /-- Get the string sort. -/
  def getStringSort : TermManager → cvc5.Sort

  /-- Create an array sort.

  - `indexSort`: The array index sort.
  - `elemSort`: The array element sort.
  -/
  def mkArraySort
  : TermManager → (indexSort elemSort : cvc5.Sort) → Except Error cvc5.Sort
  where
    mkArraySort! (tm idx elm) :=
      mkArraySort tm idx elm |> Error.unwrap!
  /-- Create a bit-vector sort.

  - `size`: The bit-width of the bit-vector sort, cannot be zero.
  -/
  def mkBitVectorSortUnsafe (force := "mkBitVectorSort")
  : TermManager → (size : UInt32) → Except Error cvc5.Sort
  where
    mkBitVectorSort
      (tm : TermManager) (size : UInt32)
      (valid : 0 < size := by
        first
        | decide
        | fail "failed to prove the bit-vector's size is `> 0`")
    : cvc5.Sort :=
      let _ := valid
      mkBitVectorSortUnsafe tm size |> Error.unwrap!

  /-- Create a floating-point sort.

  - `exp`: The bit-width of the exponent of the floating-point sort.
  - `sig`: The bit-width of the significand of the floating-point sort.
  -/
  def mkFloatingPointSortUnsafe (force := "mkFloatingPointSort")
  : TermManager → (exp sig : UInt32) → Except Error cvc5.Sort
  where
    mkFloatingPointSort! (tm : TermManager) (exp sig : UInt32) : cvc5.Sort :=
      Error.unwrap! (tm.mkFloatingPointSortUnsafe exp sig)
    mkFloatingPointSort (tm : TermManager) (exp sig : UInt32)
      (valid_exp : 1 < exp := by
        first | decide | fail "failed to prove the exponent is `> 1`")
      (valid_sig : 1 < sig := by
        first | decide | fail "failed to prove the significand is `> 1`")
    : Except Error cvc5.Sort :=
      let _ := valid_exp
      let _ := valid_sig
      mkFloatingPointSortUnsafe tm exp sig

  /-- Create a finite-field sort from a given string of base n.

  - `size`: The modulus of the field. Must be prime.
  - `base`: The base of the string representation of `size`.
  -/
  def mkFiniteFieldSortOfString (force := "mkFiniteFieldSort")
  : TermManager → (size : String) → (base : UInt32 := 10) → Except Error cvc5.Sort
  where
    mkFiniteFieldSortOfString! tm size (base : UInt32 := 10) :=
      mkFiniteFieldSortOfString tm size base
      |> Error.unwrap!
    /-- Create a finite-field sort from a given string of base n.

    - `size`: The modulus of the field. Must be prime.
    - `base`: The base of `size`.
    -/
    mkFiniteFieldSort
      (tm : TermManager) (size : Nat) (base : UInt32 := 10)
    : Except Error cvc5.Sort :=
      tm.mkFiniteFieldSortOfString (toString size) base

    mkFiniteFieldSort! tm size base :=
      mkFiniteFieldSort tm size base
      |> Error.unwrap!

  /-- Create function sort.

  - `sorts`: The sort of the function arguments.
  - `codomain`: The sort of the function return value.
  -/
  def mkFunctionSort
  : TermManager → (sorts : Array cvc5.Sort) → (codomain : cvc5.Sort) → Except Error cvc5.Sort
  where
    mkFunctionSort! tm sorts codomain :=
      mkFunctionSort tm sorts codomain
      |> Error.unwrap!

  /-- Create a predicate sort.

  This is equivalent to calling `mkFunctionSort` with the Boolean sort as the codomain.

  - `sorts`: The list of sorts of the predicate.
  -/
  def mkPredicateSort : TermManager → (sorts : Array cvc5.Sort) → Except Error cvc5.Sort

  /-- Create an uninterpreted sort.

  - `symbol`: The name of the sort.
  -/
  def mkUninterpretedSort : TermManager → (symbol : String) → Except Error cvc5.Sort

  /-- Create a sort parameter.

  - `symbol`: The name of the sort.
  -/
  def mkParamSort : TermManager → (symbol : String) → Except Error cvc5.Sort

  /-- Create a Boolean constant.

  - `b`: The Boolean constant.
  -/
  def mkBoolean : TermManager → (b : Bool) → Term

  /-- Create an integer constant from a string.

  - `s`: The string representation of the constant, may represent an integer such as `"123"`.
  -/
  private def mkIntegerFromString : TermManager → (s : String) → Except Error Term
  where
    /-- Create an integer constant.

    - `i`: The integer constant.
    -/
    mkInteger (tm : TermManager) : (i : Int) → Except Error Term :=
      mkIntegerFromString tm ∘ toString

    mkInteger! tm i :=
      mkInteger tm i
      |> Error.unwrap!

  /-- Create operator of Kind:

  - `Kind.BITVECTOR_EXTRACT`
  - `Kind.BITVECTOR_REPEAT`
  - `Kind.BITVECTOR_ROTATE_LEFT`
  - `Kind.BITVECTOR_ROTATE_RIGHT`
  - `Kind.BITVECTOR_SIGN_EXTEND`
  - `Kind.BITVECTOR_ZERO_EXTEND`
  - `Kind.DIVISIBLE`
  - `Kind.FLOATINGPOINT_TO_FP_FROM_FP`
  - `Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV`
  - `Kind.FLOATINGPOINT_TO_FP_FROM_REAL`
  - `Kind.FLOATINGPOINT_TO_FP_FROM_SBV`
  - `Kind.FLOATINGPOINT_TO_FP_FROM_UBV`
  - `Kind.FLOATINGPOINT_TO_SBV`
  - `Kind.FLOATINGPOINT_TO_UBV`
  - `Kind.INT_TO_BITVECTOR`
  - `Kind.TUPLE_PROJECT`

  See `cvc5.Kind` for a description of the parameters.

  - `kind`: The kind of the operator.
  - `args`: The arguments (indices) of the operator.

  If `args` is empty, the `Op` simply wraps the `cvc5.Kind`. The `Kind` can be used in `Solver.mkTerm`
  directly without creating an `Op` first.
  -/
  def mkOpOfIndices : TermManager → (kind : Kind) → (args : Array Nat) → Except Error Op
  where
    mkOpOfIndices! tm kind args :=
      mkOpOfIndices tm kind args
      |> Error.unwrap!

  /-- Create operator of kind:

  - `Kind.DIVISIBLE` (to support arbitrary precision integers)

  See `cvc5.Kind` for a description of the parameters.

  - `kind`: The kind of the operator.
  - `arg`: The string argument to this operator.

  -/
  private def mkOpOfString : TermManager → (kind : Kind) → (arg : String) → Except Error Op
  where
    /-- Create divisibility-by operator, supports arbitrary precision. -/
    mkOpDivisible (tm : TermManager) (n : Nat) (_valid : 0 < n := by simp) : Op :=
      tm.mkOpOfString Kind.DIVISIBLE (toString n)
      |> Error.unwrap!

  /-- Create n-ary term of given kind.

  - `kind`: The kind of the term.
  - `children`: The children of the term.
  -/
  def mkTerm : TermManager → (kind : Kind) → (children : Array Term := #[]) → Except Error Term
  where
    mkTerm! tm kind children :=
      mkTerm tm kind children
      |> Error.unwrap!

  /-- Create n-ary term of given kind from a given operator.

  Create operators with `mkOp`.

  - `op`: The operator.
  - `children`: The children of the term.
  -/
  def mkTermOfOp : TermManager → (op : Op) → (children : Array Term := #[]) → Except Error Term
  where
    mkTermOfOp! tm op children :=
      mkTermOfOp tm op children
      |> Error.unwrap!

  /-- Create a free constant.

  Note that the returned term is always fresh, even if the same arguments were provided on a
  previous call to `mkConst`.

  - `sort`: The sort of the constant.
  - `symbol`: The name of the constant.
  -/
  def mkConst : TermManager → (sort : cvc5.Sort) → (symbol : String) → Term

  /-- Create a bound variable to be used in a binder (i.e., a quantifier, a lambda, or a witness
    binder).

  The returned term is always fresh, even if the same arguments were provided on a previous call to
  `mkVar`.

  - `sort`: The sort of the constant.
  - `symbol`: The name of the constant.
  -/
  def mkVar : TermManager → (sort : cvc5.Sort) → (symbol : String) → Term

end TermManager

namespace Solver

variable [Monad m]

/-- Only used by FFI to wrap *success* results. -/
@[export solver_val]
private def val (a : α) : SolverT m α := pure a

/-- Only used by FFI to wrap errors. -/
@[export solver_err]
private def err (e : Error) : SolverT m α := throw e

/-- Only used by FFI to wrap cvc5 errors. -/
@[export solver_errOfString]
private def errorOfString (msg : String) : SolverT m α := throw (.error msg)

defs! "solver"
  /-- Constructor.

  Constructs solver instance from a given term manager instance.

  - `tm`: The associated term manager.
  -/
  def new : (tm : TermManager) → Solver

  /-- Get a string representation of the version of this solver. -/
  def getVersion : SolverT m String

  /-- Simplify a term or formula based on rewriting and (optionally) applying substitutions for
  solved variables.

  If `applySubs` is true, then for example, if `(= x 0)` was asserted to this solver, this function
  may replace occurrences of `x` with `0`.

  - `t` The term to simplify.
  - `applySubs` True to apply substitutions for solved variables.
  -/
  def simplify : (term : Term) → (applySubs : Bool := false) → SolverT m Term

  /-- Produces an interpolant `I` for the conjunction of the current set of assumptions `A` and the
  input term `B`.

  Requires option `produce-interpolants` to be set to a mode different from `none`.

  `I` is such that `A → I` and `I → B` are valid, and `I` only mentions symbols that appear both in
  `A` and `B`.
  -/
  private def getInterpolantOrNull (force := "getInterpolant") : (term : Term) → SolverT m Term
  where
    getInterpolant? (term : Term) : SolverT m (Option Term) := do
      let i ← getInterpolantOrNull term
      if i.isNull then return none else return i

  /-- Get the next interpolant.

  (Repeated) calls to this function are only legal after a call to `getInterpolant?` that did not
  yield `none`.

  It is guaranteed to produce a syntactically different interpolant *w.r.t.* the last returned
  interpolant.

  Requires incremental mode.

  `I` is such that `A → I` and `I → B` are valid, and `I` only mentions symbols that appear both in
  `A` and `B`, where `A` is the current set of assertions and `B` is given in the input by the last
  call to `getInterpolant?`.
  -/
  private def getInterpolantNextOrNull (force := "getInterpolantNext")
  : SolverT m Term
  where
    getInterpolantNext? : SolverT m (Option Term) := do
      let i ← getInterpolantNextOrNull
      if i.isNull then return none else return i

  /-- Get an abduct.

  Requires to enable option `produce-abducts`.

  - `conj`: The conjecture term.

  Returns a term `C` such that `A ∧ C` is satisfiable, and `A ∧ ¬ B ∧ C` is unsatisfiable, where `A`
  is the current set of assertions and `B` is given in the input by `conj`, or the null term if such
  a term cannot be found.
  -/
  private def getAbductOrNull (force := "getAbduct") : (conj : Term) → SolverT m Term
  where
    getAbduct? (term : Term) : SolverT m (Option Term) := do
      let i ← getAbductOrNull term
      if i.isNull then return none else return i

  /-- Get the next abduct.

  (Repeated) calls to this function are only legal after a call to `getAbduct?` that did not yield
  `none`.

  It is guaranteed to produce a syntactically different abduct *w.r.t.* the last returned abduct if
  not `none`.

  Requires to enable incremental mode.

  Returns a term `C` such that `A ∧ C` is satisfiable and `A ∧ ¬ B ∧ C` is unsatisfiable, where `A`
  is the current set of assertions and `B` is given in the input by the last call to `getAbduct?`.
  -/
  private def getAbductNextOrNull (force := "getAbductNext")
  : SolverT m Term
  where
    getAbductNext? : SolverT m (Option Term) := do
      let i ← getAbductNextOrNull
      if i.isNull then return none else return i

  /-- Do quantifier elimination.

  Quantifier elimination is only complete for logics such as `LRA`, `LIA`, and `BV`.

  - `q`: A quantified formula of the form `Qx₁ ... Qxₙ , P x₁ ... xₙ y₁ ... yₖ` where
    - `Qxᵢ` is a set of quantified variables of the form `Q a₁ ... aₘ` with `Q` is `∀` or `∃`, and
    - `P x₁ ... xₙ y₁ ... yₖ` is a quantifier-free formula.

  Returns a formula `φ` such that, given the current set of formulas `A` asserted to this solver:
  - `A ∧ q` and `A ∧ φ` are equivalent, and
  - `φ` is a quantifier-free formula containing only free variables in `{y₁, ..., yₖ}`.
  -/
  def getQuantifierElimination : (q : Term) → SolverT m Term


  /-- Do partial quantifier elimination, which can be used for incrementally computing the result of
    a quantifier elimination.

  Quantifier Elimination is only complete for logics such as `LRA`, `LIA`, and `BV`.

  - `q`: A quantified formula of the form `Q x_1 ... Q x_n, P(x_1, ..., x_n, y_1, ..., y_m)` where
    - `Q x_i` is a set of quantifier variables of the form
      - `z_1, ..., z_k`, and
      - `P(x_1, ..., x_n, y_1, ..., y_m)` is a quantifier-free formula

  Returns a formula `φ` such that, given the current set of formulas `A` asserted to the solver:
  - `A ∧ q → A ∧ φ` if `Q` is `∀`, and `A ∧ φ → A ∧ q` if `Q` is `∃`;
  - `φ` is a quantifier-free formula containing only free variables in `y_1, ..., y_n`;
  - if `Q` is `∃`, let `A ∧ Q_n` be the formula `A ∧ ¬(φ ∧ Q_1) ∧ ... ∧ ¬(φ ∧ Q_n)` where for each
    `i = [1, n]` formula `φ ∧ Q_i` is the result of calling `getQuantifierEliminationDisjunct` for
    `q` with the set of assertions `A ∧ Q_{i-1}`.

    Similarly, if `Q` is `∀`, then let `A ∧ Q_n` be `A ∧ (φ ∧ Q_1) ∧ ... ∧ (φ ∧ Q_n)` where `φ ∧
    Q_i` is the same as above.

    In either case, we have that `φ ∧ Q_j` will eventually be true or false, for some finite `j`.
  -/
  def getQuantifierEliminationDisjunct : (q : Term) → SolverT m Term

  /-- Set option.

  - `option`: The option name.
  - `value`: The option value.
  -/
  def setOption : (option value : String) → SolverT m Unit

  /-- Remove all assertions. -/
  def resetAssertions : SolverT m Unit

  /-- Set logic.

  - `logic`: The logic to set.
  -/
  def setLogic : (logic : String) → SolverT m Unit

  /-- Declares a function symbol `symbol` with signature `in_sorts → out_sort`.

  If `fresh`, then a new (fresh) `Term` is always produced; otherwise, the `Term` will always be
  (physically) the same.

  See also `declareFreshFun`.
  -/
  def declareFun :
    (symbol : String)
    → (in_sorts : Array cvc5.Sort) → (out_sort : cvc5.Sort)
    → (fresh : Bool)
    → SolverT m Term

  /-- Declares a sort symbol `symbol` with arity `arity`.

  If `fresh`, then a new (fresh) `Sort` is always produced; otherwise, the `Sort` will always be
  (physically) the same.

  See also `declareFreshSort`.
  -/
  def declareSort :
    (symbol : String) → (arity: Nat) → (fresh : Bool) → SolverT m cvc5.Sort

  /-- Assert a formula.

  - `term`: The formula to assert.
  -/
  def assertFormula : (term : Term) → SolverT m Unit

  /-- Check satisfiability. -/
  def checkSat : SolverT m Result

  /-- Check satisfiability assuming the given formulas.

  - `assumptions`: The formulas to assume.
  -/
  def checkSatAssuming : (assumptions : Array Term) → SolverT m Result

  /-- Get a proof associated with the most recent call to `checkSat`.

  Requires to enable option `produce-proofs`
  -/
  def getProof : SolverT m (Array Proof)

  /-- Get the value of the given term in the current model.

  - `term`: The term for which the value is queried.
  -/
  def getValue : (term : Term) → SolverT m Term

  /-- Get the values of the given terms in the current model.

  - `term`: The terms for which the value is queried.
  -/
  def getValues : (term : Array Term) → SolverT m (Array Term)

  /-- Get the domain elements of the uninterpreted sort `s` in the current model.

  The current model interprets `s` as the finite sort whose domain elements are given in the return
  value of this function.

  - `s`: The uninterpreted sort in question.
  -/
  def getModelDomainElements : (s : cvc5.Sort) → SolverT m (Array Term)

  /-- Prints a proof as a string in a selected proof format mode.

  Other aspects of printing are taken from the solver options.

  - `proof`: A proof, usually obtained from `getProof`.
  -/
  def proofToString : (proof : Proof) → SolverT m String

  /-- Parse a string containing SMT-LIB commands.

  Commands that produce a result such as `(check-sat)`, `(get-model)`, ... are executed but the
  results are ignored.
  -/
  def parse : String → SolverT m Unit

  /-- Append `symbol` to the current list of universal variables.

  - `name`: The name of the universal variable.
  - `sort`: The sort of the universal variable.
  -/
  def declareSygusVar : (symbol : String) → (sort : cvc5.Sort) → SolverT m Term

  /-- Create a Sygus grammar.

  The first non-terminal is treated as the starting non-terminal, so the order of non-terminals
  matters.

  - `bountVars`: The parameters to corresponding synth-fun/synth-inv.
  - `ntSymbols`: The pre-declaration of the non-terminal symbols.
  -/
  def mkGrammar : (boundVars : Array Term) → (ntSymbols : Array Term) → SolverT m Grammar

  /-- Synthesize n-ary function.

  - `symbol` : The name of the function.
  - `boundVars` : The parameters to this function.
  - `sort`: The sort of the return value of this function.
  -/
  def synthFun : (symbol : String) → (boundVars : Array Term) → (sort : cvc5.Sort) → SolverT m Term

  /-- Synthesize n-ary function following specified syntactic constraints.

  - `symbol` : The name of the function.
  - `boundVars` : The parameters to this function.
  - `sort`: The sort of the return value of this function.
  - `grammar`: The syntactic constraints.
  -/
  def synthFunWith
  : (symbol : String) → (boundVars : Array Term) → (sort : cvc5.Sort)
  → (grammar : Grammar)
  → SolverT m Term

  /-- Add a formula to the set of Sygus constraints.

  - `term`: The formula to add as a constraint.
  -/
  def addSygusConstraint : (term : Term) → SolverT m Unit

  /-- Get the list of Sygus constraints. -/
  def getSygusConstraints : SolverT m (Array Term)

  /-- Add a formula to the set of Sygus assumptions.

  - `term`: The formula to add as an assumption.
  -/
  def addSygusAssumption : (term : Term) → SolverT m Unit

  /-- Get the list of Sygus assumptions. -/
  def getSygusAssumptions : SolverT m (Array Term)

  /-- Add a set of sygus constraints to the current state that correspond to an invariant synthesis
  problem.

  - `inv`: The function-to-synthesize.
  - `pre`: The pre-condition.
  - `trans`: The transition relation.
  - `post`: The post-condition.
  -/
  def addSygusInvConstraint
  : (inv : Term) → (pre : Term) → (trans : Term) → (post : Term) → SolverT m Unit

  /-- Try to find a solution for the synthesis conjecture corresponding to the current list of
    functions-to-synthesize, universal variables and constraints.

  The result of the check, which is "solution" if the check found a solution in which case solutions
  are available via `getSynthSolutions`, "no solution" if it was determined there is no solution, or
  "unknown" otherwise.
  -/
  def checkSynth : SolverT m SynthResult

  /-- Get the synthesis solution of the given term. This function should be called immediately after the solver answers unsat for sygus input.

  - `term`: The term for which the synthesis solution is queried.
  -/
  def getSynthSolution : (term : Term) → SolverT m Term
  where
    /-- Get the synthesis solutions of the given terms.

    This function should be called immediately after the solver answers unsat for sygus input.

    - `terms`: The terms for which the synthesis solutions is queried.
    -/
    getSynthSolutions (terms : Array Term) : SolverT m (Array Term) := do
      let mut res := Array.mkEmpty terms.size
      for term in terms do
        res := res.push (← getSynthSolution term)
      return res

  /-- Find a target term of interest using sygus enumeration, with no provided grammar.

  The solver will infer which grammar to use in this call, which by default will be the grammars
  specified by the function(s)-to-synthesize in the current context.

  - `fst`: The identifier specifying what kind of term to find.
  -/
  private def findSynthOrNull (force := "findSynth") : (fst : FindSynthTarget) → SolverT m Term
  where
    findSynth? (fst : FindSynthTarget) : SolverT m (Option Term) := do
      let term ← findSynthOrNull fst
      if term.isNull then return none else return term

  /-- Find a target term of interest using sygus enumeration with a provided grammar.

  - `fst`: The identifier specifying what kind of term to find.
  - `grammar`: The grammar for the term.
  -/
  private def findSynthWithOrNull (force := "findSynthWith")
  : (fst : FindSynthTarget) → (grammar : Grammar) → SolverT m Term
  where
    findSynthWith? (fst : FindSynthTarget) (grammar : Grammar) : SolverT m (Option Term) := do
      let term ← findSynthWithOrNull fst grammar
      if term.isNull then return none else return term

  /-- Try to find a next target term of interest using sygus enumeration.

  (Repeated) calls to this function are only legal after a call to `findSynth?`/`findSynthWith?`
  that did not yield `none`.
  -/
  def findSynthNextOrNull (force := "findSynthNext") : SolverT m Term
  where
    findSynthNext? : SolverT m (Option Term) := do
      let term ← findSynthNextOrNull
      if term.isNull then return none else return term

/-- Run a `query` given a term manager `tm`. -/
def run (tm : TermManager) (query : SolverT m α) : m (Except Error α) :=
  return match ← ExceptT.run query (new tm) with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

end Solver

end cvc5
