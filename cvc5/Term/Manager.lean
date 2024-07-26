/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Term.Defs



namespace cvc5



private opaque Term.ManagerImpl : NonemptyType.{0}

def Term.Manager : Type := Term.ManagerImpl.type



section lean_type_to_sort

/-- Specifies that a `cvc5.Sort` corresponding to `α` can be constructed with a `Term.Manager`. -/
class ToCvc5Sort (α : Type u) : Type u where
  /-- Creates a `cvc5.Sort`. -/
  mkCvc5Sort : Term.Manager → cvc5.Sort

opaque ToCvc5Sort.Hack (_ : cvc5.Sort) : Type :=
  Unit

instance : CoeSort cvc5.Sort Type where
  coe sort := ToCvc5Sort.Hack sort

-- @[default_instance]
instance (sort : cvc5.Sort) : ToCvc5Sort (ToCvc5Sort.Hack sort) where
  mkCvc5Sort _ := sort

-- instance instToCvc5SortSort (sort : cvc5.Sort) : ToCvc5Sort sort :=
--   inferInstance

end lean_type_to_sort



namespace Term.Manager

instance instNonempty : Nonempty Manager := ManagerImpl.property

@[extern "termManager_new"]
opaque mk : BaseIO Manager



/-! ## Sort creation -/


variable (self : Manager)

open cvc5 (ToCvc5Sort)



@[inherit_doc ToCvc5Sort.mkCvc5Sort]
abbrev mkSort :=
  @ToCvc5Sort.mkCvc5Sort

/-- Boolean sort. -/
@[extern "termManager_mkBooleanSort"]
opaque mkSortBool : Manager → cvc5.Sort

instance instToCvc5SortBool : ToCvc5Sort Bool :=
  ⟨mkSortBool⟩

/-- Integer sort. -/
@[extern "termManager_mkIntegerSort"]
opaque mkSortInt : Manager → cvc5.Sort

instance instToCvc5SortInt : ToCvc5Sort Int :=
  ⟨mkSortInt⟩

/-- Real/Rat sort. -/
@[extern "termManager_mkRealSort"]
opaque mkSortReal : Manager → cvc5.Sort

-- # TODO
-- `Lean.Rat` is not cvc5's `Real`, maybe a bad idea to have that
instance instToCvc5SortRat : ToCvc5Sort Lean.Rat :=
  ⟨mkSortReal⟩

/-- regular expression sort. -/
@[extern "termManager_mkRegExpSort"]
opaque mkSortRegExp : Manager → cvc5.Sort

/-- String sort. -/
@[extern "termManager_mkStringSort"]
opaque mkSortString : Manager → cvc5.Sort

instance instToCvc5SortString : ToCvc5Sort String :=
  ⟨mkSortString⟩

/-- Array sort. -/
@[extern "termManager_mkArraySort"]
opaque mkSortArray : Manager → (idxSort : cvc5.Sort) → (elmSort : cvc5.Sort) → cvc5.Sort

-- # TODO
-- the resulting sort is indexed by `Int`, might not be a good idea to have this :/
instance instToCvc5SortArray [ToCvc5Sort α] : ToCvc5Sort (Array α) where
  mkCvc5Sort tm :=
    let idxSort := tm.mkSort Int
    let elmSort := tm.mkSort α
    tm.mkSortArray idxSort elmSort

/-- BitVec sort. -/
@[extern "termManager_mkBitVectorSort"]
opaque mkSortBitVec : Manager → (size : Nat) → cvc5.Sort

instance instToCvc5BitVec : ToCvc5Sort (BitVec size) where
  mkCvc5Sort tm := tm.mkSortBitVec size



/-! ## Term creation -/

/-- Creates a boolean constant. -/
@[extern "termManager_mkBoolean"]
opaque mkBoolean : Manager → Bool → Term

@[extern "termManager_mkIntegerFromString"]
private opaque mkIntegerFromString : Manager → String → Term

/-- Creates an integer constant. -/
def mkInteger : Int → Term :=
  self.mkIntegerFromString ∘ toString

/-- Creates an n-ary `Term` of a given `Kind`. -/
@[extern "termManager_mkTerm"]
opaque mkTerm : Manager → Kind → (children : Array Term := #[]) → Term

/-- Creates an if-then-else.

- `cnd` must be of sort `Bool`
- `thn` and `els` must have the same sort
-/
def mkIte (cnd thn els : Term) : Term :=
  self.mkTerm .ITE #[cnd, thn, els]

/-- Creates an n-ary equality with `1 < n`.

- all `terms` must have the same sort
-/
def mkEqualN (terms : Array Term) (_ : 1 < terms.size := by simp_arith) : Term :=
  self.mkTerm .EQUAL terms

/-- Creates a binary equality.

- `lft` and `rgt` must have the same sort
-/
def mkEqual (lft rgt : Term) : Term :=
  self.mkEqualN #[lft, rgt]

/-- Creates a negation of the input term.

- `t` must have sort `Bool`
-/
def mkNot (t : Term) : Term :=
  self.mkTerm .NOT #[t]

/-- Creates an implication between two terms.

- `lhs` and `rhs` must have sort `Bool`
-/
def mkImplies (lhs rhs : Term) : Term :=
  self.mkTerm .IMPLIES #[lhs, rhs]
