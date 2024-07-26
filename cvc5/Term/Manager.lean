/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Term.Defs



namespace cvc5.Term

private opaque ManagerImpl : NonemptyType.{0}

def Manager : Type := ManagerImpl.type

namespace Manager

instance instNonempty : Nonempty Manager := ManagerImpl.property

@[extern "termManager_new"]
opaque mk : BaseIO Manager



/-! ## Term creation -/

/-- Creates a boolean constant. -/
@[extern "termManager_mkBoolean"]
opaque mkBoolean : Manager → Bool → Term

@[extern "termManager_mkIntegerFromString"]
private opaque mkIntegerFromString : Manager → String → Term

/-- Creates an integer constant. -/
def mkInteger (tm : Manager) : Int → Term :=
  (mkIntegerFromString tm) ∘ toString

/-- Creates an n-ary `Term` of a given `Kind`. -/
@[extern "termManager_mkTerm"]
opaque mkTerm : Manager → Kind → (children : Array Term := #[]) → Term



variable (self : Manager)

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



/-! ## Sort creation -/

/-- The Boolean Sort. -/
@[extern "termManager_mkBooleanSort"]
opaque mkBoolSort : Manager → cvc5.Sort
