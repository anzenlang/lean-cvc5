/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Command` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_datatype_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackParametricDatatype, proj_issue387] tm => do
  -- unused in the original test
  let _s1 ← tm.getBooleanSort

  let u2 ← tm.mkUninterpretedSortConstructorSort 1
  let p1 ← tm.mkParamSort "_x4"

  let _ ← tm.mkDatatypeDecl "_x0" #[p1]
  let ctorDecl1 ← tm.mkDatatypeConstructorDecl "_x18"
  (u2.instantiate #[p1, p1] >>= ctorDecl1.addSelector "_x17") |>  assertError
    "arity mismatch for instantiated sort constructor"
