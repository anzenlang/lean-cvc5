/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Data.Rat

import cvc5.Term.Defs
import cvc5.Op.Defs


namespace cvc5.Term

@[extern "term_getOp"]
opaque getOp : Term → Op