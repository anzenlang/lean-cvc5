/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Solver.Defs
import cvc5.Term.Manager



namespace cvc5



namespace Solver

@[extern "solver_new"]
opaque mk : Term.Manager → Solver

variable [Monad m]

def run (tm : Term.Manager) (query : SolverT m α) : m (Except Error α) := do
  match ← ExceptT.run query (mk tm) with
  | (.ok x, _) => return .ok x
  | (.error e, _) => return .error e

end Solver



namespace Ctx



end Ctx
