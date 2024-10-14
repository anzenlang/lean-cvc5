/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Autogen

namespace cvc5

cppEnumsToLean! "cvc5_proof_rule.h"

#guard_msgs(drop info) in #check ProofRule
#guard_msgs(drop info) in #check ProofRule.AND_INTRO
#guard_msgs(drop info) in #check (inferInstance : Inhabited ProofRule)
#guard_msgs(drop info) in #check (inferInstance : Repr ProofRule)
#guard_msgs(drop info) in #check (inferInstance : BEq ProofRule)
#guard_msgs(drop info) in #check (inferInstance : Hashable ProofRule)

-- raise confidence that the variants are aligned by checking the last one
/-- info: cvc5.ProofRule.UNKNOWN -/
#guard_msgs in
#eval repr ProofRule.UNKNOWN

#guard_msgs(drop info) in #check ProofRewriteRule
#guard_msgs(drop info) in #check ProofRewriteRule.ARITH_ELIM_LT
#guard_msgs(drop info) in #check (inferInstance : Inhabited ProofRewriteRule)
#guard_msgs(drop info) in #check (inferInstance : Repr ProofRewriteRule)
#guard_msgs(drop info) in #check (inferInstance : BEq ProofRewriteRule)
#guard_msgs(drop info) in #check (inferInstance : Hashable ProofRewriteRule)

-- raise confidence that the variants are aligned by checking the last one
/-- info: cvc5.ProofRewriteRule.UF_BV2NAT_GEQ_ELIM -/
#guard_msgs in
#eval repr ProofRewriteRule.UF_BV2NAT_GEQ_ELIM

namespace ProofRule

@[extern "proofRule_toString"]
protected opaque toString : ProofRule → String

instance : ToString ProofRule := ⟨ProofRule.toString⟩

end ProofRule

namespace ProofRewriteRule

@[extern "proofRewriteRule_toString"]
protected opaque toString : ProofRewriteRule → String

instance : ToString ProofRewriteRule := ⟨ProofRewriteRule.toString⟩

end ProofRewriteRule

end cvc5
