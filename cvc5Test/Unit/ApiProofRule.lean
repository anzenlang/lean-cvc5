import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_proof_rule_black.cpp>
-/

namespace cvc5.Test

partial def ProofRule.iterAll [Monad m] (f : ProofRule → m Unit) : m Unit :=
  loop none 0
where loop (prev : Option ProofRule) (n : Nat) : m Unit := do
  let k := ProofRule.ofNat n
  f k
  if prev = some k then return () else loop (some k) n.succ

test![TestApiBlackProofRule, proofRuleToString] do
  ProofRule.iterAll fun pr => assertNe "?" pr.toString

test![TestApiBlackProofRule, proofRuleHash] do
  assertEq ProofRule.UNKNOWN.ctorIdx ProofRule.UNKNOWN.hash.toNat

partial def ProofRewriteRule.iterAll [Monad m] (f : ProofRewriteRule → m Unit) : m Unit :=
  loop none 0
where loop (prev : Option ProofRewriteRule) (n : Nat) : m Unit := do
  let k := ProofRewriteRule.ofNat n
  f k
  if prev = some k then return () else loop (some k) n.succ

test![TestApiBlackProofRewriteRule, proofRewriteRuleToString] do
  ProofRewriteRule.iterAll fun pr => assertNe "?" pr.toString

test![TestApiBlackProofRewriteRule, proofRewriteRuleHash] do
  assertEq ProofRewriteRule.NONE.ctorIdx ProofRewriteRule.NONE.hash.toNat
