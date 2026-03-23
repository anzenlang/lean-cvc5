import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_skolem_id_black.cpp>
-/

namespace cvc5.Test

partial def iterAll [Monad m] (f : SkolemId → m Unit) : m Unit :=
  loop none 0
where loop (prev : Option SkolemId) (n : Nat) : m Unit := do
  let k := SkolemId.ofNat n
  f k
  if prev = some k then return () else loop (some k) n.succ

test![TestApiBlackSkolemId, skolemIdToString] do
  iterAll fun si => assertNe "?" si.toString

test![TestApiBlackSkolemId, skolemIdHash] do
  assertEq SkolemId.PURIFY.ctorIdx SkolemId.PURIFY.hash.toNat
  assertNe SkolemId.PURIFY.ctorIdx SkolemId.INTERNAL.hash.toNat
