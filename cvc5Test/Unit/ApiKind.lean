import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_kind_black.cpp>
-/

namespace cvc5.Test

partial def iterAll [Monad m] (f : Kind → m Unit) : m Unit :=
  loop none 0
where loop (prev : Option Kind) (n : Nat) : m Unit := do
  let k := Kind.ofNat n
  f k
  if prev = some k then return () else loop (some k) n.succ

test![TestApiKind, kindToString] do iterAll fun
  | k@.INTERNAL_KIND => assertEq "INTERNAL_KIND" k.toString
  | k@.UNDEFINED_KIND => assertEq "UNDEFINED_KIND" k.toString
  | k => do
    let s := k.toString
    assertNe "INTERNAL_KIND" s
    assertNe "UNDEFINED_KIND" s

test![TestApiKind, kindHash] do
  -- assertion failures here indicate a problem in lean-to-cpp conversion
  for idx in [Kind.INTERNAL_KIND.ctorIdx : Kind.LAST_KIND.ctorIdx] do
    let k := Kind.ofNat idx
    if k = Kind.INTERNAL_KIND then
      assertEq (k.hash + 2) ⟨UInt64.size⟩
    else if k  = Kind.UNDEFINED_KIND then
      assertEq (k.hash + 1) ⟨UInt64.size⟩
    else
      assertEq (k.hash + 2) ⟨k.ctorIdx⟩
