import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_sort_kind_black.cpp>
-/

namespace cvc5.Test

partial def iterAll [Monad m] (f : SortKind → m Unit) : m Unit :=
  loop none 0
where loop (prev : Option SortKind) (n : Nat) : m Unit := do
  let k := SortKind.ofNat n
  f k
  if prev = some k then return () else loop (some k) n.succ

test![TestApiSortKind, sortKindToString] do iterAll fun
  | sk@SortKind.INTERNAL_SORT_KIND => assertEq "INTERNAL_SORT_KIND" sk.toString
  | sk@SortKind.UNDEFINED_SORT_KIND => assertEq "UNDEFINED_SORT_KIND" sk.toString
  | sk => do
    let s := sk.toString
    assertNe "INTERNAL_SORT_KIND" s
    assertNe "UNDEFINED_SORT_KIND" s
