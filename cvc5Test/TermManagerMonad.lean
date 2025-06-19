import cvc5Test.Init

namespace cvc5.Test

def buildSum : TermManagerIO Unit := do
  let int ← cvc5.Sort.int
  println! "int: {int}"
  let a ← Term.mkConst int "a"
  println! "a: {a}"
  let five ← Term.mkInt 5
  println! "five: {five}"
  let term ← Term.mk Kind.ADD #[a, five]
  println! "term: {term}"

/--
info:
running
int: Int
a: a
five: 5
term: (+ a 5)
done
-/
#guard_msgs in #eval do
  println! "running"
  if let (.error e) ← buildSum.run
  then println! "{e}"
  else println! "done"
