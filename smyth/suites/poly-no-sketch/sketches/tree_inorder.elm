type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

type Tree a
  = Leaf ()
  | Node (Tree a, a, Tree a)

append : forall a . List a -> List a -> List a
append <a> l1 l2 =
  case l1 of
    Nil _ ->
      l2
    Cons p ->
      Cons<a> (#2.1 p, append <a> (#2.2 p) l2)

treeInOrder : forall a . Tree a -> List a
treeInOrder <a> xss =
  ??
