module State

import Control.Monad.State

data Tree a
  = Empty
  | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node l x r) = flatten l ++ x :: flatten r

treeLabelWith : Stream labelType -> Tree a ->
                (Stream labelType, Tree (labelType, a))
treeLabelWith labels Empty = (labels, Empty)
treeLabelWith labels (Node l x r) =
  let (label :: labels', l') = treeLabelWith labels l
      (labels'', r') = treeLabelWith labels' r
  in  (labels'', Node l' (label, x) r')

treeLabelWith' : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith' Empty = pure Empty
treeLabelWith' (Node l x r) = do
  l' <- treeLabelWith' l
  (label :: labels) <- get
  put labels
  r' <- treeLabelWith' r
  pure (Node l' (label, x) r')

treeLabel : Stream labelType -> Tree a -> Tree (labelType, a)
treeLabel labels tree = evalState (treeLabelWith' tree) labels

update : (stateType -> stateType) -> State stateType ()
update f = do
  current <- get
  put (f current)

increase : Nat -> State Nat ()
increase inc = update (+ inc)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase 1
countEmpty (Node l x r) = do
  countEmpty l
  countEmpty r

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\(e, n) => (e + 1, n))
countEmptyNode (Node l x r) = do
  update (\(e, n) => (e, n + 1))
  countEmptyNode l
  countEmptyNode r
