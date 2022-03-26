module CustomState

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

data State : (stateType : Type) -> Type -> Type where
     Get : State stateType stateType
     Put : stateType -> State stateType ()
     Pure : ty -> State stateType ty
     Bind : State stateType a -> (a -> State stateType b) -> State stateType b

mutual
  Functor (State stateType) where
    map f state = do
      val <- state
      pure (f val)

  Applicative (State stateType) where
    pure x = Pure x
    mf <*> mx = do
      f <- mf
      x <- mx
      Pure (f x)

  Monad (State stateType) where
    (>>=) = Bind

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node l x r) = do
  l' <- treeLabelWith l
  (label :: labels) <- get
  put labels
  r' <- treeLabelWith r
  pure (Node l' (label, x) r')

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put x) st = ((), x)
runState (Pure x) st = (x, st) 
runState (Bind cmd prog) st =
  let (val, st') = runState cmd st
  in  runState (prog val) st'

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst $ runState (treeLabelWith tree) [1..]

addIfPositive : Integer -> State Integer Bool
addIfPositive val = do
  when (val > 0) $ do
    current <- get
    put (current + val)
  pure (val > 0)

addPositives : List Integer -> State Integer Nat
addPositives vals = do
  added <- traverse addIfPositive vals
  pure $ length (filter id added)
