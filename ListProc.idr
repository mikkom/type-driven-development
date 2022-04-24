module ListProc

import ProcessLib

data ListAction : Type where
  Length : List a -> ListAction
  Append : List a -> List a -> ListAction

ListType : ListAction -> Type
ListType (Length xs) = Nat
ListType (Append {a} xs ys) = List a

procList : Service ListType ()
procList = do
  Respond (\msg => case msg of
                     Length xs => Pure (length xs)
                     Append xs ys => Pure (xs ++ ys))
  Loop procList

procMain : Client ()
procMain = do
  Just list <- Spawn procList
    | Nothing => Action (putStrLn "Failed to spawn list proc")
  len <- Request list (Length [1,2,3])
  Action (printLn len)
  app <- Request list (Append [4,5,6] [7,8,9])
  Action (printLn app)
