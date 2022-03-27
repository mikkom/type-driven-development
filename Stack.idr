module Stack

import Data.Vect

%default total

data StackCmd : Type -> Nat -> Nat -> Type where
     Push : Integer -> StackCmd () height (S height)
     Pop : StackCmd Integer (S height) height
     Top : StackCmd Integer (S height) (S height)

     GetStr : StackCmd String height height
     PutStr : String -> StackCmd () height height

     Pure : ty -> StackCmd ty height height
     (>>=) : StackCmd a height1 height2 -> (a -> StackCmd b height2 height3) ->
             StackCmd b height1 height3

testAdd : StackCmd Integer 0 0
testAdd = do
  Push 10
  Push 20
  val1 <- Pop
  val2 <- Pop
  Pure (val1 + val2)

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack stk (Pure x) = pure (x, stk)
runStack stk GetStr = do
  str <- getLine
  pure (str, stk)
runStack stk (PutStr str) = do
  putStr str
  pure ((), stk)
runStack stk (cmd >>= f) = do
  (res, stk') <- runStack stk cmd
  runStack stk' (f res)

doOp : (Integer -> Integer -> Integer) ->
       StackCmd () (S (S height)) (S height)
doOp f = do
  val1 <- Pop
  val2 <- Pop
  Push (f val1 val2)

doDiscard : StackCmd () (S height) height
doDiscard = do
  Pop
  Pure ()

doNegate : StackCmd () (S height) (S height)
doNegate = do
  val <- Pop
  Push (- val)

doDuplicate : StackCmd () (S height) (S (S height))
doDuplicate = do
  val <- Top 
  Push val

data StackIO : Nat -> Type where
     Do : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel 
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) stk (Do c f) = do
  (res, stk') <- runStack stk c
  run fuel stk' (f res)
run Dry stk p = pure ()

data StkInput
  = Number Integer
  | Add
  | Subtract
  | Multiply
  | Negate
  | Discard
  | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "sub" = Just Subtract
strToInput "mul" = Just Multiply
strToInput "neg" = Just Negate
strToInput "discard" = Just Discard
strToInput "dup" = Just Duplicate
strToInput x =
  if all isDigit (unpack x)
     then Just (Number (cast x))
     else Nothing

mutual
  tryOp : (Integer -> Integer -> Integer) -> StackIO height
  tryOp f {height = S (S h)} = do
    doOp f
    res <- Top
    PutStr (show res ++ "\n")
    stackCalc
  tryOp _ = do
    PutStr "Not enough items on the stack\n"
    stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = S h} = do
    doDiscard
    stackCalc
  tryDiscard = do
    PutStr "Not enough items on the stack\n"
    stackCalc

  tryNegate : StackIO height
  tryNegate {height = S h} = do
    doNegate
    stackCalc
  tryNegate = do
    PutStr "Not enough items on the stack\n"
    stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = S h} = do
    doDuplicate
    stackCalc
  tryDuplicate = do
    PutStr "Not enough items on the stack\n"
    stackCalc

  stackCalc : StackIO height
  stackCalc = do
    PutStr "> "
    input <- GetStr
    case strToInput input of
      Nothing => do
        PutStr "Invalid input\n"
        stackCalc
      Just (Number x) => do
        Push x
        stackCalc
      Just Add => tryOp (+)
      Just Subtract => tryOp (-)
      Just Multiply => tryOp (*)
      Just Negate => tryNegate
      Just Discard => tryDiscard
      Just Duplicate => tryDuplicate

partial
main : IO ()
main = run forever [] stackCalc
