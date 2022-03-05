module InteractivePrograms

%default total

data RunIO : Type -> Type where
     Quit : a -> RunIO a
     Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

greet : RunIO ()
greet = do
  putStr "Enter your name: "
  name <- getLine
  if name == ""
     then do
       putStrLn "Bye bye!"
       Quit ()
     else do
       putStrLn ("Hello " ++ name)
       greet

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

partial
forever : Fuel
forever = More forever

run : Fuel -> RunIO a -> IO (Maybe a)
run Dry action = pure Nothing
run (More fuel) (Quit x) = pure (Just x)
run (More fuel) (Do action cont) = do
  res <- action
  run fuel (cont res)

partial
main : IO ()
main = ignore $ run forever greet
