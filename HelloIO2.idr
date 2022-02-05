module HelloIO2

import Data.Vect
import System

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine 
  pure $ if all isDigit (unpack input)
     then Just (cast input)
     else Nothing

guess : Nat -> Nat -> IO ()
guess target count = do
  putStr $ "Make a guess (you have guessed " ++ show count ++ " times): "
  Just num <- readNumber | Nothing => (putStrLn "Invalid guess" *> guess target count)
  if num == target
     then putStrLn "Correct!"
     else do
       if num < target
          then putStrLn "Too low"
          else putStrLn "Too high"
       guess target (S count)

getRandom : IO Integer
getRandom = do
  t <- time
  pure $ mod t 100 + 1

readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
  x <- getLine
  xs <- readVectLen k
  pure $ x :: xs

data VectUnknown : Type -> Type where
     MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVectPoorly : IO (VectUnknown String)
readVectPoorly = do
  x <- getLine
  if x == ""
     then pure (MkVect _ [])
     else do
       MkVect _ xs <- readVectPoorly
       pure $ MkVect _ (x :: xs)

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) =
  putStrLn $ show xs ++ " (length " ++ show len ++ ")"

anyVect : (n ** Vect n String)
anyVect = (3 ** ["Rod", "Jane", "Freddy"])

readVect : IO (n ** Vect n String)
readVect = do
  x <- getLine
  if x == ""
     then pure (Z ** [])
     else do
       (k ** xs) <- readVect
       pure (S k ** x :: xs)

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector (blank line to end):"
  (len1 ** vec1) <- readVect
  putStrLn "Enter second vector (blank line to end):"
  (len2 ** vec2) <- readVect
  let Just vec2' = exactLength len1 vec2
    | Nothing => putStrLn "The vector lenghts don't match"
  putStrLn $ show (zip vec1 vec2')

readToBlank : IO (List String)
readToBlank = do
  line <- getLine
  if line == ""
     then pure []
     else do
       lines <- readToBlank
       pure $ line :: lines

readAndSave : IO ()
readAndSave = do
  lines <- readToBlank
  putStr "Giev fiel naem: "
  fileName <- getLine
  let contents = intercalate ['\n'] (map unpack lines)
  writeFile fileName (pack contents)
  pure ()

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
    Right file <- openFile filename Read
      | Left err => (printLn err *> pure (Z ** []))
    ret <- go file
    closeFile file
    pure ret
  where
    go : File -> IO (n ** Vect n String)
    go file = do
      False <- fEOF file
        | True => pure (Z ** [])
      Right line <- fGetLine file
        | Left err => (printLn err *> pure (Z ** []))
      (k ** lines) <- go file
      pure (S k ** line :: lines)
