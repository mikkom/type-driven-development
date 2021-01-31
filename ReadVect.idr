module ReadVect

import Data.Vect

readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) =
  do line <- getLine
     rest <- readVectLen k
     pure (line :: rest)

data VectUnknown : Type -> Type where
     MkVect : (len : Nat) -> Vect len a -> VectUnknown a

{-
readVect : IO (VectUnknown String)
readVect =
  do x <- getLine
     if x == ""
        then pure $ MkVect _ []
        else do MkVect _ xs <- readVect
                pure $ MkVect _ (x :: xs)
-}

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) =
  putStrLn (show xs ++ " (length " ++ show len ++ ")")

anyVect : (n ** Vect n String)
anyVect = (3 ** ["Rod", "Jane", "Freddy"])

readVect : IO (len ** Vect len String)
readVect =
  do x <- getLine
     if x == ""
        then pure $ (_ ** [])
        else do (_ ** xs) <- readVect
                pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs =
  do putStrLn "Enter first vector (blank line to end):"
     (n ** xs) <- readVect
     putStrLn "Enter second vector (blank line to end):"
     (m ** ys) <- readVect
     case exactLength n ys of
          Just ys' => printLn $ zip xs ys'
          Nothing => putStrLn $ "No good, lengths were " ++ show n ++ " and " ++ show m

readToBlank : IO (List String)
readToBlank =
  do x <- getLine
     if x == ""
        then pure []
        else do xs <- readToBlank
                pure (x :: xs)

readAndSave : IO ()
readAndSave =
  do putStrLn "Enter input (blank line to end):"
     xs <- readToBlank
     putStr "Input file name: "
     fileName <- getLine
     Right _ <- writeFile fileName (unlines xs) | Left err => printLn err
     putStrLn "All done."

readLines: (file : File) -> IO (n : Nat ** Vect n String)
readLines file =
  do eof <- fEOF file
     if eof
        then pure (_ ** [])
        else do Right line <- fGetLine file | Left err => do printLn err
                                                             pure (_ ** [])
                (_ ** lines) <- readLines file
                pure (_ ** line :: lines)

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename =
  do Right file <- openFile filename Read | Left err => do printLn err
                                                           pure (_ ** [])
     ret <- readLines file
     closeFile file
     pure ret
