module Main

import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (i :: is) = i :: addToData is

data Command = Add String
             | Get Integer
             | Size
             | Search String
             | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "search" str = Just (Search str)
parseCommand "size" "" = Just Size
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              (Just id) => Just (index id store_items ++ "\n", store)

zipWithIndex : Vect n a -> Vect n (a, Nat)
zipWithIndex xs = helper xs 0
  where
    helper : Vect n a -> Nat -> Vect n (a, Nat)
    helper [] _ = []
    helper (x :: xs) k = (x, k) :: helper xs (S k)


prettyPrint : (p ** Vect p (String, Nat)) -> String
prettyPrint (Z ** []) = ""
prettyPrint (S k ** (str, n) :: xs) = cast n ++ ": " ++ str ++ "\n" ++ prettyPrint (k ** xs)

searchString : (str : String) -> (store : DataStore) -> Maybe (String, DataStore)
searchString str store
  = let iis = zipWithIndex (items store)
        matching = filter (isInfixOf str . fst) iis
        strs = prettyPrint matching in
        Just (strs, store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse inp of
                              Nothing => Just ("Invalid command\n", store)
                              Just (Add item) =>
                                Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                              Just (Get pos) => getEntry pos store
                              Just Size => Just (show (size store) ++ "\n", store)
                              Just (Search str) => searchString str store
                              Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
