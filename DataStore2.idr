module DataStore2

import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) ->
              (items : Vect size String) ->
              DataStore

size : DataStore -> Nat
size (MkData size _) = size

items : (store : DataStore) -> Vect (size store) String
items (MkData _ xs) = xs

addToStore : DataStore -> String -> DataStore
addToStore (MkData _ items) item = MkData _ (items ++ [item])

data Command = Add String
             | Get Integer
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" item = Just $ Add item
parseCommand "get" val with (all isDigit (unpack val))
  | True = Just $ Get (cast val)
  | _ = Nothing
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input: String) -> Maybe Command
parse input = case span (/= ' ') input of
              (cmd, args) => parseCommand cmd (ltrim args)

getEntry : Integer -> DataStore -> Maybe (String, DataStore)
getEntry pos store = case integerToFin pos (size store) of
                       Nothing => Just ("Out of range\n", store)
                       (Just i) => Just (index i (items store) ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
                           Nothing => Just ("Invalid command\n", store)
                           (Just (Add item)) =>
                             Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                           (Just (Get pos)) => getEntry pos store
                           (Just Quit) => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
