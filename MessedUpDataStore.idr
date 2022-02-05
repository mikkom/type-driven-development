module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (s1 .+. s2) = (SchemaType s1, SchemaType s2)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)


addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema' size' items') newitem = MkData schema' _ (addToData items')
  where
    addToData : Vect old (SchemaType schema') -> Vect (S old) (SchemaType schema')
    addToData [] = [newitem]
    addToData (i :: is) = i :: addToData is

data Command : Schema -> Type where
     Add : SchemaType schema -> Command schema
     Get : Integer -> Command schema
     Size : Command schema
     -- Search : String -> Command schema
     Quit : Command schema

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Just (res, "") => Just res
                                  Just _ => Nothing
                                  Nothing => Nothing

parseCommand : (schema: Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" str = let item = parseBySchema schema str in map Add item
-- parseCommand schema "search" str = Just (Search str)
parseCommand schema "size" "" = Just Size
parseCommand schema "get" val = case all isDigit (unpack val) of
                                     False => Nothing
                                     True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (a .+. b)} (i1, i2) = display i1 ++ ", " ++ display i2

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing => Just ("Out of range\n", store)
           (Just id) => Just (display (index id store_items) ++ "\n", store)

zipWithIndex : Vect n a -> Vect n (a, Nat)
zipWithIndex xs = helper xs 0
  where
    helper : Vect n a -> Nat -> Vect n (a, Nat)
    helper [] _ = []
    helper (x :: xs) k = (x, k) :: helper xs (S k)

prettyPrint : (p ** Vect p (String, Nat)) -> String
prettyPrint (Z ** []) = ""
prettyPrint (S k ** (str, n) :: xs) = cast n ++ ": " ++ str ++ "\n" ++ prettyPrint (k ** xs)

{-
searchString : (str : String) -> (store : DataStore) -> Maybe (String, DataStore)
searchString str store
  = let iis = zipWithIndex (items store)
        matching = filter (isInfixOf str . fst) iis
        strs = prettyPrint matching in
        Just (strs, store)
-}

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse (schema store) inp of
                              Nothing => Just ("Invalid command\n", store)
                              Just (Add item) =>
                                Just ("ID " ++ show (size store) ++ "\n", addToStore store (?convert item))
                              Just (Get pos) => getEntry pos store
                              Just Size => Just (show (size store) ++ "\n", store)
                              -- Just (Search str) => searchString str store
                              Just Quit => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
