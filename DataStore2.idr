module DataStore2

import Data.Vect

infixr 5 .+.

data Schema
  = SString
  | SInt
  | SChar
  | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (s1 .+. s2) = (SchemaType s1, SchemaType s2)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

storeType : DataStore -> Type
storeType = SchemaType . schema

addToStore : (store : DataStore) -> storeType store -> DataStore
addToStore (MkData _ _ items) item = MkData _ _ (items ++ [item])

data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema 
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  GetAll : Command schema
  Size : Command schema
  Search : String -> Command schema
  Quit : Command schema

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = SChar} item = singleton item
display {schema = (sx .+. sy)} (x, y) = display x ++ ", " ++ display y

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
           (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
           _ => Nothing
    getQuoted _ = Nothing
parsePrefix SInt input =
  case span isDigit input of
       ("", rest) => Nothing
       (num, rest) => Just $ (cast num, ltrim rest)
parsePrefix SChar input =
  case unpack input of
       (ch :: rest) => Just $ (ch, ltrim (pack rest))
       _ => Nothing
parsePrefix (sx .+. sy) input = do
  (x, rest) <- parsePrefix sx input
  (y, rest') <- parsePrefix sy rest
  pure ((x, y), rest')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Just (res, "") => Just res
                                  Just _ => Nothing
                                  Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
  case xs of
       [] => Just SString
       _ => (SString .+.) <$> parseSchema xs
parseSchema ("Int" :: xs) =
  case xs of
       [] => Just SInt
       _ => (SInt .+.) <$> parseSchema xs
parseSchema ("Char" :: xs) =
  case xs of
       [] => Just SChar
       _ => (SChar .+.) <$> parseSchema xs
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "schema" input = SetSchema <$> parseSchema (words input)
parseCommand schema "add" item = Add <$> parseBySchema schema item
parseCommand _ "get" "" = Just GetAll
parseCommand _ "get" val with (all isDigit (unpack val))
  | True = Just $ Get (cast val)
  | _ = Nothing
parseCommand _ "size" "" = Just Size
parseCommand _ "search" str = Just $ Search str
parseCommand _ "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema: Schema) -> (input: String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

getEntry : Integer -> (store : DataStore) -> String
getEntry pos store =
  case integerToFin pos (size store) of
       Nothing => "Out of range\n"
       (Just i) => display (index i (items store)) ++ "\n"

indexed : Vect n a -> Vect n (Nat, a)
indexed = go Z
  where
    go : Nat -> Vect n a -> Vect n (Nat, a)
    go k [] = []
    go k (x :: xs) = (k, x) :: go (S k) xs

mapi : ((Nat, a) -> b) -> Vect n a -> Vect n b
mapi f xs = map f $ indexed xs

getAll : (store : DataStore) -> String
getAll store = concat $ mapi go (items store)
  where
    go : (Nat, storeType store) -> String
    go (idx, item) = show idx ++ ": " ++ display item ++ "\n"

searchItems : String -> DataStore -> Maybe (String, DataStore)
searchItems str store =
  case filter (isInfixOf str . snd) (indexed $ map display (items store)) of
       (Z ** []) => Just ("No results\n", store)
       (n ** results) => Just (concatMap printResult results, store)
  where
    printResult : (Nat, String) -> String
    printResult (i, str) = show i ++ ": " ++ str ++ "\n"

processInput : (store : DataStore) -> String -> Maybe (String, DataStore)
processInput store input =
  case parse (schema store) input of
       Nothing => Just ("Invalid command\n", store)
       Just (SetSchema newSchema) =>
         if size store == 0
         then Just ("Schema updated\n", MkData newSchema _ [])
         else Just ("The store is not empty\n", store)
       Just (Add item) =>
         Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
       Just (Get pos) => Just $ (getEntry pos store, store)
       Just GetAll => Just $ (getAll store, store)
       Just Size => Just (show (size store) ++ "\n", store)
       Just (Search str) => searchItems str store
       Just Quit => Nothing

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " processInput
