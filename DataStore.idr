module DataStore

import Data.Vect

infixr 5 .+.

public export
data Schema
  = SString
  | SInt
  | SChar
  | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (s1 .+. s2) = (SchemaType s1, SchemaType s2)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (item : SchemaType schema) -> (store : DataStore schema) ->
             DataStore schema 
addToStore item (MkData _ items) = MkData _ (item :: items)

public export
data StoreView : DataStore schema -> Type where
     SNil : StoreView empty 
     SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema)) -> 
                StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (val :: xs) = SAdd (storeViewHelp xs)

total
export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items
