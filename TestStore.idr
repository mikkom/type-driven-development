module TestStore

import DataStore
import Data.Vect

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974) $
            addToStore ("Venus", "Venera", 1961) $
            addToStore ("Uranus", "Voyager 2", 1986) $
            addToStore ("Pluto", "New Horizons", 2015) $
            empty

-- empty' : DataStore schema
-- empty' = MkData 0 []

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
  listItems empty | SNil = []
  listItems (addToStore value store) | (SAdd rec) =
    value :: listItems store | rec

filterKeys : (test : SchemaType schema -> Bool) -> 
             DataStore (SString .+. schema) -> List String
filterKeys test input with (storeView input)
  filterKeys test empty | SNil = []
  filterKeys test (addToStore (key, value) store) | (SAdd rec) =
    if test value then key :: rest else rest
      where rest = filterKeys test store | rec

getValues : DataStore (SString .+. schema) -> List (SchemaType schema)
getValues input with (storeView input)
  getValues empty | SNil = []
  getValues (addToStore (key, value) store) | (SAdd rec) =
    value :: getValues store | rec
