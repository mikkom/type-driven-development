module Predicates

import Data.Vect

data MyElem : a -> Vect k a -> Type where
     Here : MyElem x (x :: xs)
     There : (later : MyElem x xs) -> MyElem x (y :: xs)

oneInVector : MyElem 1 [1, 2, 3]
oneInVector = Here

twoInVector : MyElem 2 [1, 2, 3]
twoInVector = There Here

threeInVector : MyElem 3 [1, 2, 3]
threeInVector = There (There Here)

removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (value = x) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem' : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
isElem' value [] = No notInNil
isElem' value (x :: xs) = 
  case decEq value x of
       (Yes Refl) => Yes Here
       (No notHere) => case isElem' value xs of
                            (Yes prf) => Yes (There prf)
                            (No notThere) => No (notInTail notHere notThere)

data ListElem : a -> List a -> Type where
     ListHere : ListElem x (x :: xs)
     ListThere : (later : ListElem x xs) -> ListElem x (y :: xs)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

noLastInNil : Last [] value -> Void
noLastInNil LastOne impossible
noLastInNil (LastCons _) impossible

noLastInSingleton : (contra : (x = value) -> Void) -> Last [x] value -> Void
noLastInSingleton contra LastOne = contra Refl
noLastInSingleton contra (LastCons later) = noLastInNil later

noLastInTail : (contra : Last (x :: xs) value -> Void) ->
               Last (y :: (x :: xs)) value -> Void
noLastInTail contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No noLastInNil
isLast [x] value = case decEq x value of
                        (Yes Refl) => Yes LastOne
                        (No contra) => No (noLastInSingleton contra)
isLast (y :: (x :: xs)) value = case isLast (x :: xs) value of
                                     (Yes prf) => Yes (LastCons prf)
                                     (No contra) => No (noLastInTail contra)
