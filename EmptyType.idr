module EmptyType

-- import Data.Vect
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

data Void' : Type where

twoPlusTwoAintFive : 2 + 2 = 5 -> Void
twoPlusTwoAintFive Refl impossible

loop : Void
loop = loop

valueAintSucc : (k : Nat) -> k = S k -> Void
valueAintSucc _ Refl impossible

zeroAintSucc : Z = S k -> Void
zeroAintSucc Refl impossible

succAintZero : S k = Z -> Void
succAintZero Refl impossible

noRec: (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroAintSucc
checkEqNat (S k) Z = No succAintZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes (cong prf)
                              (No contra) => No (noRec contra)

exactLength' : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength' {m} len input = case decEq len m of
                                  (Yes Refl) => Just input
                                  (No contra) => Nothing

headUnequal : DecEq a => { xs : Vect n a } -> { ys : Vect n a } ->
       (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => { xs : Vect n a } -> { ys : Vect n a } ->
       (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case (decEq x y, decEq xs ys) of
                                   (No contra, _) => No $ headUnequal contra
                                   (_, No contra) => No $ tailUnequal contra
                                   (Yes Refl, Yes Refl) => Yes Refl
