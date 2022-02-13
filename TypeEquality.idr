module TypeEquality

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
     Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = do
  eq <- checkEqNat k j
  pure $ sameS _ _ eq

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = do
  Same len <- checkEqNat m len
  pure input

data Mirror : a -> b -> Type where
     Refl' : Mirror x x

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat' Z Z = Just Refl
checkEqNat' Z (S k) = Nothing
checkEqNat' (S k) Z = Nothing
checkEqNat' (S k) (S j) = do
  eqPrf <- checkEqNat' k j
  pure (cong eqPrf)

sameCons : { xs : List a } -> xs = ys -> (x :: xs = x :: ys)
sameCons Refl = Refl

sameLists : { xs : List a } -> x = y -> xs = ys -> (x :: xs = y :: ys)
sameLists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
     ThreeRefl : ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z ThreeRefl = ThreeRefl
