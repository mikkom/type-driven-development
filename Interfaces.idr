module Interfaces

occurrences : Eq ty => (item: ty) -> (values : List ty) -> Nat
occurrences item values = length $ filter (== item) values

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

data Tree elem
  = Empty 
  | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node l x r) (Node l' x' r') = x == x' && l == l' && r == r'
  (==) _ _ = False

Functor Tree where
  map f Empty = Empty
  map f (Node l x r) = Node (map f l) (f x) (map f r)

Foldable Tree where
  foldr f acc Empty = acc
  foldr f acc (Node l x r) =
    let leftFold = foldr f acc l
        rightFold = foldr f leftFold r
    in  f x rightFold

record Album where
  constructor MkAlbum
  artist : String
  title : String
  year : Integer

Eq Album where
  (==) (MkAlbum artist title year) (MkAlbum artist' title' year') =
    artist == artist' && title == title' && year == year'

Ord Album where
  compare (MkAlbum artist title year) (MkAlbum artist' title' year') =
    case compare artist artist' of
      EQ => case compare year year' of
        EQ => compare title title'
        cmp => cmp
      cmp => cmp


help : Album
help = MkAlbum "The Beatles" "Help" 1965

rubbersoul : Album
rubbersoul = MkAlbum "The Beatles" "Rubber Soul" 1965

clouds : Album
clouds = MkAlbum "Joni Mitchell" "Clouds" 1969

hunkydory : Album
hunkydory = MkAlbum "David Bowie" "Hunky Dory" 1971

heroes : Album
heroes = MkAlbum "David Bowie" "Heroes" 1977

collection : List Album
collection = [help, rubbersoul, clouds, hunkydory, heroes]

Show Album where
  show (MkAlbum artist title year) =
    title ++ " by " ++ artist ++ " (released " ++ show year ++ ")"

data Shape
  = Triangle Double Double
  | Rectangle Double Double
  | Circle Double

Eq Shape where
  (==) (Triangle x h) (Triangle x' h') = x == x' && h == h'
  (==) (Rectangle w h) (Triangle w' h') = w == w' && h == h'
  (==) (Circle r) (Circle r') = r == r'
  (==) _ _ = False

area : Shape -> Double
area (Triangle x h) = 0.5 * x * h
area (Rectangle w h) = w * h
area (Circle r) = 2 * pi * r

Ord Shape where
  compare shape shape' = compare (area shape) (area shape')

data Expr num
  = Val num
  | Add (Expr num) (Expr num)
  | Sub (Expr num) (Expr num)
  | Mul (Expr num) (Expr num)
  | Div (Expr num) (Expr num)
  | Absolut (Expr num)

eval : (Neg num, Integral num, Abs num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Absolut x) = abs (eval x)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub

Abs ty => Abs (Expr ty) where
  abs = Absolut

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Absolut x) = "|" ++ show x ++ "|"

(Eq num, Neg num, Integral num, Abs num) => Eq (Expr num) where
  (==) expr expr' = eval expr == eval expr'

(Neg num, Integral num, Abs num) => Cast (Expr num) num where
  cast = eval

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add e e') = Add (map f e) (map f e')
  map f (Sub e e') = Sub (map f e) (map f e')
  map f (Mul e e') = Mul (map f e) (map f e')
  map f (Div e e') = Div (map f e) (map f e')
  map f (Absolut e) = Absolut (map f e)

Cast (Maybe elem) (List elem) where
  cast Nothing = []
  cast (Just x) = [x]

totalLen : List String -> Nat
totalLen xs = foldr (\str, len => length str + len) 0 xs


data Vector : Nat -> Type -> Type where
     Nil    : Vector Z a
     (::) : a -> Vector k a -> Vector (S k) a

%name Vector xs, ys, zs

Eq a => Eq (Vector n a) where
   (==) [] [] = True
   (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (Vector n) where
  foldr f acc [] = acc
  foldr f acc (x :: xs) = f x (foldr f acc xs)
