module RecursiveViews

data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : (snoc : SnocList input) -> (rest : List a) ->
               SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) =
  rewrite appendAssociative input [x] xs in
          snocListHelp (Snoc snoc {x}) xs

total
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

myReverse : (input : List a) -> List a
myReverse input with (snocList input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (Snoc rec) = x :: myReverse xs | rec

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | Empty = True
  isSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      if x == y then isSuffix xs ys | xsrec | ysrec else False
