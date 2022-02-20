module Views

data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          NonEmpty ys y => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd input with (listLast input)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (xs ++ [x]) | (NonEmpty xs x) =
    "Non-empty, initial portion = " ++ show xs

myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) ->
                 SplitList (lefts ++ rights)

-- total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (item :: items) =
      case splitListHelp counter items of
           SplitNil => SplitOne
           SplitOne {x} => SplitPair [item] [x]
           (SplitPair lefts rights) => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) =
    merge (mergeSort lefts) (mergeSort rights)

data TakeN : List a -> Type where
     Fewer : TakeN xs
     Exact : (taken : List a) -> TakeN (taken ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) =
  case takeN k xs of
       Fewer => Fewer
       Exact taken => Exact (x :: taken)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (taken ++ rest) | (Exact taken) =
    taken :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = ([], xs)
  halves (taken ++ rest) | (Exact taken) = (taken, rest)
