module BuiltinViews

import Data.Vect
import Data.Vect.Views
import Data.List.Views
import Data.Nat.Views

total
mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) =
    merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

total
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      if x == y then (equalSuffix xs ys | xsrec | ysrec) ++ [x] else []

total
vectorMergeSort : Ord a => Vect n a -> Vect n a
vectorMergeSort xs with (splitRec xs)
  vectorMergeSort [] | SplitRecNil = []
  vectorMergeSort [x] | SplitRecOne = [x]
  vectorMergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) =
    merge (vectorMergeSort lefts | lrec) (vectorMergeSort rights | rrec)

total
toBinary : Nat -> String
toBinary n with (halfRec n)
  toBinary Z | HalfRecZ = ""
  toBinary (x + x) | (HalfRecEven rec) = toBinary x | rec ++ "0"
  toBinary (S (x + x)) | (HalfRecOdd rec) = toBinary x | rec ++ "1"

total
palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) =
    x == y && palindrome ys | rec
