module Main

average : (str: String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum $ allLengths (words str) in
                  cast totalLength / cast numWords
  where
    wordCount : String -> Nat
    wordCount str = length $ words str

    allLengths : List String -> List Nat
    allLengths strs = map length strs

showAverage : String -> String
showAverage str = "The average word length is: " ++
                  (show $ average str) ++ "\n"

palindrome : String -> Bool
palindrome str = let lstr = toLower str in
                     reverse lstr == lstr

top_ten : Ord a => List a -> List a
top_ten xs = take 10 $ reverse $ sort xs

allLengths : List String -> List Nat
allLengths [] = [] 
allLengths (word :: words) = length word :: allLengths words

{-
isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not $ isEven k
-}

mutual
  isEven : Nat -> Bool
  isEven Z = True
  isEven (S k) = isOdd k

  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S k) = isEven k


main : IO ()
main = repl "Enter a string: " showAverage
