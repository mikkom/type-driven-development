module FirstClassTypes

import Data.Vect

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False val = trim val
valToString True val = cast val

valToString' : (isInt : Bool) -> (case isInt of
                                       False => String
                                       True => Int) -> String
valToString' False val = trim val
valToString' True val = cast val

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

Adder : Nat -> Type -> Type
Adder Z numType = numType
Adder (S k) numType = numType -> Adder k numType

adder : (Num t) => (numargs: Nat) -> t -> Adder numargs t
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

TupleVect : Nat -> Type -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1, 2, 3, 4, ())

data Format
  = Number Format
  | Str Format
  | Chr Format
  | Dbl Format
  | Lit String Format
  | End


toFormat : List Char -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number $ toFormat chars
toFormat ('%' :: 's' :: chars) = Str $ toFormat chars
toFormat ('%' :: 'c' :: chars) = Chr $ toFormat chars
toFormat ('%' :: 'f' :: chars) = Dbl $ toFormat chars
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt
-- toFormat chars = let (lit, rest) = span (/= '%') chars
--                  in Lit (pack lit) (toFormat rest)

PrintfType : Format -> Type
PrintfType (Number fmt) = Int -> PrintfType fmt
PrintfType (Str fmt) = String -> PrintfType fmt
PrintfType (Chr fmt) = Char -> PrintfType fmt
PrintfType (Dbl fmt) = Double -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc: String) -> PrintfType fmt
printfFmt (Number fmt) acc = \x => printfFmt fmt (acc ++ show x)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ singleton c)
printfFmt (Dbl fmt) acc = \x => printfFmt fmt (acc ++ show x)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)
printfFmt End acc = acc

printf : (fmt: String) -> PrintfType (toFormat $ unpack fmt)
printf fmt = printfFmt _ ""
