import Data.Vect

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Vect 3 Position
tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False str = trim str
valToString True n = cast n

valToStringg : (isInt : Bool) -> (case isInt of
                                       False => String
                                       True => Int) -> String
valToStringg False str = trim str
valToStringg True n = cast n

AdderType : (argCount : Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next : numType) -> AdderType k numType

adder : Num numType => (argCount : Nat) -> (acc: numType) -> AdderType argCount numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

data Format = Number Format
            | Str Format
            | Ch Format
            | Flt Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType End = String
PrintfType (Number fmt) = Int -> PrintfType fmt
PrintfType (Str fmt) = String -> PrintfType fmt
PrintfType (Ch fmt) = Char -> PrintfType fmt
PrintfType (Flt fmt) = Double -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt End acc = acc
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Ch fmt) acc = \c => printfFmt fmt (acc ++ cast c)
printfFmt (Flt fmt) acc = \f => printfFmt fmt (acc ++ show f)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Ch (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Flt (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

Matrix : Nat -> Nat -> Type
Matrix m n = Vect m (Vect n Double)

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

TupleVect : Nat -> Type -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1,2,3,4,())

