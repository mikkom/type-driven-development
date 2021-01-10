import Data.Vect

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (row :: rows) = let tmat = transposeMat rows in
                                        zipWith (::) row tmat

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (r1 :: rs1) (r2 :: rs2) = zipWith (+) r1 r2 :: addMatrix rs1 rs2

createRow : Num a => Vect m a -> Vect p (Vect m a) -> Vect p a
createRow r [] = []
createRow r (c :: cs) = sum (zipWith (*) r c) :: createRow r cs

multHelper : Num a => Vect n (Vect m a) -> Vect p (Vect m a) -> Vect n (Vect p a)
multHelper [] _ = []
multHelper (r :: rs) cs = createRow r cs :: multHelper rs cs

multMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix m1 m2 = multHelper m1 (transposeMat m2)
