module RealsLib where

import Data.Ratio

{- core -}

{- types -}

type Q = Rational

type C a = Q -> a

type R = C Q

type UCF a b = (a -> b, Q -> Q)



{- constants -}

standartEps :: Q
standartEps = (1 % 1000)



{- core functions -}

unitC :: a -> C a
unitC = const

mapC :: UCF a b -> C a -> C b
mapC f x = fst f . x . snd f

joinC :: C (C a) -> C a
joinC x eps = x (eps / 2) (eps / 2)

bindC :: UCF a (C b) -> (C a -> C b)
bindC f = joinC . mapC f

apC :: C (UCF a b) -> C a -> C b
apC f x eps = mapC (f (eps / 2)) x (eps / 2)

map2C :: (UCF a (UCF b c)) -> (C a -> C b -> C c)
map2C f = apC . mapC f



{- basic arithmetic library -}

{- double -}

double :: UCF Q Q
double = ((2 *), (/ 2))

doubleR :: R -> R
doubleR = mapC double

eDouble :: Q -> R
eDouble x eps = doubleR (unitC x) eps

sDouble :: Q -> Double
sDouble x = fromRational (eDouble x standartEps)


{- addition -}

{- definition 11.4 - page 96 -}
add :: UCF Q (UCF Q Q)
add = (\x -> (\y -> x + y, id), id) 

addR :: R -> R -> R
addR = map2C add

eAdd :: Q -> Q -> R
eAdd x y eps = addR (unitC x) (unitC y) eps 

sAdd :: Q -> Q -> Double
sAdd x y = fromRational (eAdd x y standartEps)


{- subtraction -}

sub :: UCF Q (UCF Q Q)
sub = (\x -> (\y -> x - y, id), id) 

subR :: R -> R -> R
subR = map2C sub

eSub :: Q -> Q -> R
eSub x y eps = subR (unitC x) (unitC y) eps 

sSub :: Q -> Q -> Double
sSub x y = fromRational (eSub x y standartEps)


{- multiplication -}

bound :: (Ord a, Num a) => a -> a -> a
bound c x = min (max x (negate c)) c 

mul :: Q -> UCF Q (UCF Q Q)
mul c = (\a -> (\b -> a * bound c b, (/ a)), (/ c))

mulR :: R -> R -> R
mulR x y = map2C (mul c) x y
  where c = abs (y 1) + 1

eMul :: Q -> Q -> R
eMul x y eps = mulR (unitC x) (unitC y) eps

sMul :: Q -> Q -> Double
sMul x y = fromRational (eMul x y standartEps)


{- reciprocal number -}

reciprPositive :: Q -> UCF Q Q
reciprPositive a = (\x -> 1 / max x a, \eps -> eps * a * a)

reciprNegative :: Q -> UCF Q Q
reciprNegative a = (\x -> 1 / min x a, \eps -> eps * a * a)

reciprRPositive :: Q -> R -> R
reciprRPositive a = mapC (reciprPositive a)

reciprRNegative :: Q -> R -> R
reciprRNegative a = mapC (reciprNegative a)

eRecipr :: Q -> R
eRecipr x
  | x > 0 = reciprRPositive x (unitC x)
  | x < 0 = reciprRNegative x (unitC x)
  | otherwise = error "No reciprocal for zero"

sRecipr :: Q -> Double
sRecipr x = fromRational (eRecipr x standartEps) 


{- division -}

divRPositive :: R -> R -> Q -> R
divRPositive x y a = mulR x (reciprRPositive a y)   

divRNegative :: R -> R -> Q -> R
divRNegative x y a = mulR x (reciprRNegative a y) 

eDiv :: Q -> Q -> R
eDiv x y
  | y > 0 = divRPositive (unitC x) (unitC y) y
  | y < 0 = divRNegative (unitC x) (unitC y) y
  | otherwise = error "Division by zero"

sDiv :: Q -> Q -> Double
sDiv x y = fromRational (eDiv x y standartEps) 


{- exponent -}

expDef :: Q -> Integer -> Q -> Q -> Q -> Q
expDef a i xi s eps
   | stop xi   = newSum 
   | otherwise = expDef a (i + 1) nextMember newSum eps
   where stop x = (abs x) < eps
         nextMember = xi * a * (1 % (i + 1))
         newSum = s + xi

expNegativeBound :: Integer -> UCF Q R
expNegativeBound a = (\b eps -> expDef (min b (a % 1)) 0 1 0 eps, \eps -> eps * 2^a)

expPositiveBound :: Integer -> UCF Q R
expPositiveBound a = (\b eps -> expDef (min b (a % 1)) 0 1 0 eps, \eps -> eps * 3^a)

expR :: R -> R
expR x
  | c <= 0    = bindC (expNegativeBound c) x
  | otherwise = bindC (expPositiveBound c) x
  where c = ceiling (x 1 + 1)

eExp :: Q -> Q -> Q
eExp x eps = expR (unitC x) eps

sExp :: Q -> Double
sExp x = fromRational (eExp x standartEps)


{- square root -}

sqrtApproxs :: Q -> [Q]
sqrtApproxs a = iterate (\b -> (a / b + b) / 2) ((a + 1) / 2)

sqrtErrors :: [Q]
sqrtErrors = iterate (\a -> a * a) (1 / 2)

sqrtQ :: Q -> Q -> Q
sqrtQ a eps 
  | 0 < a  && a < 1 = (next (sqrtApproxs (fst args1)) sqrtErrors) / (snd args1)
  | 1 <= a && a < 4 = next (sqrtApproxs a) sqrtErrors
  | a >=4           = (next (sqrtApproxs (fst args2)) sqrtErrors) / (snd args2)
  | otherwise       = error "Square root for negative real is not defined"
  where next (x : xs) (e : es)
          | e < eps   = x
          | otherwise = next xs es
        args1 = (bounds a 1 (\a m -> 4^m * a) (\m -> 2^m))
        args2 = (bounds a 1 (\a m -> (1 / 4^m) * a) (\m -> (1 / 2^m)))
        bounds a m f1 f2 
          | (f1 a m) >= 1 && (f1 a m) < 4 = (f1 a m, f2 m) 
          | otherwise = bounds a (m + 1) f1 f2

sqrtR ::  R -> R
sqrtR = bindC (sqrtQ, \eps -> eps * eps) 

eSqrt :: Q -> Q -> Q
eSqrt 0 _ = 0
eSqrt x eps = sqrtR (unitC x) eps

sSqrt :: Q -> Double
sSqrt x = fromRational (eSqrt x standartEps)



{- example of using the library -}

{- integral of exponent from 0 to x -}

integralSum :: (R -> R) -> Integer -> Integer -> R -> R -> R -> R
integralSum f n i x dx s 
  | i == n    = s
  | otherwise = integralSum (f) n (i + 1) (addR x dx) dx (addR s (mulR (f x) dx))

eIntegralExp :: Q -> Integer -> R
eIntegralExp x n = integralSum (expR) n 0 (unitC 0) (mulR (unitC x) (unitC (1 % n))) (unitC 0)

sIntegralExp :: Q -> Double
sIntegralExp x = fromRational (eIntegralExp x parts standartEps)
  where parts = 1000