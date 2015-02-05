{-# LANGUAGE GADTs, 
             TypeSynonymInstances, 
             FlexibleInstances #-}

import Data.Ratio
import qualified Data.Map as Map
import Control.Monad.State

class Eq a => Field a where
  zero :: a
  one  :: a
  add  :: a -> a -> a
  mult :: a -> a -> a
  neg  :: a -> a
  inv  :: a -> a

instance Field Rational where 
  zero = 0
  one  = 1
  add  = (+)
  mult = (*)
  neg  = \n -> -n
  inv  = \n -> denominator n % numerator n

data Poly a where
  Poly :: Field a => [a] -> Poly a

instance Show a => Show (Poly a) where
  show (Poly l) = show l

type Var = Int

-- the constant polynomial over 'nw' variables, equal 'c'
const_poly :: Field a => Int -> a -> Poly a
const_poly nw c = Poly $ c : take nw (repeat zero)

-- the polynomial over 'nw' variables, equal variable 'x'
var_poly :: Field a => Int -> Var -> Poly a
var_poly nw x
  | x < nw
  = let f y = if x == y then one else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

-- the polynomial over 'nw' variables, equal 'x + y'
add_poly :: Field a => Int -> Var -> Var -> Poly a
add_poly nw x y
  | x < nw
  , y < nw  
  = let f z = if x == z || y == z then one else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

data R1C a where
  R1C :: Field a => (Poly a, Poly a, Poly a) -> R1C a

data R1CS a where
  R1CS :: Field a => [R1C a] -> R1CS a

-- sat_r1c: Does witness 'w' satisfy constraint 'c'?
sat_r1c :: Field a => [a] -> R1C a -> Bool
sat_r1c w c
  | R1C (aV, bV, cV) <- c
  = inner aV w `mult` inner bV w == inner cV w
    where inner :: Field a => Poly a -> [a] -> a
          inner p w
            | Poly v <- p
            , length v == 1 + length w
            = foldl add zero $ map (uncurry mult) (zip v (one : w))

            | otherwise
            = error "witness has wrong length"

-- sat_r1cs: Does witness 'w' satisfy constraint set 'cs'?
sat_r1cs :: Field a => [a] -> R1CS a -> Bool
sat_r1cs w cs
  | R1CS cs' <- cs
  = all (sat_r1c w) cs'                 

-- x * y = z
cA :: R1CS Rational
cA = R1CS [R1C (Poly [0,1,0,0],Poly [0,0,1,0],Poly [0,0,0,1])]

cA_wit :: [Rational]
cA_wit = [1,2,2]

-- x + y = z
dA :: R1CS Rational
dA = R1CS [R1C (Poly [1,0,0,0],Poly [0,1,1,0],Poly [0,0,0,1])]

dA_wit :: [Rational]
dA_wit = [1,2,3]

data Constraint a where
  CEq   :: Field a => (Var,a) -> Constraint a -- x = c
  CVar  :: (Var,Var) -> Constraint a    -- x = y
  CAdd  :: (Var,Var,Var) -> Constraint a -- x+y = z
  CMult :: (Var,Var,Var) -> Constraint a -- x*y = z

r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw c = case c of
  CEq (x,c)     -> R1C (const_poly nw one,var_poly nw x,const_poly nw c)
  CVar (x,y)    -> R1C (const_poly nw one,var_poly nw x,var_poly nw y)
  CAdd (x,y,z)  -> R1C (const_poly nw one,add_poly nw x y,var_poly nw z)
  CMult (x,y,z) -> R1C (var_poly nw x,var_poly nw y,var_poly nw z)

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs

data Exp a where
  EVar  :: Var -> Exp a
  EVal  :: Field a => a -> Exp a
  EAdd  :: Exp a -> Exp a -> Exp a
  EMult :: Exp a -> Exp a -> Exp a
  ELet  :: Var -> Exp a -> Exp a
  --EApp  :: Var -> [Exp a] -> Exp a

cs_of_exp :: Field a => Var -> Exp a -> [Constraint a]
cs_of_exp out e = case e of
  EVar x -> [CVar (out,x)]
  -- EVal c -> do { x <- fresh
  --              ; add_constraint (CEq (x,c))
  --              ; add_constraint (CVar (out,x)) }

      

  

  







