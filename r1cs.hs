{-# LANGUAGE GADTs, 
             TypeSynonymInstances, 
             FlexibleInstances #-}

import Data.Ratio
import qualified Data.Map.Strict as Map
import Control.Monad.State

----------------------------------------------------------------
--                Rank-1 Constraint Systems                   --
----------------------------------------------------------------

class (Show a,Eq a) => Field a where
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

-- the polynomial over 'nw' variables, equal 'x - y'
sub_poly :: Field a => Int -> Var -> Var -> Poly a
sub_poly nw x y
  | x < nw
  , y < nw  
  = let f z = if x == z then one else if y == z then neg one else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

data R1C a where
  R1C :: Field a => (Poly a, Poly a, Poly a) -> R1C a

instance Show a => Show (R1C a) where
  show (R1C (aV,bV,cV)) = show aV ++ "*" ++ show bV ++ "==" ++ show cV

data R1CS a where
  R1CS :: Field a => [R1C a] -> R1CS a

instance Show a => Show (R1CS a) where
  show (R1CS cs) = show cs

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

----------------------------------------------------------------
--            Intermediate Constraint Language                --
----------------------------------------------------------------

data Op = Add | Sub | Mult | Inv

instance Show Op where
  show Add  = "+"
  show Sub  = "-"
  show Mult = "*"
  show Inv  = "-*"      

invert_op :: Op -> Op
invert_op op = case op of
  Add -> Sub
  Sub -> Add
  Mult -> Inv
  Inv -> Mult

interp_op :: Field a => Op -> a -> a -> a
interp_op op = case op of
  Add -> add
  Sub -> \a1 a2 -> a1 `add` (neg a2)
  Mult -> mult
  Inv -> \a1 a2 -> if a2 == zero then zero else a1 `mult` (inv a2)

data Constraint a where
  CVal   :: Field a => (Var,a)  -> Constraint a -- x = c
  CVar   :: (Var,Var)           -> Constraint a -- x = y
  CBinop :: Op -> (Var,Var,Var) -> Constraint a -- x `op` y = z

instance Show a => Show (Constraint a) where
  show (CVal (x,c)) = show x ++ "==" ++ show c
  show (CVar (x,y)) = show x ++ "==" ++ show y
  show (CBinop op (x,y,z))
    = show x ++ show op ++ show y ++ "==" ++ show z    

type Assgn a = Map.Map Var a

solve_constraints :: Field a => [Constraint a] -- constraints to be solved
                  -> Assgn a -- initial assignment
                  -> Assgn a -- resulting assignment
solve_constraints cs env = g env cs
  where g env [] = env
        g env (CVal (x,c) : cs') = g (Map.insert x c env) cs'
        g env (CVar (x,y) : cs')
          = case (Map.lookup x env,Map.lookup y env) of
              (Nothing,Nothing) -> g env (cs' ++ [CVar (x,y)])
              (Just c,Nothing)  -> g (Map.insert y c env) cs'
              (Nothing,Just d)  -> g (Map.insert x d env) cs'
              (Just c,Just d)   ->
                if c == d then g env cs'
                else error "inconsistent assignment"
        g env (CBinop op (x,y,z) : cs')
          = let f_op  = interp_op op
                fn_op = interp_op (invert_op op)  
            in case (Map.lookup x env,Map.lookup y env,Map.lookup z env) of
              (Just c,Just d,Nothing) -> g (Map.insert z (c `f_op` d) env) cs'
              (Just c,Nothing,Just e) -> g (Map.insert y (e `fn_op` c) env) cs'
              (Nothing,Just d,Just e) -> g (Map.insert x (e `fn_op` d) env) cs'
              (Just c,Just d,Just e)  ->
                if e == c `f_op` d then g env cs'
                else error $ show c ++ " " ++ show op ++ " " ++ show d
                             ++ "==" ++ show e ++ ": inconsistent assignment"
              (_,_,_) -> g env (cs' ++ [CBinop op (x,y,z)])

r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw c = case c of
  CVal (x,c)    -> R1C (const_poly nw one,var_poly nw x,const_poly nw c)
  CVar (x,y)    -> R1C (const_poly nw one,var_poly nw x,var_poly nw y)
  CBinop Add  (x,y,z) -> R1C (const_poly nw one,add_poly nw x y,var_poly nw z)
  CBinop Sub  (x,y,z) -> R1C (const_poly nw one,sub_poly nw x y,var_poly nw z)  
  CBinop Mult (x,y,z) -> R1C (var_poly nw x,var_poly nw y,var_poly nw z)

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data Exp a where
  EVar   :: Var -> Exp a
  EVal   :: Field a => a -> Exp a
  EBinop :: Op -> Exp a -> Exp a -> Exp a
  EIf    :: Exp a -> Exp a -> Exp a -> Exp a
  ELet   :: Var -> Exp a -> Exp a -> Exp a
  --EApp  :: Var -> [Exp a] -> Exp a

max_var_of_exp :: Exp a -> Var
max_var_of_exp e = g (-1) e
  where g y e = case e of
          EVar x -> max x y
          EVal c -> y
          EBinop op e1 e2 -> max (g y e1) (g y e2)
          EIf b e1 e2 -> max (g y b) $ max (g y e1) (g y e2)
          ELet x e1 e2 -> max x $ max (g y e1) (g y e2)

fresh_var_of_exp :: Exp a -> Var
fresh_var_of_exp = (+1) . max_var_of_exp

data CEnv a =
  CEnv { cur_cs   :: [Constraint a]
       , next_var :: Var }

add_constraint :: Constraint a -> State (CEnv a) ()
add_constraint c = modify (\cenv -> cenv {cur_cs = c : cur_cs cenv})

get_constraints :: State (CEnv a) [Constraint a]
get_constraints
  = do { cenv <- get
       ; return (cur_cs cenv) }

get_next_var :: State (CEnv a) Var
get_next_var
  = do { cenv <- get
       ; return (next_var cenv) }

-- assumes variables are numbered sequentially 0..next_var-1
-- will be true if we canonicalize variable indices in source expression
get_num_vars :: State (CEnv a) Int
get_num_vars = get_next_var

set_next_var :: Var -> State (CEnv a) ()
set_next_var next = modify (\cenv -> cenv { next_var = next })

fresh_var :: State (CEnv a) Var
fresh_var
  = do { next <- get_next_var
       ; set_next_var (next + 1)
       ; return next }

-- add constraint 'x \/ y = c'
add_or_constraints :: Field a => (Var,Var,Var) -> State (CEnv a) ()
add_or_constraints (x,y,z)
  = do { x_mult_y <- fresh_var
       ; x_plus_y <- fresh_var
       ; add_constraint (CBinop Mult (x,y,x_mult_y))
       ; add_constraint (CBinop Add (x,y,x_plus_y))
       ; add_constraint (CBinop Sub (x_plus_y,z,x_mult_y)) }

-- add constraint 'b^2 = b'
ensure_boolean :: Field a => Var -> State (CEnv a) ()
ensure_boolean b
  = do { b_sq <- fresh_var
       ; add_constraint (CBinop Mult (b,b,b_sq))
       ; add_constraint (CVar (b_sq,b)) }

cs_of_exp :: Field a => Var -> Exp a -> State (CEnv a) ()
cs_of_exp out e = case e of
  EVar x ->
    do { add_constraint (CVar (out,x)) }
  EVal c ->
    do { add_constraint (CVal (out,c)) }
  EBinop op e1 e2 ->
    do { e1_out <- fresh_var
       ; e2_out <- fresh_var        
       ; cs_of_exp e1_out e1
       ; cs_of_exp e2_out e2
       ; add_constraint (CBinop op (e1_out,e2_out,out)) }
  EIf b e1 e2 ->
    do { b_out  <- fresh_var -- b
       ; bn_out <- fresh_var -- (1-b)
       ; e1_out <- fresh_var -- e1
       ; e2_out <- fresh_var -- e2
       ; b_e1   <- fresh_var -- b*e1
       ; bn_e2  <- fresh_var -- (1-b)*e2
         
       ; cs_of_exp b_out b
       ; cs_of_exp bn_out (EBinop Sub (EVal one) b)
       ; cs_of_exp e1_out e1
       ; cs_of_exp e2_out e2

       ; ensure_boolean b_out 
       ; add_constraint (CBinop Mult (b_out,e1_out,b_e1))
       ; add_constraint (CBinop Mult (bn_out,e2_out,bn_e2))
       ; add_or_constraints (b_e1,bn_e2,out) }
  ELet x e1 e2 ->
    do { cs_of_exp x e1
       ; cs_of_exp out e2 }  

r1cs_of_exp :: Field a => Var -> Exp a
            -> State (CEnv a) (Assgn a -> Assgn a,R1CS a)
r1cs_of_exp out e
  = do { cs_of_exp out e
       ; nv <- get_num_vars
       ; cs <- get_constraints
       ; let f = solve_constraints cs
       ; return $ (f,r1cs_of_cs nv cs) }

compile_exp :: Field a => Exp a -> ([a] -> [a],R1CS a)
compile_exp e
  = let out = fresh_var_of_exp e
        cenv_init = CEnv [] (out+1)
        ((f,r1cs),_) = runState (r1cs_of_exp out e) cenv_init
        g w = map snd $ Map.toList $ f $ Map.fromList (zip [0..] w)
    in (g,r1cs)

e1 :: Exp Rational
e1 = EBinop Add (EVal 3) (EVal 5)

e2 :: Exp Rational
e2 = EBinop Sub (EBinop Sub (EVal 3) (EBinop Add (EVal 5) (EVal 3)))
       (EBinop Mult (EVal 8) (EVal 8))

e3 :: Exp Rational
e3 = EBinop Sub (EVal 1) (EVar 0)

e4 :: Exp Rational
e4 = ELet 0 (EVal 1) (EVar 0)

e8 :: Exp Rational
e8 = EIf (EVar 0) (EVal 55) (EVal 77)  

  







