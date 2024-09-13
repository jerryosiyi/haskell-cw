-------------------------
-------- PART A --------- 
-------------------------
import Data.List

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
--  deriving Show

instance Show Term where
  show = pretty

example :: Term
example = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Apply (Variable "a") (Variable "c"))) (Variable "x")) (Variable "b")))

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m


------------------------- Assignment 1

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

------------------------- Assignment 2

variables :: [Var]
variables = map (:[]) ['a'..'z'] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

filterVariables :: [Var] -> [Var] -> [Var]
filterVariables xs []     = xs 
filterVariables xs (y:ys) = filter (/=y) (filterVariables xs ys)

fresh :: [Var] -> Var
fresh = head . filterVariables variables

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x n) = merge [x] (used n)
used (Apply  n m) = merge (used n) (used m)


------------------------- Assignment 3


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z n)
    | z == x    = Lambda z n
    | otherwise = Lambda z (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y m)
    | x == y    = Lambda y m
    | otherwise = Lambda z (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)

------------------------- Assignment 4

beta :: Term -> [Term]
beta (Apply (Lambda x n) m) =
  [substitute x m n] ++
  [Apply (Lambda x n') m  | n' <- beta n] ++
  [Apply (Lambda x n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x n) = [Lambda x n' | n' <- beta n]
beta (Variable _) = []


normalize :: Term -> Term
normalize n
  | null ns   = n
  | otherwise = normalize (head ns) 
  where ns = beta n

run :: Term -> IO ()
run n = do
  print n
  let ns = beta n
  if null ns then
    return ()
  else
    run (head ns)

 
-------------------------

suc    = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Apply (Variable "n") (Variable "f")) (Variable "x")))))
add    = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Variable "f")) (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))))))
mul    = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Apply (Variable "n") (Variable "f"))) (Variable "x")))))
dec    = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Apply (Variable "n") (Lambda "g" (Lambda "h" (Apply (Variable "h") (Apply (Variable "g") (Variable "f")))))) (Lambda "u" (Variable "x"))) (Lambda "x" (Variable "x")))))
minus  = Lambda "n" (Lambda "m" (Apply (Apply (Variable "m") dec) (Variable "n")))
-------------------------
-------- PART B --------- 
-------------------------

------------------------- Assignment 5

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = delete x (free n)
free (Apply  n m) = merge (free n) (free m) 

abstractions :: Term -> [Var] -> Term
abstractions n [] = n
abstractions n (x:xs) = Lambda x (abstractions n (xs))

applications :: Term -> [Term] -> Term
applications n [] = n
applications n (x:xs) = Apply (application n (ys)) y
    where 
        y:ys = reverse (x:xs)

application :: Term -> [Term] -> Term
application n [] = n      
application n (x:xs) = Apply (application n (xs)) x

lift :: Term -> Term
lift n = applications y (xv)
    where
        x = free(n)
        xv = conVartoTerm(x)
        y = abstractions n (x)

conVartoTerm :: [Var] -> [Term]
conVartoTerm [] = []
conVartoTerm (x:xs) = Variable x : conVartoTerm(xs)

super :: Term -> Term
super (Variable x) = (Variable x)
super (Lambda x n) = lift (Lambda x (superAux (n)))
super (Apply  n m) = Apply(super n) (super m)

superAux :: Term -> Term
superAux (Variable x) = super (Variable x)
superAux (Lambda x n) = Lambda x (superAux n)
superAux (Apply  n m) = super (Apply  n m)


------------------------- Assignment 6

data Expr =
    V   Var
  | A   Expr Expr


toTerm :: Expr -> Term
toTerm (V x) = Variable x
toTerm (A n m) = Apply (toTerm (n)) (toTerm(m))


instance Show Expr where
  show = show . toTerm

type Inst = (Var,[Var],Expr)

data Prog = Prog [Inst]


instance Show Prog where
  show (Prog ls) = unlines (map showInst ks)
    where
      ks = map showParts ls
      n  = maximum (map (length . fst) ks)
      showParts (x,xs,e) = (x ++ " " ++ unwords xs , show e)
      showInst (s,t) = take n (s ++ repeat ' ') ++ " = " ++ t


names = ['$':show i | i <- [1..] ]

-------------------------

stripAbs :: Term -> ([Var],Term)
stripAbs (Variable x) = ([],Variable x)
stripAbs (Lambda x n) = ([x] ++ (y), z)
    where
        y = fst (stripAbs(n))
        z = snd (stripAbs(n))
stripAbs (Apply  n m) = ([],Apply n m)

takeAbs :: Term -> [Term]
takeAbs (Variable x) = []
takeAbs (Lambda x n) = [Lambda x n]
takeAbs (Apply  n m) = x ++ y
    where
        x = takeAbs n
        y = takeAbs m

toExpr :: [Var] -> Term -> Expr
toExpr (y:ys) (Variable x) = snd (toExprAux(y:ys) (Variable x))
toExpr (y:ys) (Lambda x n) = snd (toExprAux(y:ys) (Lambda x n))
toExpr (y:ys) (Apply  n m) = snd (toExprAux(y:ys) (Apply  n m))

toExprAux :: [Var] -> Term -> ([Var],Expr)
toExprAux (y:ys) (Variable x) = ((y:ys),V x)
toExprAux (y:ys) (Lambda x n) = ((ys),V y)
toExprAux (y:ys) (Apply  n m) = (fst (b), A (snd (a))(snd (b)))
    where
        a = toExprAux (y:ys) n
        b = toExprAux (fst (a)) m
toExprAux [] (Variable x) = ([],V x)
toExprAux [] (Lambda x n) = error "no fresh variables"
toExprAux [] (Apply  n m) = (fst (b), A (snd (a))(snd (b)))
    where
        a = toExprAux [] n
        b = toExprAux (fst (a)) m
                
toInst :: [Var] -> (Var,Term) -> (Inst,[(Var,Term)],[Var])
toInst (f:fs) ((inst,n)) = (i,p, r)
    where
        (abs,m) = stripAbs (n)
        (r,e) = toExprAux(f:fs)(m)
        i = (inst, abs, e)
        p = pairAbsVar(f:fs) (takeAbs(m))
        
pairAbsVar :: [Var] -> [Term] -> [(Var,Term)]
pairAbsVar (y:ys) (x:xs) = [(y,x)] ++ pairAbsVar(ys)(xs)
pairAbsVar _ [] = []
pairAbsVar [] _ = []
        
prog :: Term -> Prog
prog n = Prog (aux names [("$main",super(n))])
  where
    aux :: [Var] -> [(Var,Term)] -> [Inst]
    aux (x:xs) (y:ys)= [a] ++ aux(c)(ys ++ b)
        where
            (a,b,c) = toInst(x:xs)(y)
    aux _ [] = []
    aux [] _ = []
example2 = Apply (Variable "S") (Apply (Apply example (numeral 0)) (Variable "0"))
example3 = Apply (Apply add (numeral 1)) (Apply (Apply mul (numeral 2)) (numeral 3))
example4 = Apply (Apply example3 (Variable "S")) (Variable "0")

------------------------- Assignment 7

sub :: [(Var,Expr)] -> Expr -> Expr
sub (y:ys) (V x)
    |x == fst y  = snd y
    |otherwise   = sub(ys) (V x)
sub (y:ys) (A n m) = A (sub (y:ys) n) (sub (y:ys) m)
sub [] e = e

findInst :: Var -> [Inst] -> (Inst, Int)
findInst e ((a,b,c):xs) = do
    if a == e
    then ((a,b,c), 0)
    else findInst e xs
findInst e [] = (("error",[], (V "error")), 1)
    
getPairs :: [Var] -> [Expr] -> ([(Var,Expr)],[Expr])
getPairs (y:ys) [] = error "step: insufficient arguments on stack"
getPairs [] x = ([], x)
getPairs (y:ys) (x:xs) = ([(y,x)] ++ fst(a),snd (a))
    where
        a = getPairs(ys)(xs)
    
step :: [Inst] -> [Expr] -> IO [Expr]
step inst [] = do
    return []
step inst ((V x):xs) = do
    let ((_,vars,expr), error) = findInst x inst
    if error == 0 
    then do
        let (pairs, stack) = getPairs (vars) (xs)
        let newExpr = sub (pairs) expr
        return ([newExpr] ++ stack)
    else do
        putStr (x ++ " ")
        return xs           
        
step inst ((A n m):ys) = do
    return (n:(m:ys))
        
supernormalize :: Term -> IO ()
supernormalize n = do
    let Prog p = prog n
    process p [V "$main"]
    putStr "\n"
    return ()
    where
        process :: [Inst] -> [Expr] -> IO [Expr]
        process p [] = do
            return []
        process p (x:xs) = do 
            a <- step p (x:xs)
            process p a
            return a
    