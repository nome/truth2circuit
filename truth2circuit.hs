import Data.List
import Debug.Trace

data BoolExpr = Var Int | Const Bool | Not BoolExpr | And [BoolExpr] | Or [BoolExpr] deriving (Eq, Ord)

instance Show BoolExpr where
	show (Var i) = [ ['a'..] !! i ]
	show (Const b) = show b
	show (Not e) = "/" ++ show e ++ "\\"
	show (And es) = concat (map show (sort es))
	show (Or es)  = "(" ++ concat (intersperse " + " (map show (sort es))) ++ ")"

{-
 - Check whether we're certain that truth of one expression implies truth of another
 - Might produce some false negatives; an "implies" (=>) in the strict mathematical
 - sense would be a BoolExpr anyway
 -}
implies :: BoolExpr -> BoolExpr -> Bool
(Const x) `implies` (Const y) = x == y
(And xs)  `implies` (And ys)  = all (`elem` xs) ys
(And xs)  `implies` y         = y `elem` xs
(Or xs)   `implies` (Or ys)   = all (`elem` ys) xs
x         `implies` (Or ys)   = x `elem` ys
x         `implies` y         = x == y

{-
 - Apply various identities in order to simplify a boolean expression
 -}
simplify :: BoolExpr -> BoolExpr

simplify (Var i) = Var i
simplify (Const b) = Const b
simplify (Not (Const b)) = Const (not b)
simplify (Not e) = Not (simplify e)

simplify (And (x:xs)) = simplifyAnd [] (simplify x) (map simplify xs) where
	simplifyAnd :: [BoolExpr] -> BoolExpr -> [BoolExpr] -> BoolExpr
	--simplifyAnd done current rest | trace ("simplifyAnd " ++ show done ++ " | " ++ show current ++ " | " ++ show rest) False = undefined
	--simplifyAnd done _ _ | length done > 3 = undefined
	simplifyAnd [] x [] = x
	simplifyAnd done (Const True) (r:rest) = simplifyAnd done r rest
	simplifyAnd (d:done) (Const True) [] = simplifyAnd done d []
	simplifyAnd _ (Const False) _ = Const False
	simplifyAnd done (And (x:xs)) rest = simplifyAnd done x (xs ++ rest)
	simplifyAnd done current [] = And (current:done)
	simplifyAnd done current rest = case simplifyAndWith current [] rest of
														Const False -> Const False
														And (x:xs) -> simplifyAnd (current:done) x xs
														And [] -> And (current:done)
	simplifyAndWith :: BoolExpr -> [BoolExpr] -> [BoolExpr] -> BoolExpr
	--simplifyAndWith current acc rest | trace ("simplifyAndWith " ++ show current ++ " | " ++ show acc ++ " | " ++ show rest) False = undefined
	simplifyAndWith _ acc []       = And acc
	simplifyAndWith x acc (y:ys)
		| x `implies` y             = simplifyAndWith x acc ys
		| y `implies` x             = simplifyAndWith y acc ys
		| x == Not y || Not x == y  = Const False
		| otherwise                 = simplifyAndWith x (y:acc) ys

simplify (Or (x:xs)) = simplifyOr [] (simplify x) (map simplify xs) where
	simplifyOr :: [BoolExpr] -> BoolExpr -> [BoolExpr] -> BoolExpr
	simplifyOr [] x [] = x
	simplifyOr done (Const False) (r:rest) = simplifyOr done r rest
	simplifyOr (d:done) (Const False) [] = simplifyOr done d []
	simplifyOr _ (Const True) _ = Const True
	simplifyOr done (Or (x:xs)) rest = simplifyOr done x (xs ++ rest)
	simplifyOr done current [] = Or (current:done)
	simplifyOr done current rest = case simplifyOrWith current [] rest of
														Const True -> Const True
														Or (x:xs) -> simplifyOr (current:done) x xs
														Or [] -> Or (current:done)
	simplifyOrWith :: BoolExpr -> [BoolExpr] -> [BoolExpr] -> BoolExpr
	simplifyOrWith x acc (y:ys)
		| x `implies` y             = simplifyOrWith x acc ys
		| y `implies` x             = simplifyOrWith y acc ys
		| x == Not y || Not x == y  = Const True
		| otherwise                 = simplifyOrWith x (y:acc) ys
	simplifyOrWith _ acc []        = Or acc

{-
 - Make sum of products representation by multiplying out all "Or"'s
 -}
sop :: BoolExpr -> BoolExpr
sop (And s) = case break isOr s of
						(_,[]) -> And s
						(s1,(Or m):s2) -> Or $ map (sop.And.(s1++).(:s2)) m
				  where
				  isOr (Or _) = True
				  isOr _ = False
sop x = x

{-
 - Given the values of all variables, compute the truth value of the expression
 -}
applyExpr :: BoolExpr -> [Bool] -> Bool
applyExpr (Var i) ins = ins !! i
applyExpr (Const b) _ = b
applyExpr (Not e) ins = not $ applyExpr e ins
applyExpr (And xs) ins = and $ map (\e -> applyExpr e ins) xs
applyExpr (Or xs) ins = or $ map (\e -> applyExpr e ins) xs

{-
 - Helper function: count number of list elements for which predicate is True
 -}
count :: Enum b => (a -> Bool) -> [a] -> b
count pred = foldl (\c e -> if pred e then succ c else c) (toEnum 0)


{-
 - Some stuff for working with truth tables
 -}
type TruthTable = [([Bool], Bool)]

{-
 - Converting between truth tables and boolean expressions
 -}

exprFromTable :: TruthTable -> BoolExpr
exprFromTable tt = if count id (map snd tt) > (length tt) `div` 2 then productOfSums tt else sumOfProducts tt where
	productOfSums tt = And [ Or [ if ival then Not (Var inum) else Var inum | (ival, inum) <- zip ins [0..] ] | (ins, out) <- tt, not out ]
	sumOfProducts tt = Or [ And [ if ival then Var inum else Not (Var inum) | (ival, inum) <- zip ins [0..] ] | (ins, out) <- tt, out ]

tableFromExpr :: BoolExpr -> TruthTable
tableFromExpr e = map (\ins -> (ins, applyExpr e ins)) (permutations [False,True] (numVariables e)) where
	permutations :: [a] -> Int -> [[a]]
	permutations list num = sequence $ replicate num list
	numVariables = numVariables' 0
	numVariables' :: Int -> BoolExpr -> Int
	numVariables' acc (Var i) = if i >= acc then i+1 else acc
	numVariables' acc (Const _) = 0
	numVariables' acc (Not e) = numVariables' acc e
	numVariables' acc (And es) = maximum $ map (numVariables' acc) es
	numVariables' acc (Or es)  = maximum $ map (numVariables' acc) es

{-
 - Converting between internal and string representations of truth tables
 -}

parseTruthTable :: String -> TruthTable
parseTruthTable = map (splitLast . map (=='1') . filter (`elem` "01")) . lines where
	splitLast l = (uncurry $ (.head) . (,)) $ splitAt (length l - 1) l

showTruthTable :: TruthTable -> String
showTruthTable = unlines . (map $ unwords . (map (\b -> if b then "1" else "0")) . (\(i,o) -> i++[o]))

{-
 -}

testExpr :: BoolExpr -> TruthTable -> String
testExpr e tt = unlines $ map testLine tt where
	testLine (ins, out) = unwords $ map showBit $ ins ++ [out, applyExpr e ins]
	showBit b = if b then "1" else "0"


