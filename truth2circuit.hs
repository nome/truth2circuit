module Main where

import Data.List
import Data.Maybe

{-
 - basic data type representing boolean expressions
 -}

data BoolExpr = Var Int | Const Bool | Not BoolExpr | And [BoolExpr] | Or [BoolExpr] deriving (Eq, Ord)

instance Show BoolExpr where
	show (Var i) = [ ['a'..] !! i ]
	show (Const b) = show b
	show (Not e) = "/" ++ show e ++ "\\"
	show (And es) = concat (map show (sort es))
	show (Or es)  = "(" ++ concat (intersperse " + " (map show (sort es))) ++ ")"


{-
 - code common to simplification of And and Or expressions
 -}
type BinaryBoolRules = BoolExpr -> BoolExpr -> Maybe BoolExpr
applyBinaryRules ::  BinaryBoolRules -> ([BoolExpr] -> BoolExpr) -> (BoolExpr -> Maybe [BoolExpr]) -> [BoolExpr] -> BoolExpr
applyBinaryRules rules boxer unboxer input = applyBinaryRules' [] (head input) (tail input) where
	applyBinaryRules' :: [BoolExpr] -> BoolExpr -> [BoolExpr] -> BoolExpr
	-- unboxing
	applyBinaryRules' [] x [] = x
	-- splicing
	applyBinaryRules' done current rest | isJust unboxed = applyBinaryRules' [] (head new) (tail new) where
		unboxed = unboxer current
		new = done ++ (fromJust unboxed) ++ rest
	-- we finished applying rules to the list
	applyBinaryRules' done current [] = boxer (current:done)
	-- apply the binary rules
	applyBinaryRules' done current rest = case applyRulesFor current [] rest of
															Just replacement -> let new = done ++ replacement in
																						   applyBinaryRules' [] (head new) (tail new)
															Nothing -> applyBinaryRules' (current:done) (head rest) (tail rest)
	applyRulesFor _ _ [] = Nothing
	applyRulesFor x done (r:rest) = case rules x r of
													Just replacement -> Just $ done ++ replacement:rest
													Nothing -> case rules r x of
																		Just replacement -> Just $ done ++ replacement:rest
																		Nothing -> applyRulesFor x (r:done) rest

{-
 - Check whether we're certain that truth of one expression implies truth of another
 - Might produce some false negatives; an "implies" (=>) in the strict mathematical
 - sense would be a BoolExpr anyway
 -}
implies :: BoolExpr -> BoolExpr -> Bool
(Const x) `implies` (Const y) = y || not x
(And xs)  `implies` (And ys)  = all (`elem` xs) ys
(And xs)  `implies` y         = y `elem` xs
(Or xs)   `implies` (Or ys)   = all (`elem` ys) xs
x         `implies` (Or ys)   = x `elem` ys
x         `implies` y         = x == y

{-
 - Apply various identities in order to simplify a boolean expression
 -
 - Finding an expression corresponding to a truth table is easy (see below); the
 - hard part is finding a _simple_ expression with that property.
 -}
simplify :: BoolExpr -> BoolExpr

-- basic identities
simplify (Var i) = Var i
simplify (Const b) = Const b
simplify (Not (Const b)) = Const (not b)
simplify (Not e) = Not (simplify e)

-- rules for AND expressions
simplify (And xs) = applyBinaryRules binarySimplifyAnd And unboxAnd (map simplify xs) where
	unboxAnd (And content) = Just content
	unboxAnd _ = Nothing

	binarySimplifyAnd :: BinaryBoolRules
	binarySimplifyAnd x y | x `implies` y = Just $ x
	binarySimplifyAnd (Const True) x      = Just $ x
	binarySimplifyAnd (Const False) _     = Just $ Const False
	binarySimplifyAnd x (Not y) | x == y  = Just $ Const False
	binarySimplifyAnd _ _                 = Nothing

-- rules for OR expressions
simplify (Or xs) = applyBinaryRules binarySimplifyOr Or unboxOr (map simplify xs) where
	unboxOr (Or content) = Just content
	unboxOr _ = Nothing

	binarySimplifyOr :: BinaryBoolRules
	binarySimplifyOr x y | x `implies` y = Just $ y
	binarySimplifyOr (Const True) _      = Just $ Const True
	binarySimplifyOr (Const False) x     = Just $ x
	binarySimplifyOr x (Not y) | x == y  = Just $ Const True
	binarySimplifyOr x (And ys) | Not x `elem` ys = Just $ Or [x, And $ filter (/= Not x) ys]
	binarySimplifyOr (Not x) (And ys) | x `elem` ys = Just $ Or [Not x, And $ filter (/= x) ys]
	-- try factoring out common terms and simplifying the rest
	binarySimplifyOr (And xs) (And ys) | isSane && isJust partsimp = Just $ sumOfProducts $ And $ (fromJust partsimp):common where
		common = intersect xs ys
		(xs', ys') = (xs \\ common, ys \\ common)
		isSane = not $ null common || null xs' || null ys'
		partsimp = binarySimplifyOr (simplify (And xs')) (simplify (And ys'))
	binarySimplifyOr _ _                 = Nothing


{-
 - Make sum of products representation by multiplying out all ORs
 -}
sumOfProducts :: BoolExpr -> BoolExpr
sumOfProducts (And xs) = case break isOr xs of
									(_,[]) -> And xs
									(s1,(Or m):s2) -> Or $ map (sumOfProducts.And.(s1++).(:s2)) m
	where
		isOr (Or _) = True
		isOr _      = False
sumOfProducts xs = xs

{-
 - Given the values of all variables, compute the truth value of the expression
 -}
applyExpr :: BoolExpr -> [Bool] -> Bool
applyExpr (Var i) ins  = ins !! i
applyExpr (Const b) _  = b
applyExpr (Not e) ins  = not $ applyExpr e ins
applyExpr (And xs) ins = and $ map (\e -> applyExpr e ins) xs
applyExpr (Or xs) ins  = or $ map (\e -> applyExpr e ins) xs

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
	-- Depending on the number of True outputs, either a product-of-sums or a
	-- sum-of products translation yields a shorter expression. Since neither is
	-- particularly complicated, we implement both in order to get a good
	-- starting point for further simplification.
	productOfSums tt = And [ sumForInputs ins | (ins, out) <- tt, not out ]
	sumForInputs ins = Or [ if ival then Not (Var inum) else Var inum | (ival, inum) <- zip ins [0..] ]
	sumOfProducts tt = Or [ productForInputs ins | (ins, out) <- tt, out ]
	productForInputs ins = And [ if ival then Var inum else Not (Var inum) | (ival, inum) <- zip ins [0..] ]

tableFromExpr :: BoolExpr -> TruthTable
tableFromExpr e = map (\ins -> (ins, applyExpr e ins)) (permutations [False,True] (numVariables e)) where
	permutations :: [a] -> Int -> [[a]]
	permutations list num = sequence $ replicate num list
	numVariables = numVariables' 0
	numVariables' :: Int -> BoolExpr -> Int
	numVariables' acc (Var i)   = if i >= acc then i+1 else acc
	numVariables' acc (Const _) = 0
	numVariables' acc (Not e)   = numVariables' acc e
	numVariables' acc (And es)  = maximum $ map (numVariables' acc) es
	numVariables' acc (Or es)   = maximum $ map (numVariables' acc) es

{-
 - Converting between internal and string representations of truth tables
 -}

parseTruthTable :: String -> TruthTable
parseTruthTable = map (splitLast . map (=='1') . filter (`elem` "01")) . lines where
	splitLast l = (uncurry $ (.head) . (,)) $ splitAt (length l - 1) l

showTruthTable :: TruthTable -> String
showTruthTable = unlines . (map $ unwords . (map (\b -> if b then "1" else "0")) . (\(i,o) -> i++[o]))

{-
 - Debugging aid
 -}
testExpr :: BoolExpr -> TruthTable -> String
testExpr e tt = unlines $ map testLine tt where
	testLine (ins, out) = unwords $ map showBit $ ins ++ [out, applyExpr e ins]
	showBit b = if b then "1" else "0"

main = do
	interact $ show.simplify.sumOfProducts.exprFromTable.parseTruthTable
	putStr "\n"
