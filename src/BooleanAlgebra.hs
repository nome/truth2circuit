{-
 - Copyright (C) 2011 by Knut Franke (knut dot franke at gmx dot de)
 -
 - This program is free software; you can redistribute it and/or modify
 - it under the terms of the GNU General Public License as published by
 - the Free Software Foundation; either version 2 of the License, or
 - (at your option) any later version.
 -
 - This program is distributed in the hope that it will be useful,
 - but WITHOUT ANY WARRANTY; without even the implied warranty of
 - MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 - GNU General Public License for more details.
 -
 - You should have received a copy of the GNU General Public License
 - along with this program; if not, write to the Free Software
 - Foundation, Inc., 51 Franklin Street, Fifth Floor,
 - Boston, MA  02110-1301  USA
 -}

{-# LANGUAGE PatternGuards #-}
module BooleanAlgebra (
	BoolExpr(Var, Const, Not, And, Or),
	unbox,
	simplify,
	sumOfProducts,
	applyExpr,
	maxVar,
	toBinary,
	toTernary,
	createBindings,
	showBindings
	) where

import Data.List
import Control.Applicative ((<$>))
import Control.Monad.State
import Data.Maybe

{-
 - basic data type representing boolean expressions
 -}

data BoolExpr = Var Int | Const Bool | Not BoolExpr | And [BoolExpr] | Or [BoolExpr] deriving (Eq, Ord)

instance Show BoolExpr where
	show (Var i) = (concatMap (sequence . flip replicate ['a'..'z']) [1..]) !! i
	show (Const b) = show b
	show (Not e) = "/" ++ show e ++ "\\"
	show (And []) = "!EMPTY AND!"
	show (And [x]) = "!AND " ++ show x ++ "!"
	show (And es) = concat (intersperse " " (map show es))
	show (Or [])  = "!EMPTY OR!"
	show (Or [x]) = "!OR " ++ show x ++ "!"
	show (Or es)  = "(" ++ concat (intersperse " + " (map show es)) ++ ")"


-- helper function for reaching into composite expressions
unbox :: BoolExpr -> ([BoolExpr] -> BoolExpr, [BoolExpr])
unbox (And xs) = (And, xs)
unbox (Or  xs) = (Or,  xs)
unbox (Not x)  = (Not . head, [x])
unbox x        = (const x, [])


{-
 - code common to simplification of And and Or expressions
 -}
type BinaryBoolRules = BoolExpr -> BoolExpr -> Maybe BoolExpr
applyBinaryRules ::  BinaryBoolRules -> ([BoolExpr] -> BoolExpr) -> (BoolExpr -> Maybe [BoolExpr]) -> [BoolExpr] -> BoolExpr
applyBinaryRules rules box unbox input = applyBinaryRules' [] input where
	applyBinaryRules' :: [BoolExpr] -> [BoolExpr] -> BoolExpr
	-- unboxing
	applyBinaryRules' [] [x] = x
	-- splicing
	applyBinaryRules' done (cur:rest) | Just x <- unbox cur = applyBinaryRules' [] (done ++ x ++ rest)
	-- we finished applying rules to the list
	applyBinaryRules' done [current] = box $ sort $ current:done
	-- apply the binary rules
	applyBinaryRules' done (current:rest) = case applyRulesFor current [] rest of
															Just replacement -> applyBinaryRules' [] (done ++ replacement)
															Nothing -> applyBinaryRules' (current:done) rest
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
 - Finding an expression corresponding to a truth table is easy (see exprFromTable below); the
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
	binarySimplifyOr x (And ys) | Not x `elem` ys = Just $ simplify $ Or [x, And $ filter (/= Not x) ys]
	binarySimplifyOr (Not x) (And ys) | x `elem` ys = Just $ simplify $ Or [Not x, And $ filter (/= x) ys]
	-- try factoring out common terms and simplifying the rest
	binarySimplifyOr (And xs) (And ys) | isSane && isJust partsimp = Just $ simplify $ sumOfProducts $ And $ (fromJust partsimp):common where
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
 - Compute the highest variable index occuring in a given expression
 -}
maxVar :: BoolExpr -> Int
maxVar = maxVar' (-1) where
	maxVar' acc (Var i)   = max acc i
	maxVar' acc (Const _) = -1
	maxVar' acc (Not e)   = maxVar' acc e
	maxVar' acc (And es)  = maximum $ map (maxVar' acc) es
	maxVar' acc (Or es)   = maximum $ map (maxVar' acc) es


{-
 - bringing expressions into a circuit-equivalent form, i.e. taking care of limited number of
 - inputs on standard gates (=> nest were necessary) and flattening the parse tree by
 - introducing intermediate variables
 -}

-- split ANDs and ORs into nested binary relations
toBinary :: BoolExpr -> BoolExpr
toBinary be | length xs > 2 = foldl1 (\x y -> box [x,y]) (map toBinary xs) where
	(box, xs) = unbox be
toBinary be = be

-- split ANDs and ORs into nested ternary relations
toTernary :: BoolExpr -> BoolExpr
toTernary be | length xs > 3 = let (one,two) = splitAt 3 (map toTernary xs) in tt (box one) two where
	(box, xs) = unbox be
	tt x [] = x
	tt x xs = let (one,two) = splitAt 2 xs in tt (box (x:one)) two
toTernary be = be

 -- introduce intermediate variables
 -- return list of variable indices corresponding to inputs and a list of variable bindings
 -- this helps reduce redundancies
createBindings :: [BoolExpr] -> ([Int], [BoolExpr])
createBindings bes = (((map unvar).snd.unbox) toplevel , reverse others) where
	unvar (Var i) = i
	toplevel:others = execState (ii (And bes)) initialVars
	initialVars = reverse (map Var [0 .. maximum (map maxVar bes)])
	ii :: BoolExpr -> State [BoolExpr] BoolExpr
	ii (Const b) = return (Const b)
	ii (Var i)   = return (Var i)
	ii be = do
		let (box, xs) = unbox be
		replacement <- box <$> mapM ii xs
		vars <- get
		case findIndex (== replacement) vars of
			Just i -> return $ Var $ length vars - i - 1
			Nothing -> put (replacement:vars) >> (return $ Var $ length vars)

showBindings :: [BoolExpr] -> String
showBindings = unlines . map (\(i,val) -> (show (Var i)) ++ " = " ++ show val) . zip [0..]

