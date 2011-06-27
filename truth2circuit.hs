module Main where

import Data.List
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
	show (And es) = concat (intersperse " " (map show (sort es)))
	show (Or [])  = "!EMPTY OR!"
	show (Or [x]) = "!OR " ++ show x ++ "!"
	show (Or es)  = "(" ++ concat (intersperse " + " (map show (sort es))) ++ ")"


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
tableFromExpr e = map (\ins -> (ins, applyExpr e ins)) (permutations [False,True] (maxVar e + 1)) where
	permutations :: [a] -> Int -> [[a]]
	permutations list num = sequence $ replicate num list

maxVar :: BoolExpr -> Int
maxVar = maxVar' (-1) where
	maxVar' acc (Var i)   = max acc i
	maxVar' acc (Const _) = -1
	maxVar' acc (Not e)   = maxVar' acc e
	maxVar' acc (And es)  = maximum $ map (maxVar' acc) es
	maxVar' acc (Or es)   = maximum $ map (maxVar' acc) es

{-
 - Converting between internal and string representations of truth tables
 -}

parseTruthTable :: String -> TruthTable
parseTruthTable = map (splitLast . map (=='1') . filter (`elem` "01")) . lines where
	splitLast l = (uncurry $ (.head) . (,)) $ splitAt (length l - 1) l

showTruthTable :: TruthTable -> String
showTruthTable = unlines . (map $ unwords . (map (\b -> if b then "1" else "0")) . (\(i,o) -> i++[o]))

-- for truth tables with multiple outputs
parseMultiTruthTable :: String -> [TruthTable]
parseMultiTruthTable str = map tableForOutput [0..(numOuts-1)] where
	numIns, numOuts :: Int
	numIns = truncate $ logBase 2 $ fromInteger.toInteger $ length (lines str)
	numOuts = (length $ convertLine (head (lines str))) - numIns
	convertLine :: String -> [Bool]
	convertLine = map (=='1') . filter (`elem` "01")
	tableForOutput :: Int -> TruthTable
	tableForOutput o = map ((uncurry $ (.(!!o)) . (,)) . splitAt numIns . convertLine) (lines str)


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


{-
 -}

showBindings :: [BoolExpr] -> String
showBindings = unlines . map (\(i,val) -> (show (Var i)) ++ " = " ++ show val) . zip [0..]

handleInput :: String -> IO ()
handleInput input = do
	let exprs    = map (simplify.sumOfProducts.exprFromTable) (parseMultiTruthTable input)
	let (evars, bindings) = createBindings (map toTernary exprs)
	putStrLn $ replicate 80 '='
	putStrLn "The truth table is generated by the following expressions:"
	putStrLn $ replicate 80 '-'
	putStr $ unlines $ map (\(v,e) -> show (Var v) ++ " = " ++ show e) (zip evars exprs)
	putStrLn ""
	putStrLn $ replicate 80 '='
	putStrLn "Subdivided into variable bindings implementable by logic gates:"
	putStrLn $ replicate 80 '-'
	putStr $ showBindings bindings

main = getContents >>= handleInput
