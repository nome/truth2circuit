{-# LANGUAGE TupleSections, FlexibleContexts #-}
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
module Main where

import Data.List
import Data.Maybe
import Control.Monad.State
import Data.Functor
import Data.Array.ST
import Data.Array.Unboxed
import Debug.Trace

{-
 - Helper function: interleave two lists, starting with the first
 - the result list contains elements from both arguments in turn and terminates as soon as one of the arguments does
 -}
interleave :: [a] -> [a] -> [a]
interleave = interleave1 where
	interleave1 [] _ = []
	interleave1 (x:xs) ys = x:(interleave2 xs ys)
	interleave2 _ [] = []
	interleave2 xs (y:ys) = y:(interleave1 xs ys)

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

-- filter out empty lines and comments
isTableLine []      = False
isTableLine ('#':_) = False
isTableLine _       = True

parseTruthTable :: String -> TruthTable
parseTruthTable = map (splitLast . map (=='1') . filter (`elem` "01")) . (filter isTableLine) . lines where
	splitLast l = (uncurry $ (.head) . (,)) $ splitAt (length l - 1) l

showTruthTable :: TruthTable -> String
showTruthTable = unlines . (map $ unwords . (map (\b -> if b then "1" else "0")) . (\(i,o) -> i++[o]))

-- for truth tables with multiple outputs
parseMultiTruthTable :: String -> [TruthTable]
parseMultiTruthTable str = map tableForOutput [0..(numOuts-1)] where
	rows = filter isTableLine (lines str)
	numIns, numOuts :: Int
	numIns = truncate $ logBase 2 $ fromInteger.toInteger $ length rows
	numOuts = (length $ convertLine (head rows)) - numIns
	convertLine :: String -> [Bool]
	convertLine = map (=='1') . filter (`elem` "01")
	tableForOutput :: Int -> TruthTable
	tableForOutput o = map ((uncurry $ (.(!!o)) . (,)) . splitAt numIns . convertLine) rows


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
 - Now, towards a graphical representation of a BoolExpr as logic gates
 -}

center n c s       = let p = (n - length s) `div` 2 in replicate p ' ' ++ s ++ replicate (n - length s - p) c
justifyLeft n c s  = s ++ replicate (n - length s) c
justifyRight n c s = replicate (n - length s) c ++ s

visual :: BoolExpr -> Int ->  [String]
visual (And [_,_]) o = ["    __  " ++ center 3 ' ' (show (Var o)),
                        "---|  -  | ",
                        "   |   )-^-",
                        "---|__-    "]
visual (And [_,_,_]) o = ["    __  " ++ center 3 ' ' (show (Var o)),
                          "---|  -  | ",
                          "---|   )-^-",
                          "---|__-    "]
visual (And x) o =     ["        " ++ center 3 ' ' (show (Var o)),
                        " ERROR   | ",
                        " AND    -^-",
                        " " ++ justifyLeft 10 ' ' (show (length x))]
visual (Or [_,_])  o = ["   ___  " ++ center 3 ' ' (show (Var o)),
                        "--\\   -. | ",
                        "   )    >^-",
                        "--/___-'   "]
visual (Or [_,_,_])  o = ["   ___  " ++ center 3 ' ' (show (Var o)),
                          "--\\   -. | ",
                          "---)    >^-",
                          "--/___-'   "]
visual (Or x) o =      ["        " ++ center 3 ' ' (show (Var o)),
                        " ERROR   | ",
                        " OR     -^-",
                        " " ++ justifyLeft 10 ' ' (show (length x))]
visual (Not _) o = ["        " ++ center 3 ' ' (show (Var o)),
                    "         | ",
                    "----|>o--^-",
                    "           "]

visual (Var i) _ = ["           ",
                    "           ",
                    justifyRight 5 ' ' (show (Var i)) ++ " >----",
                    "           "]

visual (Const True) _ =  ["           ",
                          "           ",
                          " True >----",
                          "           "]
visual (Const False) _ = ["           ",
                          "           ",
                          "False >----",
                          "           "]
-- drawing functions should work with any mutable array type
type Arena a = a (Int, Int) Char

-- turn a list of variable definitions (i.e. each BoolExpr represents a variable binding) into an ASCII art drawing
bindingsToCircuit :: [BoolExpr] -> String
bindingsToCircuit input = showArray $ runSTUArray draw where

	l :: [[(BoolExpr,Int)]]
	l = layout input

	-- returns a list of columns, each of which is a list of (gate,output var) pairs
	layout :: [BoolExpr] -> [[(BoolExpr,Int)]]
	layout = reverse . map reverse . layout' 0 [[]] where
		layout' _ acc [] = acc
		layout' n (cur:done) (x:xs) = if isVar x
		                                  then layout' (n+1) (((sortInputs x,n):cur):done) xs
		                                  else layout' (n+1) (insert (snd $ unbox x) (sortInputs x,n) [] (reverse (cur:done))) xs
		insert _ x done [] = [x]:done
		insert sf x done (y:ys) = if null sf
		                              then (reverse ys) ++ (x:y):done
		                              else insert (filter (not.(`isIn` y)) sf) x (y:done) ys
		isIn (Var i) = any ((==i).snd)
		isIn _ = const True -- just in case we get fed unexpected input
		isVar (Var _) = True
		isVar _ = False
		sortInputs x = let (boxer,content) = unbox x in boxer $ sort content

	-- the easy part: convert final 2D char array into string
	showArray :: IArray a Char => a (Int,Int) Char -> String
	showArray a = unlines $ map (\y -> map ((a!).(,y)) [xmin..xmax]) [ymin..ymax] where
		((xmin,ymin), (xmax,ymax)) = bounds a

	-- list of pass-through connections in each column
	-- a pass-through connection starts in the column *after* the one containing the output
	-- and ends in the column *before* the last one consuming it
	passThrough :: [[Int]]
	passThrough = reverse $ foldl pt [] [0 .. length l - 1] where
		pt [] _ = [[]]
		pt (a:as) c = (:a:as) $ filter ((>c).lastConsume) (a ++  (map snd (l!!(c-1))))
		lastConsume x = case findIndices (references x) l of { [] -> -1; y -> maximum y }
		references i c = any (elem (Var i) . snd . unbox . fst) c

	-- for each column, contains a list of mappings out->[in] from the outputs of that column to their respective inputs
	-- (where out and in are visual row numbers)
	connections :: [[(Int,[Int])]]
	connections = map (uncurry connsBetween) $ zip (zip l passThrough) (tail (zip l passThrough)) where
		connsBetween (out,outpt) (ins,inpt) = connsFromGates ++ connsFromPass where
			connsFromGates  = [ (n*visualHeight+visualOutput,       connsToVar outvar) | ((_,outvar),n) <- zip out   [0..] ]
			connsFromPass   = [ ((length out)*visualHeight + n + 1, connsToVar ptvar)  | (ptvar,n)      <- zip outpt [0..] ]
			connsToVar var  = connsToGates ++ connsToPass where
				connsToGates = [ n*visualHeight + ((visualInputs be)!!m) | ((be,_),n) <- zip ins [0..], m <- findRefs var be]
				connsToPass  = [ (length ins)*visualHeight + n + 1       | (var',n)   <- zip inpt [0..], var' == var        ]
				findRefs var = (elemIndices (Var var)) . snd . unbox
		-- row numbers of in/outputs relative to the top of the respective visual
		visualOutput               = 3
		visualInputs (Not _)       = [3]
		visualInputs (And [_,_])   = [2,4]
		visualInputs (And [_,_,_]) = [2,3,4]
		visualInputs (Or  [_,_])   = [2,4]
		visualInputs (Or  [_,_,_]) = [2,3,4]
		visualInputs x             = trace ("ERROR: can't get visual inputs of " ++ show x) []

	-- number of rows we need for the visual represenation of each column
	colHeights :: [Int]
	colHeights = [ visualHeight*(length gates) + (length passes) | (gates, passes) <- zip l passThrough ]

	-- space needed after each column in order to draw all connections
	interColWidths :: [Int]
	interColWidths = map (\conns -> 2 * (length conns + 2 * length (collisions conns))) connections

	-- when we have an output on the left and an input on the right on the same row,
	-- we have to take care to keep all the lines separate
	collisions conns = do
		((out,_), bp)      <- zip conns [0..]
		((out',ins'), bp') <- zip conns [0..]
		guard $ bp > bp'
		guard $ out `elem` ins'
		return (out', bp)

   -- dimensions of visual gate representations
	visualWidth, visualHeight :: Int
	visualWidth = 11
	visualHeight = 4

	draw :: (MArray a Char m) => m (Arena a)
	draw = do
		arena <- newArray ((1,1), (visualWidth*(length l) + sum interColWidths, maximum colHeights)) ' '
		bounds <- getBounds arena
		foldM_ (drawColumn arena) 1 (zip3 l passThrough (interColWidths++[0]))
		foldM_ (drawConnectionsAt arena) (visualWidth+1) (zip connections interColWidths)
		return arena

	-- draw a given set of connections between two columns of gates
	drawConnectionsAt :: (MArray a Char m) => Arena a -> Int -> ([(Int,[Int])], Int) -> m Int
	drawConnectionsAt arena xmin (conns, space) = do
		let xmax = xmin + space - 1
		let collWidth = 2 * (length (collisions conns))
		let connect (n,m,aas) (from,to) = case lookup from (collisions conns) of
		                                      Nothing -> drawConnectionsFrom arena (xmin+collWidth+n) xmin xmax from to >> return (n+2,m,aas)
		                                      Just bp -> do
		                                          let taboo = (aas++) $ join $ map (uncurry (:)) $ filter ((/= from).fst) conns
		                                          let preferred = sum to `div` length to
		                                          let cands = interleave [preferred,preferred-1..1] [preferred+1,preferred+2..(maximum colHeights)]
		                                          if null (cands \\ taboo)
		                                             then do
		                                                writeArray arena (xmin, from) 'o'
		                                                forM_ (zip (show from) [xmin+1..]) (\(c,x) -> writeArray arena (x,from) c)
		                                                forM_ to (\t -> writeArray arena (xmax, t) 'o' >>
		                                                                forM_ (zip (reverse (show from)) [xmax-1,xmax-2..])
		                                                                      (\(c,x) -> writeArray arena (x,t) c))
		                                                return (n,m+2,aas)
		                                             else do
		                                                let avoidAt = head $ cands \\ taboo
		                                                let center = ((xmin+xmax) `div` 2)
		                                                drawConnectionsFrom arena (xmin+m) xmin       center  from    [avoidAt]
		                                                drawConnectionsFrom arena (xmax-m) (center+1) xmax    avoidAt to
		                                                return (n,m+2,avoidAt:aas)
		foldM_ connect (collWidth, 0, []) conns
		return (xmax+visualWidth+1)

	-- draw connections starting at a given output
	drawConnectionsFrom :: (MArray a Char m) => Arena a -> Int -> Int -> Int -> Int -> [Int] -> m ()
	drawConnectionsFrom _ _ _ _ _ [] = return ()
	drawConnectionsFrom arena branchAt startX endX startY endYs = do
		let top = (minimum (startY:endYs))
		let bottom = (maximum (startY:endYs))
		-- draw horizontal line from output to branch
		drawLine arena True startX (branchAt-1) startY
		-- draw horizontal lines from branch to inputs
		forM_ endYs $ drawLine arena True (branchAt+1) endX
		if top == bottom
			then drawLine arena True branchAt branchAt top
			else do
				-- draw vertical branching line
				drawLine arena False top bottom branchAt
				-- replace top corner with a nicer symbol, if appropriate
				if top == startY && top `elem` endYs
					then return ()
					else writeArray arena (branchAt, top) $ if top == startY then '.' else ','
				-- replace bottom corner with a nicer symbol, if appropriate
				if bottom == startY && bottom `elem` endYs
					then return ()
					else writeArray arena (branchAt, bottom) $ '\'' --if bottom == startY then '’' else '`'
				-- replace branch point with a * (i.e. a dot)
				sequence_ [ writeArray arena (branchAt, y) '*' | y <- startY:endYs, y /= top || (top == startY && top `elem` endYs), y /= bottom || (bottom == startY && bottom `elem` endYs) ]

	-- draw all gates in a given column
	drawColumn :: (MArray a Char m) => Arena a -> Int -> ([(BoolExpr,Int)], [Int], Int) -> m Int
	drawColumn arena xmin (col, passes, spaceAfter) = do
		let xmax = xmin + visualWidth - 1
		mapM_ (\(ymin,(be,o)) -> drawBoolExpr arena xmin ymin be o) $ zip [1,1+visualHeight ..] col
		let bottom = visualHeight*(length col)
		mapM_ (drawLine arena True xmin xmax) [bottom+1 .. bottom+(length passes)]
		return (xmax + spaceAfter + 1)

	-- draw a single gate
	drawBoolExpr :: (MArray a Char m) => Arena a -> Int -> Int -> BoolExpr -> Int -> m ()
	drawBoolExpr arena xmin ymin be o = forM_ (zip [ymin..] (visual be o)) (\(y,l) -> forM_ (zip [xmin..] l) (\(x,c) -> writeArray arena (x,y) c))

	-- draw a horizontal or vertical line, inserting crossings (+) as needed
	-- and marking any other (unintentional) collisions with a !
	drawLine :: (MArray a Char m) => Arena a -> Bool -> Int -> Int -> Int -> m ()
	drawLine arena horiz min max at = forM_ [min..max] (\o -> do
		let pos = if horiz then (o,at) else (at,o)
		current <- readArray arena pos
		writeArray arena pos $ case current of
		                            '|' -> if horiz then '+' else '!'
		                            '-' -> if horiz then '!' else '+'
		                            ' ' -> if horiz then '-' else '|'
		                            _   -> '!' -- ! means there's a bug in layout/drawing code
		)

showBindings :: [BoolExpr] -> String
showBindings = unlines . map (\(i,val) -> (show (Var i)) ++ " = " ++ show val) . zip [0..]

handleInput :: String -> IO ()
handleInput input = do
	let exprs    = map (simplify.sumOfProducts.exprFromTable) (parseMultiTruthTable input)
	let (evars, bindings) = createBindings (map toTernary exprs)
	let circuit  = bindingsToCircuit bindings
	putStrLn $ replicate 80 '='
	putStrLn "The truth table is generated by the following expressions:"
	putStrLn $ replicate 80 '-'
	putStr $ unlines $ map (\(v,e) -> show (Var v) ++ " = " ++ show e) (zip evars exprs)
	putStrLn ""
	putStrLn $ replicate 80 '='
	putStrLn "Subdivided into variable bindings implementable by logic gates:"
	putStrLn $ replicate 80 '-'
	putStr $ showBindings bindings
	putStrLn ""
	putStrLn $ "============"
	let (numAnd2, numAnd3, numOr2, numOr3, numNot) = foldl countGates (0,0,0,0,0) bindings where
		countGates (a2,a3,o2,o3,n) (And [_,_])   = (a2+1,a3,o2,o3,n)
		countGates (a2,a3,o2,o3,n) (And [_,_,_]) = (a2,a3+1,o2,o3,n)
		countGates (a2,a3,o2,o3,n) (Or [_,_])    = (a2,a3,o2+1,o3,n)
		countGates (a2,a3,o2,o3,n) (Or [_,_,_])  = (a2,a3,o2,o3+1,n)
		countGates (a2,a3,o2,o3,n) (Not _)       = (a2,a3,o2,o3,n+1)
		countGates (a2,a3,o2,o3,n) _             = (a2,a3,o2,o3,n)
	putStrLn $ "type  number"
	putStrLn $ "------------"
	putStrLn $ "2xAND " ++ show numAnd2
	putStrLn $ "3xAND " ++ show numAnd3
	putStrLn $ "2xOR  " ++ show numOr2
	putStrLn $ "3xOR  " ++ show numOr3
	putStrLn $ "NOT   " ++ show numNot
	putStrLn $ "------------"
	putStrLn $ "total " ++ show (numAnd2 + numAnd3 + numOr2 + numOr3 + numNot)
	putStrLn ""
	putStrLn $ replicate 80 '='
	putStrLn "The corresponding circuit looks like this:"
	putStrLn $ replicate 80 '-'
	putStr circuit

main = getContents >>= handleInput
