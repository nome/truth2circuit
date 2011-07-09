{-# LANGUAGE TupleSections, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, PatternGuards #-}
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
 - Helper function: count number of list elements for which predicate is True
 -}
count :: Enum b => (a -> Bool) -> [a] -> b
count pred = foldl (\c e -> if pred e then succ c else c) (toEnum 0)

{-
 - String padding
 -}
center, justifyLeft, justifyRight :: Int -> Char -> String -> String
center n c s       = let p = (n - length s) `div` 2 in replicate p ' ' ++ s ++ replicate (n - length s - p) c
justifyLeft n c s  = s ++ replicate (n - length s) c
justifyRight n c s = replicate (n - length s) c ++ s


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
 - Abstraction of low-level drawing routines
 -
 - Improves code readability by clearly separating details of the graphical representation from more
 - generic layout code; also it allows reusing the layout code for different output formats.
 -}
class Monad m => DrawingArea a m where
	drawLine   :: a -> (Int,Int) -> (Int,Int)       -> m ()
	drawDot    :: a -> (Int,Int)                    -> m ()
	drawGate   :: a -> (Int,Int) -> BoolExpr -> Int -> m ()
	drawMarker :: a -> (Int,Int) -> Bool -> String  -> m ()

{-
 - A DrawingContext contains layout-relevant properties of a DrawingArea implementation.
 - These need to be known in order to calculate the required size of the DrawingArea, i.e. before
 - creating it.
 -}
data DrawingContext = DrawingContext {
	gateWidth, gateHeight, xLineSep, yLineSep :: Int,
	gateInputs :: BoolExpr -> [Int],
	gateOutput :: BoolExpr -> Int
	}

-- coarse-grained placement of gates and "bypass" connections in a column
data Placement = Placement {
                   -- [(gate,output variable)]
                   gatePlacement :: [(BoolExpr,Int)],
                   -- list of pass-through connections
                   -- a pass-through connection starts in the column *after* the one containing the
                   -- output and ends in the column *before* the last one consuming it
                   bypassPlacement :: [Int]
                 }

place :: [BoolExpr] -> [Placement]
place bindings = map (uncurry Placement) (zip gates bypasses) where
	gates :: [[(BoolExpr, Int)]]
	gates = reverse $ map reverse $ gates' 0 bindings [[]] where
		gates' _ [] acc = acc
		gates' n (x:xs) (cur:done) = gates' (n+1) xs $ if isVar x
			then (((sortInputs x,n):cur):done)
			else (insert (snd $ unbox x) (sortInputs x,n) [] (reverse (cur:done)))

		insert _ x done [] = [x]:done
		insert sf x done (y:ys) = if null sf
			then (reverse ys) ++ (x:y):done
			else insert (filter (not.(`isIn` y)) sf) x (y:done) ys
		isIn (Var i) = any ((==i).snd)
		isIn _ = const True -- just in case we get fed unexpected input
		isVar (Var _) = True
		isVar _ = False

		sortInputs x = let (boxer,content) = unbox x in boxer $ sort content

	bypasses :: [[Int]]
	bypasses = reverse $ foldl bp [] [0 .. length gates - 1] where
		bp [] _ = [[]]
		bp (a:as) c = (:a:as) $ filter ((>c).lastConsume) (a ++  (map snd (gates!!(c-1))))

		lastConsume x = case findIndices (references x) gates of { [] -> -1; y -> maximum y }

		references i c = any (elem (Var i) . snd . unbox . fst) c

-- routing information for a layout column
data Routing = Routing {
	colLeft, colRight, connectLeft, connectRight :: Int,
	rowBounds :: [(Int,Int)],
	bypassPositions :: [Int],
	connectors :: [[(Int,Int,[Int])]]
	} deriving Show

route :: DrawingContext -> [Placement] -> [Routing]
route dc places = map routeColumn (zip3 places (zip colXs ((ymin,ymin):connectXs)) ([]:connectors)) where
	routeColumn (c, ((l,r),(ll,rr)), conn) = Routing l r ll rr (rowYs c) (passYs c) conn

	rowYs :: Placement -> [(Int,Int)]
	rowYs col = take (length $ gatePlacement col) $ let gh = gateHeight dc in zip [1,1+gh ..] [gh, 2*gh ..]

	passYs :: Placement -> [Int]
	passYs col = take (length $ bypassPlacement col) [sry + (yLineSep dc), sry + 2*(yLineSep dc) ..] where
		sry = snd (last (rowYs col))

	ymin = 1
	ymax = maximum $ map colHeight places where
		colHeight c = if null (passYs c)
			then snd (last (rowYs c))
			else max (snd (last (rowYs c))) (last (passYs c))

	-- for each column, computes a list of mappings out->[in] from the outputs of that column to
	-- their respective inputs (where out and in are visual row numbers)
	connections :: [[(Int,[Int])]]
	connections = map connections' (zip places (tail places)) where
		connections' (col,next) = filter (not.null.snd) $ connsFromGates ++ connsFromPass where
			connsFromGates = do
				((be,outvar), n) <- zip (gatePlacement col)   [0..]
				return $ (n*(gateHeight dc)+(gateOutput dc be), connsToVar outvar)
			connsFromPass = do
				(ptvar, n)       <- zip (bypassPlacement col) [0..]
				return $ ((length (gatePlacement col))*(gateHeight dc) + (n+1)*(yLineSep dc), connsToVar ptvar)
			connsToVar var  = connsToGates ++ connsToPass where
				connsToGates = do
					((be,_), n)   <- zip (gatePlacement next)  [0..]
					m <- findRefs var be
					return $ n*(gateHeight dc) + ((gateInputs dc be)!!m)
				connsToPass = do
					(var',n) <- zip (bypassPlacement next) [0..]
					guard $ var' == var
					return $ (length (gatePlacement next))*(gateHeight dc) + (n+1)*(yLineSep dc)
				findRefs var = (elemIndices (Var var)) . snd . unbox

	interColWidths :: [Int]
	interColWidths = map (\conns -> (xLineSep dc) * (length conns + length (collisions conns))) connections

	colXs :: [(Int,Int)]
	colXs = tail $ reverse $ foldl colXs' [(0,0)] (0:interColWidths) where
		colXs' a@((_,pe):_) sb = (pe+sb+1, pe+sb+gateWidth dc):a

	connectXs :: [(Int,Int)]
	connectXs = map (\((_,a),(b,_)) -> (a,b)) (zip colXs (tail colXs))

	-- when we have an output on the left and an input on the right on the same row,
	-- we have to take care to keep all the lines separate
	collisions :: [(Int, [Int])] -> [(Int, Int)]
	collisions conns = do
		((out,_), bp)      <- zip conns [0..]
		((out',ins'), bp') <- zip conns [0..]
		guard $ bp > bp'
		guard $ out `elem` ins'
		return (out', bp)

	-- for every column, gives a list of output -> inputs connections of the form
	-- [(yStart, xBranch, [yEnd])]
	-- we need to return two tuples in case of re-routing to avoid collisions => list
	connectors :: [[[(Int,Int,[Int])]]]
	connectors = map connectors' connections where
		connectors' conns = evalState (mapM connect conns) (collisionWidth + xLineSep dc, 0, []) where
			-- width of the buch of vertical lines needed for collision avoidance
			collisionWidth = (xLineSep dc) * (length (collisions conns))
			totalConnectWidth = (xLineSep dc) * (length conns + length (collisions conns))
			connect (from, tos) = case lookup from (collisions conns) of
				Nothing -> do
					-- simple connection (no collision avoidance needed)
					(n,m,aas) <- get
					put (n + xLineSep dc, m, aas)
					return [(from, n, tos)]
				Just bp -> do
					(n,m,aas) <- get
					let taboo = (aas++) $ join $ map (uncurry (:)) $ filter ((/= from).fst) conns
					let pref = sum tos `div` length tos
					let candsAbove = [pref, pref-(yLineSep dc) .. ymin]
					let candsBelow = [pref+(yLineSep dc), pref+2*(yLineSep dc) .. ymax]
					let cands = (interleave candsAbove candsBelow) \\ taboo
					if null cands
						then do
							-- couldn't find free visual row for drawing the connection between branch
							-- points return negative xBranch to indicate failure (we still have to return
							-- from and tos, in order to allow drawing code to insert markers there)
							put (n, m + xLineSep dc, aas)
							return $ [(from, -1, tos)]
						else do
							-- found a free visual row
							-- return two simple connections adding up to a connection avoiding the collision
							let avoidAt = head cands
							put (n, m + xLineSep dc, avoidAt:aas)
							return $ [(from, m, [avoidAt]), (avoidAt, (totalConnectWidth `div` 2) - m, tos)]

{-
 - Main circuit layout / drawing function
 -}
drawCircuit :: DrawingArea a m => ((Int,Int) -> m a) -> [Placement] -> [Routing] -> m a
drawCircuit newArea placements routings = do
	let width = colRight (last routings)
	let colHeight p = let b = bypassPositions p in if null b then snd (last $ rowBounds p) else last b
	let height = maximum $ map colHeight routings

	area <- newArea (width,height)
	forM_ (zip placements routings) (drawColumn area)
	return area

	where

	drawColumn :: DrawingArea a m => a -> (Placement, Routing) -> m ()
	drawColumn area (plac,rout) = do
		forM_ (zip (gatePlacement plac) (rowBounds rout)) (\((be,o),(ymin,_)) ->
			drawGate area (colLeft rout,ymin) be o)
		forM_ (bypassPositions rout) (\y -> drawLine area (colLeft rout, y) (colRight rout, y))
		forM_ (connectors rout) (\c ->
			forM_ (zip (rangeSplit (connectLeft rout, connectRight rout) (length c)) c) $
				uncurry (drawConnector area))

	rangeSplit :: (Int, Int) -> Int -> [(Int, Int)]
	rangeSplit (from, to) 1 = [(from,to)]
	rangeSplit (from, to) 2 = let w = (to-from) `div` 2 in [(from, from+w), (from+w, to)]

	drawConnector :: DrawingArea a m => a -> (Int,Int) -> (Int,Int,[Int]) -> m ()
	drawConnector area (xMin,xMax) (yStart, xBranchRel, yEnds) = if xBranchRel < 0
		then do
			drawMarker area (xMin, yStart) False (show yStart)
			forM_ yEnds (\y -> drawMarker area (xMax, y) True (show yStart))
		else do
			let top = (minimum (yStart:yEnds))
			let bottom = (maximum (yStart:yEnds))
			let xBranch = xBranchRel + xMin
			if top == bottom
				then drawLine area (xMin, yStart) (xMax, head yEnds)
				else do
					-- draw horizontal line from output to branch
					drawLine area (xMin,yStart) (xBranch,yStart)
					-- draw horizontal lines from branch to inputs
					forM_ yEnds $ (\y -> drawLine area (xBranch,y) (xMax,y))
					-- draw vertical branching line
					drawLine area (xBranch,top) (xBranch,bottom)
					-- mark branch points with a dot
					sequence_ [ drawDot area (xBranch, y) | y <- yStart:yEnds,
						y /= top    || (top    == yStart && top    `elem` yEnds),
						y /= bottom || (bottom == yStart && bottom `elem` yEnds) ]


{-
 - ASCII art drawing
 -}

-- any mutable array type will do
instance MArray a Char m => DrawingArea (a (Int,Int) Char) m where
	-- draw a single gate
	drawGate area (xmin,ymin) be o = forM_ (zip [ymin..] (visual be o)) (\(y,l) ->
		forM_ (zip [xmin..] l) (\(x,c) -> writeArray area (x,y) c))

	-- draw a horizontal or vertical line, inserting crossings (+) as needed
	-- and marking any other (unintentional) collisions with a !
	drawLine area (x1,y1) (x2,y2) = if x1 == x2
		then do
			forM_ [((min y1 y2)+1) .. ((max y1 y2)-1)] (\y -> drawSegment (x1,y) False False '|')
			when (y1 /= y2) $ drawSegment (x1, (min y1 y2)) False True '.'
			when (y1 /= y2) $ drawSegment (x1, (max y1 y2)) False True '\''
		else if y1 == y2
			then do
				forM_ [(min x1 x2) + 1 .. (max x1 x2) - 1] (\x -> drawSegment (x,y1) True False '-')
				drawSegment (min x1 x2, y1) True True '-'
				drawSegment (max x1 x2, y1) True True '-'
			else fail "ASCII-Art drawing supports only horizontal and vertical lines"
		where
		drawSegment pos horiz endp char = do
			current <- readArray area pos
			writeArray area pos $ case current of
			                           '|' -> if horiz then '+' else if endp then char else '!'
			                           '-' -> if endp then char else if horiz then '!' else '+'
			                           ' ' -> char
			                           '+' -> '+'
			                           _   -> '!' -- ! means there's a bug in layout/drawing code

	drawDot area pos = writeArray area pos '*'

	drawMarker area (x,y) left str = do
		writeArray area (x,y) 'o'
		forM_ (if left then zip (reverse str) [x-1,x-2..] else zip str [x+1..]) (\(c,xx) ->
			writeArray area (xx,y) c)

asciiArtContext :: DrawingContext
asciiArtContext = DrawingContext aaGateWidth aaGateHeight aaXLineSep aaYLineSep aaGateInputs aaGateOutput where
	aaGateWidth  = 12
	aaGateHeight = 4
	aaXLineSep = 2
	aaYLineSep = 1

	-- row numbers of in/outputs relative to the top of the respective visual
	aaGateOutput _             = 3
	aaGateInputs (Not _)       = [3]
	aaGateInputs (And [_,_])   = [2,4]
	aaGateInputs (And [_,_,_]) = [2,3,4]
	aaGateInputs (Or  [_,_])   = [2,4]
	aaGateInputs (Or  [_,_,_]) = [2,3,4]
	aaGateInputs x             = trace ("ERROR: can't get visual inputs of " ++ show x) []


visual :: BoolExpr -> Int ->  [String]
visual (And [_,_]) o = ["    __  " ++ center 3 ' ' (show (Var o)),
                        " --|  -  | ",
                        "   |   )-^-",
                        " --|__-    "]
visual (And [_,_,_]) o = ["    __  " ++ center 3 ' ' (show (Var o)),
                          " --|  -  | ",
                          " --|   )-^-",
                          " --|__-    "]
visual (And x) o =     ["        " ++ center 3 ' ' (show (Var o)),
                        " ERROR   | ",
                        " AND    -^-",
                        " " ++ justifyLeft 10 ' ' (show (length x))]
visual (Or [_,_])  o = ["   ___  " ++ center 3 ' ' (show (Var o)),
                        " -\\   -. | ",
                        "   )    >^-",
                        " -/___-'   "]
visual (Or [_,_,_])  o = ["   ___  " ++ center 3 ' ' (show (Var o)),
                          " -\\   -. | ",
                          " --)    >^-",
                          " -/___-'   "]
visual (Or x) o =      ["        " ++ center 3 ' ' (show (Var o)),
                        " ERROR   | ",
                        " OR     -^-",
                        " " ++ justifyLeft 10 ' ' (show (length x))]
visual (Not _) o = ["        " ++ center 3 ' ' (show (Var o)),
                    "         | ",
                    " ---|>o--^-",
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

-- turn a list of variable definitions (i.e. each BoolExpr represents a variable binding) into an
-- ASCII art drawing
bindingsToCircuit :: [BoolExpr] -> String
bindingsToCircuit bnd = showArray $ runSTUArray (circuit placement routing) where
	placement = place bnd
	routing = route asciiArtContext placement

	-- do not omit the type declaration of circuit, lest the wrath of
	-- InferredTypeIsLessPolymorphicThanExpected come upon us
	circuit :: MArray a Char m => [Placement] -> [Routing] -> m (a (Int,Int) Char)
	circuit = drawCircuit (\dim -> newArray ((1,1), dim) ' ')

	-- the easy part: convert final 2D char array into string
	showArray :: IArray a Char => a (Int,Int) Char -> String
	showArray a = unlines $ map (\y -> map ((a!).(,y)) [xmin..xmax]) [ymin..ymax] where
		((xmin,ymin), (xmax,ymax)) = bounds a



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
