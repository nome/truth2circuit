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

{-# LANGUAGE MultiParamTypeClasses #-}

module CircuitDrawing where

import BooleanAlgebra
import Util
import Control.Monad.State
import Data.List

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
	colTop, colBottom :: Int,
	rowBounds :: [(Int,Int)],
	bypassPositions :: [Int],
	connectors :: [[(Int,Int,[Int])]]
	} deriving Show

route :: DrawingContext -> [Placement] -> [Routing]
route dc places = map routeColumn (zip3 places (zip colXs ((ymin,ymin):connectXs)) ([]:connectors)) where
	routeColumn (c, ((l,r),(ll,rr)), conn) = Routing l r ll rr ymin ymax (rowYs c) (passYs c) conn

	rowYs :: Placement -> [(Int,Int)]
	rowYs col = take (length $ gatePlacement col) $ let gh = gateHeight dc in zip [1,1+gh ..] [gh, 2*gh ..]

	passYs :: Placement -> [Int]
	passYs col = take (length $ bypassPlacement col) [sry+1, sry+1+(yLineSep dc) ..] where
		sry = snd (last (rowYs col))

	ymin = 1
	ymax = maximum $ map colHeight places where
		colHeight c = if null (passYs c)
			then snd (last (rowYs c))
			else (last (passYs c)) + (yLineSep dc)

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
				return $ ((passYs col)!!n, connsToVar ptvar)
			connsToVar var  = connsToGates ++ connsToPass where
				connsToGates = do
					((be,_), n)   <- zip (gatePlacement next)  [0..]
					m <- findRefs var be
					return $ n*(gateHeight dc) + ((gateInputs dc be)!!m)
				connsToPass = do
					(var',n) <- zip (bypassPlacement next) [0..]
					guard $ var' == var
					return $ (passYs next)!!n
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
					let pref = round (fromIntegral (sum tos) / fromIntegral (length tos) / (fromIntegral $ yLineSep dc)) * (yLineSep dc) + 1
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

circuitSize :: [Routing] -> (Int,Int)
circuitSize routings = (width, height) where
	width = colRight (last routings)
	height = maximum $ map colBottom routings

{-
 - Main circuit layout / drawing function
 -}
drawCircuit :: DrawingArea a m => a -> [Placement] -> [Routing] -> m a
drawCircuit area ps rs = forM_ (zip ps rs) (drawColumn area) >> return area where

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

