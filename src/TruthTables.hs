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

module TruthTables where

import BooleanAlgebra
import Util

{-
 - Represent truth tables as pairs of [inputs], output
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

