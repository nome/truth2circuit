{-# LANGUAGE TupleSections, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
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

module AsciiArtDrawing (
	AsciiArtDrawing.drawCircuit
	) where

import CircuitDrawing
import BooleanAlgebra
import Util
import Data.Array.ST
import Data.Array.Unboxed
import Control.Monad
import Debug.Trace

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
drawCircuit :: [BoolExpr] -> String
drawCircuit bnd = showArray $ runSTUArray (circuit placement routing) where
	placement = place bnd
	routing = route asciiArtContext placement

	-- do not omit the type declaration of circuit, lest the wrath of
	-- InferredTypeIsLessPolymorphicThanExpected come upon us
	circuit :: MArray a Char m => [Placement] -> [Routing] -> m (a (Int,Int) Char)
	circuit = CircuitDrawing.drawCircuit (\dim -> newArray ((1,1), dim) ' ')

	-- the easy part: convert final 2D char array into string
	showArray :: IArray a Char => a (Int,Int) Char -> String
	showArray a = unlines $ map (\y -> map ((a!).(,y)) [xmin..xmax]) [ymin..ymax] where
		((xmin,ymin), (xmax,ymax)) = bounds a

