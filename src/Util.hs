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

module Util where

{-
 - interleave two lists, starting with the first
 - the result list contains elements from both arguments in turn and terminates as soon as one of the arguments does
 -}
interleave :: [a] -> [a] -> [a]
interleave = interleave1 where
	interleave1 [] _ = []
	interleave1 (x:xs) ys = x:(interleave2 xs ys)
	interleave2 _ [] = []
	interleave2 xs (y:ys) = y:(interleave1 xs ys)

{-
 - count number of list elements for which predicate is True
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

