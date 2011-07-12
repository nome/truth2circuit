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

module CairoDrawing where

import qualified CircuitDrawing as CD
import BooleanAlgebra
import Graphics.UI.Gtk
import Graphics.Rendering.Cairo
import Control.Monad
import Debug.Trace

i2d :: Int -> Double
i2d = fromInteger . toInteger

cairoContext :: CD.DrawingContext
cairoContext = CD.DrawingContext cGateWidth cGateHeight cXLineSep cYLineSep cGateInputs cGateOutput where
	cGateWidth = 60
	cGateHeight = 50
	cXLineSep = 10
	cYLineSep = 10

	cGateOutput _             = 21
	cGateInputs (Not _)       = [21]
	cGateInputs (And [_,_])   = [11,31]
	cGateInputs (And [_,_,_]) = [11,21,31]
	cGateInputs (Or  [_,_])   = [11,31]
	cGateInputs (Or  [_,_,_]) = [11,21,31]
	cGateInputs x             = trace ("ERROR: can't get visual inputs of " ++ show x) []

instance CD.CircuitDraw Render where
	drawLine (x1,y1) (x2,y2) = do
		moveTo (i2d x1) (i2d y1)
		lineTo (i2d x2) (i2d y2)
		stroke

	drawDot (x,y) = do
		arc (i2d x) (i2d y) 4 0 (2*pi)
		fill

	drawMarker (x,y) left str = do
		arc (i2d x) (i2d y) 4 0 (2*pi)
		stroke
		te <- textExtents str
		moveTo (i2d x-(if left then 2 + textExtentsWidth te else -2)) (i2d y+(textExtentsHeight te)/2)
		showText str

	drawGate (x,y) v@(Var _) _ = do
		save ; translate (i2d x) (i2d y)
		moveTo 60 20 ; lineTo 30 20
		moveTo 24 14 ; lineTo 30 20 ; lineTo 24 26
		stroke
		te <- textExtents (show v)
		moveTo (20-textExtentsWidth te) (20+(textExtentsHeight te)/2)
		showText (show v)
		restore

	drawGate (x,y) (Const b) _ = do
		save ; translate (i2d x) (i2d y)
		moveTo 60 20 ; lineTo 30 20
		moveTo 24 14 ; lineTo 30 20 ; lineTo 24 26
		stroke
		te <- textExtents (show b)
		moveTo (20-textExtentsWidth te) (20+(textExtentsHeight te)/2)
		showText (show b)
		restore

	drawGate (x,y) (And [_,_]) o = do
		save ; translate (i2d x) (i2d y)
		moveTo 30 0
		arc 30 20 20 (-pi/2) (pi/2)
		lineTo 10 40 ; lineTo 10 0
		closePath ; stroke
		forM_ [(0,10),(0,30),(50,20)] (\(xx,yy) -> moveTo xx yy >> relLineTo 10 0)
		stroke
		te <- textExtents $ show (Var o)
		moveTo (30-(textExtentsWidth te)/2) (20+(textExtentsHeight te)/2)
		showText $ show (Var o)
		restore
	
	drawGate (x,y) (And (ins@[_,_,_])) o = do
		CD.drawGate (x,y) (And (take 2 ins)) o
		moveTo (i2d x) (i2d y+20)
		relLineTo 10 0
		stroke
	
	drawGate (x,y) (Or [_,_]) o = do
		save ; translate (i2d x) (i2d y)
		moveTo 10 0
		curveTo 30 0 40 0 50 20
		curveTo 40 40 30 40 10 40
		curveTo 20 20 10 0 10 0
		closePath ; stroke
		forM_ [(0,10),(0,30),(50,20)] (\(xx,yy) -> moveTo xx yy >> relLineTo 10 0)
		stroke
		te <- textExtents $ show (Var o)
		moveTo (30-(textExtentsWidth te)/2) (20+(textExtentsHeight te)/2)
		showText $ show (Var o)
		restore

	drawGate (x,y) (Or (ins@[_,_,_])) o = do
		CD.drawGate (x,y) (Or (take 2 ins)) o
		moveTo (i2d x) (i2d y+20)
		relLineTo 10 0
		stroke
	
	drawGate (x,y) (Not _) o = do
		save ; translate (i2d x) (i2d y)
		moveTo 30 20 ; lineTo 14 12 ; lineTo 14 28
		closePath ; stroke
		arc 34 20 4 0 (2*pi)
		stroke
		moveTo  0 20 ; lineTo 14 20
		moveTo 38 20 ; lineTo 60 20
		stroke
		te <- textExtents $ show (Var o)
		moveTo (50-(textExtentsWidth te)/2) 16
		showText $ show (Var o)
		restore

displayCircuit :: [BoolExpr] -> IO ()
displayCircuit bnd = do
	let placement = CD.place bnd
	let routing = CD.route cairoContext placement
	let (w,h) = CD.circuitSize routing

	initGUI
	window <- windowNew
	set window [ windowDefaultWidth := 300, windowDefaultHeight := 200 ]
	scroll <- scrolledWindowNew Nothing Nothing
	containerAdd window scroll
	canvas <- drawingAreaNew
	widgetModifyBg canvas StateNormal (Color 65535 65535 65535)
	widgetSetSizeRequest canvas w h
	scrolledWindowAddWithViewport scroll canvas
	widgetShowAll window

	let renderSettings = do
		setSourceRGB 0 0 0
		setLineWidth 2
		setLineCap LineCapRound
		setLineJoin LineJoinRound
		selectFontFace "Droid" FontSlantNormal FontWeightNormal
		setFontSize 14

	let renderCircuit = renderSettings >> CD.drawCircuit placement routing

	drawing <- widgetGetDrawWindow canvas
	onExpose canvas $ const $ renderWithDrawable drawing renderCircuit >> return True

	onDestroy window mainQuit
	mainGUI
