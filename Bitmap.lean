import Mathlib

open System (FilePath)
open System.Platform

namespace Bitmaps

structure Size where
  width  : UInt32
  height : UInt32
deriving Repr, BEq, DecidableEq

-------------------------------------------------------------------------------
-- A single color pixel of RGB values of any type
structure PixelRGB (RangeT : Type) where
  mk ::
  r : RangeT
  g : RangeT
  b : RangeT
deriving Repr, BEq, DecidableEq

-- Simple addition of intensities of two pixels
instance {α : Type} [Add α] : Add (PixelRGB α) where
  add p1 p2 := { r := p1.r + p2.r, g := p1.g + p2.g, b := p1.b + p2.b }

instance {α : Type} [Mul α] : Mul (PixelRGB α) where
  mul p1 p2 := { r := p1.r * p2.r, g := p1.g * p2.g, b := p1.b * p2.b }

def PixelRGB8  := PixelRGB UInt8
def PixelRGB16 := PixelRGB UInt16

-------------------------------------------------------------------------------
structure Bitmap (PixelT : Type) where
  mk ::
  size : Size
  data : Array PixelT
deriving Repr, BEq, DecidableEq

def BitmapRGB8 := Bitmap PixelRGB8

def putPixel {PixelT : Type} (i:Bitmap PixelT) (x:UInt32) (y:UInt32) (pixel:PixelT) :=
  { i with data := Array.modify i.data (UInt32.toNat (x + y * i.size.width)) (fun _ => pixel) }

def getPixel {PixelT : Type} (i:Bitmap PixelT) (x:UInt32) (y:UInt32) :=
  i.data[ UInt32.toNat (x + y * i.size.width) ]?

def mkBlankBitmap {RangeT : Type} (w : UInt32) (h : UInt32) (color : PixelRGB RangeT) : Bitmap (PixelRGB RangeT) := {
    size := { width := w, height := h },
    data := Array.replicate (UInt32.toNat (w * h)) color
  }

class FileWritable (α : Type) where
  write : FilePath -> α -> IO Unit

-------------------------------------------------------------------------------
-- Verification
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

def testPixel : PixelRGB8 := { r:=0, g:=0, b:=0 }

variable (α : Type) (aPixel aPixel' : PixelRGB α)

example : (mkBlankBitmap 0 0 aPixel).data = #[] := by rfl
example : (mkBlankBitmap 1 1 aPixel).data = #[aPixel] := by rfl

example (a : PixelRGB8) : mkBlankBitmap 1 1 a = mkBlankBitmap 1 1 a := by rfl
example : (mkBlankBitmap 1 1 aPixel).data = Array.modify (Array.replicate 1 aPixel) 0 (fun _ => aPixel) := by rfl
example : mkBlankBitmap 1 1 aPixel = putPixel (mkBlankBitmap 1 1 aPixel') 0 0 aPixel := by rfl
example : putPixel (mkBlankBitmap 2 2 aPixel) 0 0 aPixel = mkBlankBitmap 2 2 aPixel := by rfl

theorem zeroPlus (x : UInt32) : 0 + x = x := by
  simp [zero_add]

example : ∀ w : UInt32, w > 0 → (putPixel (mkBlankBitmap w 1 aPixel) 0 0 aPixel = mkBlankBitmap w 1 aPixel) := by
  intro w h
  simp [mkBlankBitmap, putPixel]
  unfold Array.replicate
  sorry


/-
example (w : UInt32) : w = 0 ∨ (putPixel (mkBlankBitmap w 1 aPixel) 0 0 aPixel = mkBlankBitmap w 1 aPixel) :=
  match w with
  | 0 => by apply Or.inl; rfl
  | x => by
    apply Or.inr
    apply (fun (_ : x > 0) => _)
    assumption
    simp [putPixel, Array.modify, Array.modifyM]
-/


/-
theorem putPixel1 (a b : PixelRGB8) : putPixel (mkBlankBitmap 1 1 a) 0 0 b = mkBlankBitmap 1 1 b := by
  conv =>
    simp [putPixel]
    lhs
    simp [mkBlankBitmap]
    args
    rfl
    rfl
    done
-/

def testBitmap : BitmapRGB8 := {
  size := { width := 1, height := 1 },
  data := #[ PixelRGB.mk 0 0 0 ]
}

#check (PixelRGB.mk 0 0 0)
#eval mkBlankBitmap 0 0 testPixel

#eval putPixel testBitmap 0 0 ({ r:=1, g:=2, b:=3 })

-- def List.sum [Add α] [OfNat α 0] : List α → α
-- Fin class for Bitmap?
-- USize (OS bit integer, like C unsigned long)
-- LinearAlgebra namespace - https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.html
-- dbgTraceIfShared
