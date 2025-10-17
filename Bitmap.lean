import Mathlib
import Init.Data.Array.Lemmas
import Init.Data.Array.Set
import Mathlib.Tactic.Linarith

-- Widgets
import Lean
open Lean Widget

open System (FilePath)
open System.Platform

namespace Bitmaps

structure Size where
  width  : ℕ
  height : ℕ
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

  valid : data.size = size.width * size.height := by simp
deriving Repr, DecidableEq

def BitmapRGB8 := Bitmap PixelRGB8

lemma arrayCoordSize_nat
    {i x y w h : Nat}
    (hx : x < w) (hy : y < h) (hi : i = x + y * w) :
    i < w * h := by
  subst hi
  -- 1) use x < w ⇒ x + y*w < w + y*w
  have hx' : x + y * w < w + y * w := Nat.add_lt_add_right hx _
  -- 2) rewrite w + y*w = w*(y+1)
  have hx'' : x + y * w < w * (y + 1) := by
    simpa [Nat.mul_comm, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx'
  -- 3) y < h ⇒ y+1 ≤ h ⇒ w*(y+1) ≤ w*h
  have hy'  : w * (y + 1) ≤ w * h := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hy)
  -- 4) chain them
  exact lt_of_lt_of_le hx'' hy'

lemma arrayCoordSize_u32
    {i w h : Nat} {x y : UInt32}
    (hx : x.toNat < w)
    (hy : y.toNat < h)
    (hi : i = x.toNat + y.toNat * w) :
    i < w * h := by
  -- Apply the Nat lemma to the toNat values
  have hlt :
      x.toNat + y.toNat * w < w * h :=
    arrayCoordSize_nat (i := x.toNat + y.toNat * w)
      hx hy rfl
  simpa [hi] using hlt

-- This is not right way to do it. I think that axiom should not be needed.
axiom idxFromCoord {i w : ℕ} {x y : UInt32} : i = x.toNat + y.toNat * w

def putPixel {PixelT : Type} (img:Bitmap PixelT) (x y : UInt32) (pixel : PixelT)
             (h1 : x.toNat < img.size.width) (h2: y.toNat < img.size.height) :=

  let idx := x.toNat + y.toNat * img.size.width

  have inBounds : idx < img.data.size := by
    rw [img.valid]
    apply arrayCoordSize_u32
    case hx =>
      exact h1
    case hy =>
      exact h2
    case hi =>
      apply idxFromCoord

  -- Array.size_set
  let resultArr := Array.set img.data idx pixel inBounds

  have inResInBounds : resultArr.size = img.data.size := by
    rw [Array.size_set]

  { img with data := resultArr, valid := by rw [inResInBounds, img.valid] }

def getPixel {PixelT : Type} (i:Bitmap PixelT) (x:UInt32) (y:UInt32) :=
  i.data[ x.toNat + y.toNat * i.size.width ]?

def mkBlankBitmap {RangeT : Type} (w h : ℕ) (color : PixelRGB RangeT) : Bitmap (PixelRGB RangeT) := {
    size := { width := w, height := h },
    data := Array.replicate (w * h) color
  }

class FileWritable (α : Type) where
  write : FilePath -> α -> IO Unit

-------------------------------------------------------------------------------
-- Verification. Converting tests into proofs.
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

def testPixel : PixelRGB8 := { r:=0, g:=0, b:=0 }

variable (α : Type) (aPixel aPixel' : PixelRGB α)

example : (mkBlankBitmap 0 0 aPixel).data = #[] := by rfl
example : (mkBlankBitmap 1 1 aPixel).data = #[aPixel] := by rfl

example (a : PixelRGB8) : mkBlankBitmap 1 1 a = mkBlankBitmap 1 1 a := by rfl
example : (mkBlankBitmap 1 1 aPixel).data = Array.modify (Array.replicate 1 aPixel) 0 (fun _ => aPixel) := by rfl

example : mkBlankBitmap 1 1 aPixel =
          putPixel (mkBlankBitmap 1 1 aPixel') 0 0 aPixel
                   (by unfold mkBlankBitmap; simp) (by unfold mkBlankBitmap; simp) := by rfl

example : putPixel (mkBlankBitmap 2 2 aPixel) 0 0 aPixel
                   (by unfold mkBlankBitmap; simp) (by unfold mkBlankBitmap; simp) =
          mkBlankBitmap 2 2 aPixel := by rfl

theorem zeroPlus (x : UInt32) : 0 + x = x := by
  simp [zero_add]

-- theorem modifyWithSameIsSame (p : aPixel) : Bitmap p

--lemma pixelIsSameAfterModification (p : aPixel)

example : ∀ w : ℕ → (putPixel (mkBlankBitmap w 1 aPixel) 0 0 aPixel = mkBlankBitmap w 1 aPixel) := by
  intro w h
  simp [mkBlankBitmap, putPixel]
  sorry
  -- unfold Array.replicate
  /-
  -- ({ toList := List.replicate w.toNat aPixel }.modify 0 fun x ↦ aPixel) =
  --  { toList := List.replicate w.toNat aPixel }

  -- This is only for a single element of an array:
  -- Array.getElem_modify_self @ Init.Data.Array.Lemmas
  --    {α : Type u_1} {xs : Array α} {i : ℕ} (f : α → α) (h : i < (xs.modify i f).size) : (xs.modify i f)[i] = f xs[i]

  -- source theorem Array.eq_toArray {α✝ : Type u_1}  {xs : Array α✝}  {as : List α✝}

  theorem Array.getElem_replicate {α : Type u_1}  {n : Nat}  {v : α}  {i : Nat}  (h : i < (replicate n v).size) :
(replicate n v)[i] = v

theorem Array.getElem_set_self {α : Type u_1}  {xs : Array α}  {i : Nat}  (h : i < xs.size)  {v : α} :
(xs.set i v h)[i] = v

theorem Array.set_getElem_self {α : Type u_1}  {xs : Array α}  {i : Nat}  (h : i < xs.size) :
xs.set i xs[i] h = xs
  -/
  --rw [Array.getElem_modify_self id 0]


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

#eval putPixel testBitmap 0 0 ({ r:=1, g:=2, b:=3 }) (by unfold testBitmap; simp) (by unfold testBitmap; simp)

end Bitmaps

-- def List.sum [Add α] [OfNat α 0] : List α → α
-- Fin class for Bitmap?
-- USize (OS bit integer, like C unsigned long)
-- LinearAlgebra namespace - https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.html
-- dbgTraceIfShared

@[widget_module]
def helloWidget : Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      return React.createElement('p', {}, 'Hello ' + name + '!')
    }"

#widget helloWidget
