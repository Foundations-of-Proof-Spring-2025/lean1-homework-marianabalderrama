/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.5: A shortcut -/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  addarith [h1]
  calc
    x = 2 - 4 := by addarith [h1]
    _ = -2 := by norm_num
  done

example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by
  addarith [ha]
  calc
    x = 2 - 4 := by addarith [h1]
    _ = -2 := by norm_num
  done

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 := by
  calc
    x + y ^ 2 = x - 7 := by addarith [hy]
    _ = -5 := by addarith [hx]
  done

-- Vérifiez que `addarith` ne peut pas vérifier cette déduction
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc
    3 * w = 4 - 1 := by addarith [h1]
    _ = 3 := by norm_num
    w = 3 / 3 := by field_simp
    _ = 1 := by norm_num
  done
