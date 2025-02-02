/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercice : Traduire en Lean les preuves dans le texte -/

-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 +5 := by rw [h2]
    _ = 6 + 5 := by norm_num
    _ = 11 := by norm_num
  done

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  calc
    x = 2 - 4 := by linarith
    _ = -2 := by norm_num
  done

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  calc
    b = 3 - 2 := by rw [h2]
    _ = 1 := by norm_num
    a = 5 * 1 + 4 := by rw [h1]
    _ = 5 + 4 := by norm_num
    _ = 9 := by norm_num
  done

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc
    3 * w = 4 - 1 := by linarith [h1]
    _ = 3 := by norm_num
    w = 3 / 3 := by field_simp
    _ = 1 := by norm_num
  done

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by
  calc
    2 * x + 3 - x = 0 := by rw [h1]; linarith
    x + 3 = 0 := by norm_num
    x = -3 := by linarith
  done

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 := by
  calc
    y - x = 1 := by linarith [h2]
    y = x + 1 := by linarith
    2 * x - (x + 1) = 4 := by rw [h1]
    x - 1 = 4 := by linarith
    x = 5 := by linarith
  done

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 := by
  (h1 + h2) / 2 = (4 + 6) / 2 := by
  calc
    2 * u = (u + 2 * v) + (u - 2 * v) := by ring
    _ = 4 + 6 := by rw [h1, h2]
    _ = 10 := by norm_num
    u = 10 / 2 := by field_simp
    _ = 5 := by norm_num
  done

-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 := by
  calc
    y = 4 - x :+ by rw [h1]
    5 * x - 3 * (4 - x) = 4 := by rw [h2]
    5 * x - 12 + 3 * x = 4 := by ring
    8 * x - 12 = 4 := by ring
    8 * x = 16 := by linarith
    x = 16 / 8 := by field_simp
    _ = 2 := by norm_num
  done

/-! # Exercises

Résolvez ces problèmes vous-même.  Il peut être utile de les résoudre sur papier avant de
les saisir dans Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 12 - 3 := by norm_num
    _ = 9 := by norm_num
  done


example {a b : ℤ} (h : a - b = 0) : a = b := by
  calc
    a = 0 + b := by rw [h]
    a = b := by linarith
  done

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 := by
  calc\
    x = 3 * y + 5 := by rw [h1]; linarith
    _ = 3 * 3 + 5 := by rw [h2]
    _ = 9 = 5 := by norm_num
    _ = 14 := by norm_num
  done


example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by
  calc
    y = 3 - 1 := by rw [h1]
    _ = 2 := by norm_num
    x = 3 - 2 * 2 := by rw [h2]
    _ = 3 - 4 := by norm_num
    _ = -1 := by norm_num
  done


example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  calc
    q = 2 + 1 := by rw [h2]
    _ = 3 := by norm_num
    p = 1 - 4 * 3 := by rw [h1]
    _ = 1 - 12 := by norm_num
    _ = - 11 := by norm_num
  done


example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3) (h3 : c = 1) :
    a = 2 := by
  calc
    b = 3 - 2 * c := by rw [h2]
    _ = 3 - 2 * 1 := by rw [h3]
    _ = 3 - 2 := by norm_num
    _ = 1 := by norm_num
    a = 7 - 2 * 1 - 3 * 1 := by rw [h1]
    _ = 7 - 2 - 3 := by norm_num
    _ = 2 := by norm_num
  done


example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 := by
  calc
    4 * u = 3 - 2 := by rw [h1, h2]
    _ = 1 := by norm_num
    u = 1 / 4 := by field_simp
  done


example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  calc
    4 * c - 3 * c = -2 - 1 := by linarith
    c = -3 := by norm_num
  done

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 := by
  calc
    5 * p - 3 - 3 * p = 1 := by linarith
    2 * p - 3 = 1 := by norm_num
    2 * p = 4 := by linarith
    p = 2 := by norm_num
  done

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 := by
  calc
    y = 1 - x := by rw [h2]
    2 * x + (1 - x) = 4 := by rw [h1]
    2 * x + 1 - x = 4 := by ring
    x + 1 = 4 := by linarith
    x = 3 := by norm_num
  done

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  calc
      b = a - 1 := by rw [h2]
      a + 2 * (a - 1) = 4 := by rw [h1]
      a + 2a - 2 = 4 := by ring
      3a - 2 = 4 := by ring
      3a = 6 := by linarith
      a = 2 := by norm_num
  done


example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by
  calc
    p = 1 + 2 * q := by rw [← h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = 1 - 2 := by norm_num
    _ = -1 := by norm_num
  done


example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 := by
  calc
    x = 5 - 3 := by rw [h1]
    _ = 2 := by norm_num
    2 * 2 - y * 2 = 0 := by rw [h2]
    4 - 2 * y = 0 := by ring
    4 = 2 * y := by linarith
    y = 4 / 2 := by field_simp
    _ = 2 := by norm_num
  done


example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by
  calc
    v = u + 1 := by rw [h1]
    v ^ 2 = (u + 1) ^ 2 := by rw [h1]
    _ = u ^ 2 + 2 * u + 1 := by ring
    v ^ 2 + v - 1 = (u ^ 2 + 2 * u + 1) + (u + 1) - 1 := by rw [h1]
    _ = u ^ 2 + 2 * u + 1 + u + 1 - 1 := by ring
    _ = u ^ 2 + 3 * u + 1 := by ring
  done

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  calc
    t ^ 2 = 4 := by linarith
    t ^ 4 = (t ^ 2) ^ 2 := by ring
    _ = 4 ^ 2 := by rw [← ht]
    _ = 16 := by norm_num
    t ^ 3 = t * t ^ 2 := by ring
    _ = t * 4 := by rw [ht]
    _ = 4 * t := by ring
    3 * t ^ 3 = 3 * (4 * t) := by rw [← ht]
    _ = 12 * t := by ring
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 16 + 12 * t - 3 * 4 - 2 * t - 2 := by rw [ht]
    _ = 16 + 12 * t - 12 - 2 * t - 2 := by norm_num
    _ = 4 + 10 * t - 2 := by ring
    _ = 10 * t + 2 := by norm_num
  done

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by
  calc
     (p + q + r) ^ 2 = p ^ 2 + q ^ 2 + r ^ 2 + 2 * (p * q + p * r + q * r) := by ring
      0 = p ^ 2 + q ^ 2 + r ^ 2 + 2 * 2 := by rw [h1, h2]
      _ = p ^ 2 + q ^ 2 + r ^ 2 + 4 := by norm_num
      p ^ 2 + q ^ 2 + r ^ 2 = -4 := by linarith
  done
