import Mathlib
-- 91 = 7 * 13 is NOT prime: this must fail
example : Nat.Prime 91 := by norm_num
