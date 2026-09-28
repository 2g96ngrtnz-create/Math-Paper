import Mathlib

/-!
Sanity checks that the Lean toolchain and the locally built Mathlib work.
Each check exercises a different part of Mathlib that the formalisation will rely on.
-/

-- Kernel evaluation and decidable arithmetic.
#eval Nat.factorization 360 2   -- expected: 3
example : Nat.Prime 97 := by norm_num

-- Divisibility and the natural-number API used in Lemma 3.1.
example (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b := Nat.le_of_dvd hb h

-- Real analysis: the logarithm, used later for Mertens/Dickman-type statements.
example : Real.log 1 = 0 := Real.log_one

-- Finsets and the prime-counting setup.
example : (Finset.filter Nat.Prime (Finset.range 20)).card = 8 := by decide

-- A non-trivial Mathlib theorem: infinitely many primes.
example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := Nat.exists_infinite_primes n
