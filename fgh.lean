import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Iterate

/-!
# Fast-growing hierarchy (FGH) in Lean 4

We define the standard FGH for natural number indices:
- `f 0 n = n + 1`
- `f (k + 1) n = (f k)^[n] n`   (i.e., iterate `f k` `n` times on `n`)

No axioms or `sorry` are used. The definition is computable in theory,
though values for larger `k` grow extremely fast.
-/

/-- Iterate a function `f : ℕ → ℕ` `m` times starting from `n`. -/
def iterate (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | m+1, n => f (iterate f m n)

/-- Fast-growing hierarchy for finite indices. -/
def fgh : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | k+1, n => iterate (fgh k) n n

-- Examples (theorems that can be proved, but not executed due to huge growth)
-- fgh 1 n = 2*n
-- fgh 2 n = 2^n * n  (approximately)

/-- The function `f_3` grows like tetration. -/
def f3 (n : ℕ) : ℕ := fgh 3 n

/-- The function `f_ω` would require a limit ordinal; for natural numbers it's not defined.
    To define FGH for limit ordinals, we would need a notion of ordinal and fundamental sequences. -/