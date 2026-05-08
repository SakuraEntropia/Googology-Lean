import Mathlib.Data.Nat.Basic  -- 如果需要基本自然数定义，但即使无导入亦可

/-- 定义 3 的 Knuth 上箭头：`arrow_3 k b` 表示 3 ↑^k b -/
def arrow_3 (k b : Nat) : Nat :=
  if k = 0 then
    3 * b                      -- 0 个箭头视为乘法（通常不使用，但为递归完整）
  else if k = 1 then
    if b = 0 then 1 else 3 ^ b  -- 1 个箭头是幂
  else
    if b = 0 then 1
    else if b = 1 then 3
    else arrow_3 (k - 1) (arrow_3 k (b - 1))
termination_by (k, b)            -- 字典序保证终止

/-- 定义葛立恒数序列：g 1 = 3↑↑↑↑3, g (n+1) = 3 ↑^{g n} 3 -/
def g : Nat → Nat
  | 1 => arrow_3 4 3             -- 4 个箭头，底数和指数均为 3
  | n+1 => arrow_3 (g n) 3       -- 箭头个数为上一项的值

/-- 葛立恒数 G(64) -/
def GrahamNumber : Nat := g 64

-- 示例：可以验证类型
#check GrahamNumber  -- GrahamNumber : Nat