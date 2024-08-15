import Mathlib.Tactic.Ring

def choose : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n (k + 1) + choose n k

theorem choose_n_plus_k (n k : ℕ) : choose n (n + k + 1) = 0 := by
  induction n generalizing k with
  | zero => simp [choose]
  | succ n ih =>
    simp [choose]
    constructor
    { have eq : n + 1 + k + 1 = n + (k + 1) + 1 := by ring
      rw [eq]
      apply ih }
    { have eq : n + 1 + k = n + k + 1 := by ring
      rw [eq]
      apply ih }

theorem choose_n_n (n : ℕ) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [choose]
    rw [choose_n_plus_k n 0, ih]
