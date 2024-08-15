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

theorem choose_n_0 (n : ℕ) : choose n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ n => rfl

def sum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => f (n + 1) + sum f n

def sum_1 (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => f (n + 1) + sum_1 f n

def binom (x y : ℕ) (n k : ℕ) : ℕ := choose n k * x^k * y^(n - k)

def binom_sum (x y n : ℕ) := sum (λ k => binom x y n k) n

#eval binom_sum 1 1 5
#eval binom_sum 0 2 5
#eval binom_sum 1 2 2

theorem sum_eq (f g : ℕ → ℕ) (n : ℕ) (h : ∀ x, f x = g x) : sum f n = sum g n := by
  induction n with
  | zero =>
    simp [sum]
    rw [h]
  | succ n ih =>
    simp [sum]
    rw [h, ih]

theorem sum_1_eq (f g : ℕ → ℕ) (n : ℕ) (h : ∀ x, f (x + 1) = g (x + 1)) : sum_1 f n = sum_1 g n := by
  induction n with
  | zero =>
    simp [sum_1]
  | succ n ih =>
    simp [sum_1]
    rw [h, ih]

theorem sum_1_eq_strong (f g : ℕ → ℕ) (n : ℕ) (h : ∀ x, x ≤ n → f x = g x) : sum_1 f n = sum_1 g n := by
  induction n with
  | zero =>
    simp [sum_1]
  | succ n ih =>
    simp [sum_1]
    rw [h, ih]
    intro k hk
    apply h
    exact Nat.le_add_right_of_le hk
    exact Nat.le_refl (n + 1)

theorem sum_mult (f : ℕ → ℕ) (n x : ℕ) : sum f n * x = sum (λ k => f k * x) n := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    simp [sum]
    rw [Nat.add_mul, ih]

theorem sum_1_mult (f : ℕ → ℕ) (n x : ℕ) : sum_1 f n * x = sum_1 (λ k => f k * x) n := by
  induction n with
  | zero => simp [sum_1]
  | succ n ih =>
    simp [sum_1]
    rw [Nat.add_mul, ih]

theorem sum_1_add (f g : ℕ → ℕ) (n : ℕ) : sum_1 f n + sum_1 g n = sum_1 (λ k => f k + g k) n := by
  induction n with
  | zero => simp [sum_1]
  | succ n ih =>
    simp [sum_1]
    rw [← ih]
    ring

theorem rename_index (f : ℕ → ℕ) (n : ℕ) : sum_1 f (n + 1) = sum (λ k => f (k + 1)) n := by
  induction n with
  | zero => simp [sum_1, sum]
  | succ n ih =>
    simp [sum_1, sum]
    rw [← ih]
    rfl

theorem sum_to_sum_1 (f : ℕ → ℕ) (n : ℕ) : sum f n = f 0 + sum_1 f n := by
  induction n with
  | zero => simp [sum, sum_1]
  | succ n ih =>
    simp [sum, sum_1]
    rw [ih]
    ring

def f1 x y n := sum_1 (λ k => choose n k * x^k * y^(n - k) * y) n

def f2 x y n := sum_1 (λ k => choose n k * x^k * y^(n + 1 - k)) n

#print Nat.pow_add

theorem aux_thm (y n k : ℕ) (h : k ≤ n) : y^(n - k) * y = y^(n+1-k) := by
  have t1 : y^1 = y := by rw [Nat.pow_one]
  nth_rw 2 [← t1]
  rw [← Nat.pow_add]
  have t2 : n - k + 1 = n + 1 - k := by
    exact Eq.symm (Nat.sub_add_comm h)
  rw [t2]

theorem rw4 : sum_1 (λ k => choose n k * x^k * y^(n - k) * y) n = sum_1 (λ k => choose n k * x^k * y^(n+1-k)) n := by
  apply sum_1_eq_strong
  intro k hk
  rw [← aux_thm]
  ring
  assumption

theorem binomial_theorem (x y n : ℕ) : (x + y)^n = sum (λ k => binom x y n k) n := by
  induction n with
  | zero => simp [sum, binom, choose]
  | succ n ih =>
    have rw1 : sum (λ k => binom x y n k * x) n = sum_1 (λ k => choose n (k - 1) * x^k * y^(n+1-k)) (n + 1) := by
      rw [rename_index]
      simp
      apply sum_eq
      intro k
      simp [binom]
      ring
    have rw2 : sum_1 (λ k => binom x y (n + 1) k) n = sum_1 (λ k => (choose n k + choose n (k - 1)) * x^k * y^(n+1-k)) n := by
      apply sum_1_eq
      intro k
      rw [binom, choose]
      have t : k + 1 - 1 = k := by
        rfl
      rw [t]
    have rw3 : sum_1 (λ k => (choose n k + choose n (k - 1)) * x^k * y^(n+1-k)) n = sum_1 (λ k => choose n k * x^k * y^(n+1-k)) n + sum_1 (λ k => choose n (k - 1) * x^k * y^(n+1-k)) n := by
      rw [sum_1_add]
      apply sum_1_eq
      intro k
      simp
      ring
    calc
      (x + y) ^ (n + 1) = (x + y)^n * x + (x + y)^n * y := by
        rw [Nat.pow_add]
        simp
        rw [Nat.mul_add]
      _ = sum (λ k => binom x y n k * x) n + sum (λ k => binom x y n k * y) n := by
        rw [ih, ← sum_mult, ← sum_mult]
      _ = x^(n + 1) + y^(n + 1) + sum_1 (λ k => choose n (k - 1) * x^k * y^(n + 1 - k)) n + sum_1 (λ k => choose n k * x^k * y^(n - k) * y) n := by
        rw [rw1, sum_1, sum_to_sum_1]
        simp [binom, choose_n_n, choose_n_0]
        have t1 : y ^ n * y = y^(n + 1) := by rfl
        rw [t1]
        ring
      _ = sum (fun k => binom x y (n + 1) k) (n + 1) := by
        rw [sum, binom, choose_n_n, sum_to_sum_1, binom, choose_n_0]
        simp
        rw [rw2, rw3, rw4]
        ring
