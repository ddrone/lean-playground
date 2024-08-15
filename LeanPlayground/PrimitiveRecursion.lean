import Mathlib.Data.Vector.Basic

inductive T : Nat → Type
  | var : {k : Nat} → Fin k → T k
  | const : (n k : Nat) → T k
  | succ : {k : Nat} → T k → T k
  -- First the number of iteration, then 0th element, then successor
  | iter : {k : Nat} → T k → T k → T (k + 1) → T k

def eval {k : Nat} (env : Mathlib.Vector ℕ k) : T k → ℕ
  | T.var v => env.get v
  | T.const n _ => n
  | T.succ e => eval env e + 1
  | T.iter count zero body =>
    let rec
      loop n := match n with
        | 0 => eval env zero
        | n + 1 => eval (Mathlib.Vector.cons (loop n) env) body
    loop (eval env count)
