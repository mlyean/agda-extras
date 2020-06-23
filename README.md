# agda-extras

Some extra stuff to supplement agda-stdlib.

## Theories

Currently has some additional theories on `Nat` in `src/Extra/Data/Nat`, including
- Factorials `_!_` (in `Factorial.agda`)
  - `m≤n⇒m!∣n! : _! Preserves _≤_ ⟶ _∣_`
- Binomial coefficients `_C_` (in `Binomial.agda`)
  - `C-!-div : ∀ (m n : ℕ) → (m + n) C m ≡ ((m + n) !) / (m ! * n !)`
  - `C-!-mod : ∀ (m n : ℕ) → ((m + n) !) % (m ! * n !) ≡ 0`
- Fibonacci numbers (in `Fibonacci.agda`)
  - `fib-rec : ∀ (m n : ℕ) → fib (suc (m + n)) ≡ fib m * fib n + fib (suc m) * fib (suc n)`
  - `fib-gcd-suc : ∀ n → gcd (fib n) (fib (suc n)) ≡ 1`
- GCD (in `GCD.agda`)
  - `gcd[n,0]≡n : ∀ n → gcd n 0 ≡ n`
  - `gcd-split : ∀ m n d → Coprime m n → d ∣ m * n → d ≡ gcd d m * gcd d n`
  - `gcd-multʳ : ∀ k → Multiplicative (gcd k)`

## TO-DO

- (`Fibonacci.agda`) Prove `fib-gcd : ∀ (m n : ℕ) → gcd (fib m) (fib n) ≡ fib (gcd m n)`
