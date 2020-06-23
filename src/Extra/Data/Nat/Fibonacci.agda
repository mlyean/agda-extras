module Extra.Data.Nat.Fibonacci where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.GCD
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Function

open import Extra.Data.Nat.GCD

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

fib′ : Pred (ℕ → ℕ) _
fib′ a = ∀ n → a (suc (suc n)) ≡ a n + a (suc n)

fib′-rec : (a : ℕ → ℕ)
             → fib′ a
             → ∀ n → a (suc n) ≡ fib n * a 0 + fib (suc n) * a 1
fib′-rec a ha zero rewrite +-identityʳ (a 1) = refl
fib′-rec a ha (suc zero) rewrite +-identityʳ (a 0) | +-identityʳ (a 1) = ha 0
fib′-rec a ha (suc (suc n)) = begin
  a (3 + n)
    ≡⟨ ha (suc n) ⟩
  a (1 + n) + a (2 + n)
    ≡⟨ cong₂ _+_  (fib′-rec a ha n) (fib′-rec a ha (suc n)) ⟩
  (fib n * a 0 + fib (1 + n) * a 1) + (fib (1 + n) * a 0 + fib (2 + n) * a 1)
    ≡⟨ solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d))
             refl (fib n * a 0) (fib (1 + n) * a 1) (fib (1 + n) * a 0) (fib (2 + n) * a 1) ⟩
  (fib n * a 0 + fib (1 + n) * a 0) + (fib (1 + n) * a 1 + fib (2 + n) * a 1)
    ≡˘⟨ cong₂ _+_ (*-distribʳ-+ (a 0) (fib n) (fib (1 + n))) (*-distribʳ-+ (a 1) (fib (1 + n)) (fib (2 + n))) ⟩
  fib (2 + n) * a 0 + fib (3 + n) * a 1
    ∎
  where
    open ≡-Reasoning
    open +-*-Solver

fib-rec : ∀ (m n : ℕ) → fib (suc (m + n)) ≡ fib m * fib n + fib (suc m) * fib (suc n)
fib-rec m n = fib′-rec (fib ∘ (_+ n)) (λ _ → refl) m

fib′-gcd : (a : ℕ → ℕ)
        → (fib′ a)
        → ∀ n → gcd (a n) (a (suc n)) ≡ gcd (a 0) (a 1)
fib′-gcd a ha zero = refl
fib′-gcd a ha (suc n) = begin
  gcd (a (1 + n)) (a (2 + n))
    ≡⟨ cong (λ x → gcd (a (1 + n)) x) (ha n) ⟩
  gcd (a (1 + n)) (a n + a (1 + n))
    ≡⟨ gcdʳ-+ʳ (a (1 + n)) (a n) ⟩
  gcd (a (1 + n)) (a n)
    ≡⟨ gcd-comm (a (1 + n)) (a n) ⟩
  gcd (a n) (a (1 + n))
    ≡⟨ fib′-gcd a ha n ⟩
  gcd (a 0) (a 1)
    ∎
  where
    open ≡-Reasoning
