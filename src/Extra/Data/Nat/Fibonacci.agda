module Extra.Data.Nat.Fibonacci where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.GCD using (gcd; gcd-comm)
open import Data.Nat.Coprimality as CP
open import Data.Nat.Divisibility using (_∣_; m∣m*n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (False; fromWitnessFalse; toWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import Extra.Data.Nat.GCD

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

fib-mono-≤ : fib Preserves _≤_ ⟶ _≤_
fib-mono-≤ {0} {n} _ = z≤n
fib-mono-≤ {1} {suc zero} _ = s≤s z≤n
fib-mono-≤ {1} {suc (suc n)} _ = ≤-trans (fib-mono-≤ {1} {suc n} (s≤s z≤n)) (m≤n+m (fib (suc n)) (fib n))
fib-mono-≤ {suc (suc m)} {suc (suc n)} (s≤s (s≤s m≤n)) = +-mono-≤ (fib-mono-≤ m≤n) (fib-mono-≤ (s≤s m≤n))

fib>0 : ∀ n → n > 0 → fib n > 0
fib>0 n n>0 = fib-mono-≤ n>0

fib≡0 : ∀ n → fib n ≡ 0 → n ≡ 0
fib≡0 zero ≡0 = refl
fib≡0 (suc n) ≡0 = contradiction ≡0 (m<n⇒n≢0 (fib>0 (suc n) (s≤s z≤n)))

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

fib′-gcd-suc : (a : ℕ → ℕ)
        → (fib′ a)
        → ∀ n → gcd (a n) (a (suc n)) ≡ gcd (a 0) (a 1)
fib′-gcd-suc a ha zero = refl
fib′-gcd-suc a ha (suc n) = begin
  gcd (a (1 + n)) (a (2 + n))
    ≡⟨ cong (λ x → gcd (a (1 + n)) x) (ha n) ⟩
  gcd (a (1 + n)) (a n + a (1 + n))
    ≡⟨ gcdʳ-+ʳ (a (1 + n)) (a n) ⟩
  gcd (a (1 + n)) (a n)
    ≡⟨ gcd-comm (a (1 + n)) (a n) ⟩
  gcd (a n) (a (1 + n))
    ≡⟨ fib′-gcd-suc a ha n ⟩
  gcd (a 0) (a 1)
    ∎
  where
    open ≡-Reasoning

fib-gcd-suc : ∀ n → gcd (fib n) (fib (suc n)) ≡ 1
fib-gcd-suc = fib′-gcd-suc fib (λ _ → refl)

fib-suc-coprime : ∀ n → Coprime (fib n) (fib (suc n))
fib-suc-coprime n = gcd≡1⇒coprime (fib-gcd-suc n)

gcd-fib-rec : ∀ (m n : ℕ) {≢0} → gcd (fib m) (fib n) ≡ gcd (fib n) (fib ((m % n) {≢0}))
gcd-fib-rec m n@(suc n-1) {≢0} = begin
  gcd (fib m) (fib n)
    ≡⟨ gcd-comm (fib m) (fib n) ⟩
  gcd (fib n) (fib m)
    ≡⟨ cong (λ x → gcd (fib n) (fib x)) (m≡m%n+[m/n]*n m n-1) ⟩
  gcd (fib n) (fib (m % n + (m / n) * n))
    ≡⟨ lem₁ (m / n) ⟩
  gcd (fib n) (fib (m % n))
    ∎
  where
    open ≡-Reasoning
    open +-*-Solver
    fib≢0 : False (fib n ≟ 0)
    fib≢0 = fromWitnessFalse {Q = fib n ≟ 0} (toWitnessFalse {Q = n ≟ 0} ≢0 ∘ fib≡0 n)
    lem₁ : ∀ (k : ℕ) → gcd (fib n) (fib (m % n + k * n)) ≡ gcd (fib n) (fib (m % n))
    lem₁ zero rewrite +-identityʳ (m % n) = refl
    lem₁ (suc k) = begin
      gcd (fib n) (fib (m % n + (suc k) * n))
        ≡⟨⟩
      gcd (fib n) (fib (m % n + (n + k * n)))
        ≡⟨ cong (λ x → gcd (fib n) (fib x)) (solve 3 (λ a b c → a :+ (b :+ c) := b :+ (a :+ c)) refl (m % n) n (k * n)) ⟩
      gcd (fib n) (fib (n + (m % n + k * n)))
        ≡⟨⟩
      gcd (fib n) (fib (suc (n-1 + (m % n + k * n))))
        ≡⟨ cong (gcd (fib n)) (fib-rec n-1 (m % n + k * n)) ⟩
      gcd (fib n) (fib n-1 * fib (m % n + k * n) + fib n * fib (suc (m % n + k * n)))
        ≡⟨ gcdʳ-∣ {fib n} {fib n-1 * fib (m % n + k * n)} {fib n * fib (suc (m % n + k * n))} (m∣m*n (fib (suc (m % n + k * n)))) ⟩
      gcd (fib n) (fib n-1 * fib (m % n + k * n))
        ≡⟨ gcd-coprime-cancel (CP.sym (fib-suc-coprime n-1)) ⟩
      gcd (fib n) (fib (m % n + k * n))
        ≡⟨ lem₁ k ⟩
      gcd (fib n) (fib (m % n))
        ∎

gcd-fib : ∀ (m n : ℕ) → gcd (fib m) (fib n) ≡ fib (gcd m n)
gcd-fib m n = gcd-induction m n lem₁ lem₂
  where
    open ≡-Reasoning
    lem₁ : ∀ m → gcd (fib m) 0 ≡ fib (gcd m 0)
    lem₁ m rewrite gcd[n,0]≡n (fib m) | gcd[n,0]≡n m = refl
    lem₂ : ∀ m n {≢0}
         → gcd (fib n) (fib ((m % n) {≢0})) ≡ fib (gcd n ((m % n) {≢0}))
         → gcd (fib m) (fib n) ≡ fib (gcd m n)
    lem₂ m n {≢0} h = begin
      gcd (fib m) (fib n)
        ≡⟨ gcd-fib-rec m n {≢0} ⟩
      gcd (fib n) (fib (m % n))
        ≡⟨ h ⟩
      fib (gcd n (m % n))
        ≡˘⟨ cong fib (gcd-rec m n) ⟩
      fib (gcd m n)
        ∎
