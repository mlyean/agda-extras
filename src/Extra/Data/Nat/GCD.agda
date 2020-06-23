module Extra.Data.Nat.GCD where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Coprimality using (Coprime; coprime⇒gcd≡1)
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.GCD
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Algebra.Definitions {A = ℕ} _≡_

*-mono-∣ : _*_ Preserves₂ _∣_ ⟶ _∣_ ⟶ _∣_
*-mono-∣ {m} {h} {n} {k} m∣h n∣k = ∣-trans (*-monoˡ-∣ n m∣h) (*-monoʳ-∣ h n∣k)

gcd[n,0]≡n : ∀ n → gcd n 0 ≡ n
gcd[n,0]≡n n = sym (gcd-universality {n} {0} {n} proj₁ (λ {d} d∣n → d∣n , d ∣0))

gcd[0,n]≡n : ∀ n → gcd 0 n ≡ n
gcd[0,n]≡n n = sym (gcd-universality {0} {n} {n} proj₂ λ {d} d∣n → (d ∣0) , d∣n)

gcd∣gcd : ∀ {m n h k}
        → (∀ {d} → d ∣ m × d ∣ n → d ∣ h × d ∣ k)
        → gcd m n ∣ gcd h k
gcd∣gcd {m} {n} {h} {k} d with d {gcd m n} (gcd[m,n]∣m m n , gcd[m,n]∣n m n)
... | gcd[m,n]∣h , gcd[m,n]∣k = gcd-greatest gcd[m,n]∣h gcd[m,n]∣k

gcd≡gcd : ∀ {m n h k}
          → (∀ {d} → d ∣ m × d ∣ n → d ∣ h × d ∣ k)
          → (∀ {d} → d ∣ h × d ∣ k → d ∣ m × d ∣ n)
          → gcd m n ≡ gcd h k
gcd≡gcd d₁ d₂ = ∣-antisym (gcd∣gcd d₁) (gcd∣gcd d₂)

gcdʳ-+ˡ : ∀ m n → gcd m (m + n) ≡ gcd m n
gcdʳ-+ˡ m n = gcd≡gcd {m} {m + n} {m} {n}
              (λ (d∣m , d∣m+n) → d∣m , ∣m+n∣m⇒∣n d∣m+n d∣m)
              (λ (d∣m , d∣n) → d∣m , ∣m∣n⇒∣m+n d∣m d∣n)

gcdʳ-+ʳ : ∀ m n → gcd m (n + m) ≡ gcd m n
gcdʳ-+ʳ m n rewrite +-comm n m = gcdʳ-+ˡ m n

gcdˡ-+ˡ : ∀ m n → gcd (n + m) n ≡ gcd m n
gcdˡ-+ˡ m n rewrite gcd-comm (n + m) n | gcd-comm m n = gcdʳ-+ˡ n m

gcdˡ-+ʳ : ∀ m n → gcd (m + n) n ≡ gcd m n
gcdˡ-+ʳ m n rewrite +-comm m n = gcdˡ-+ˡ m n

gcd-mono-∣ : gcd Preserves₂ _∣_ ⟶ _∣_ ⟶ _∣_
gcd-mono-∣ {m} {h} {n} {k} m∣h n∣k = gcd-greatest {h} {k} (∣-trans (gcd[m,n]∣m m n) m∣h) (∣-trans (gcd[m,n]∣n m n) n∣k)

gcd-monoʳ-∣ : ∀ n → (gcd n) Preserves _∣_ ⟶ _∣_
gcd-monoʳ-∣ n = gcd-mono-∣ (∣-refl {n})

gcd-monoˡ-∣ : ∀ n → (λ x → gcd x n) Preserves _∣_ ⟶ _∣_
gcd-monoˡ-∣ n h∣k = gcd-mono-∣ h∣k ∣-refl

gcd-assoc : Associative gcd
gcd-assoc m n k = gcd≡gcd {gcd m n} {k} {m} {gcd n k}
                    (λ (d∣gcd[m,n] , d∣k)
                      → (∣-trans d∣gcd[m,n] (gcd[m,n]∣m m n) ,
                        gcd-greatest (∣-trans d∣gcd[m,n] (gcd[m,n]∣n m n)) d∣k))
                    (λ (d∣m , d∣gcd[n,k])
                      → gcd-greatest d∣m (∣-trans d∣gcd[n,k] (gcd[m,n]∣m n k)) ,
                        ∣-trans d∣gcd[n,k] (gcd[m,n]∣n n k))

gcd-split₁ : ∀ m n d → Coprime m n → gcd d m * gcd d n ∣ d
gcd-split₁ m n d coprime = begin
  gcd d m * gcd d n
    ∣⟨ gcd-greatest (*-mono-∣ (gcd[m,n]∣n d m) (gcd[m,n]∣m d n)) (*-mono-∣ (gcd[m,n]∣m d m) (gcd[m,n]∣n d n)) ⟩
  gcd (m * d) (d * n)
    ≡⟨ cong (λ x → gcd x (d * n)) (*-comm m d) ⟩
  gcd (d * m) (d * n)
    ≡˘⟨ c*gcd[m,n]≡gcd[cm,cn] d m n ⟩
  d * gcd m n
    ≡⟨ cong (d *_) (coprime⇒gcd≡1 coprime) ⟩
  d * 1
    ≡⟨ *-identityʳ d ⟩
  d
    ∎
  where
    open ∣-Reasoning

gcd-split₂ : ∀ m n d → Coprime m n → d ∣ m * n → d ∣ gcd d m * gcd d n
gcd-split₂ zero n d coprime d∣mn rewrite gcd[n,0]≡n d = m∣m*n (gcd d n)
gcd-split₂ m zero d coprime d∣mn rewrite gcd[n,0]≡n d = n∣m*n (gcd d m)
gcd-split₂ m@(suc m′) n@(suc n′) d coprime d∣mn with gcd[m,n]∣m d n
... | divides k d≡k*gcd[d,n] = lem₅
  where
    open ∣-Reasoning
    lem₁ : k * gcd d n ∣ m * gcd d n
    lem₁ = begin
      k * gcd d n
        ≡˘⟨ d≡k*gcd[d,n] ⟩
      d
        ∣⟨ gcd-greatest (n∣m*n m) d∣mn ⟩
      gcd (m * d) (m * n)
        ≡˘⟨ c*gcd[m,n]≡gcd[cm,cn] m d n ⟩
      m * gcd d n
        ∎
    lem₂ : k ∣ m
    lem₂ = *-cancelʳ-∣ (gcd d n) {fromWitnessFalse (gcd[m,n]≢0 d n (inj₂ 1+n≢0))} lem₁
    lem₃ : k ∣ d
    lem₃ = begin
      k
        ∣⟨ m∣m*n (gcd d n) ⟩
      k * gcd d n
        ≡˘⟨ d≡k*gcd[d,n] ⟩
      d
        ∎
    lem₄ : k ∣ gcd d m
    lem₄ = gcd-greatest lem₃ lem₂
    lem₅ : d ∣ gcd d m * gcd d n
    lem₅ = begin
      d
        ≡⟨ d≡k*gcd[d,n] ⟩
      k * gcd d n
        ∣⟨ *-monoˡ-∣ (gcd d n) lem₄ ⟩
      gcd d m * gcd d n
        ∎

gcd-split : ∀ m n d → Coprime m n → d ∣ m * n → d ≡ gcd d m * gcd d n
gcd-split m n d coprime d∣mn = ∣-antisym (gcd-split₂ m n d coprime d∣mn) (gcd-split₁ m n d coprime)

-- Definition of multiplicative function
Multiplicative : Pred (ℕ → ℕ) _
Multiplicative f = ∀ {m n} → Coprime m n → f (m * n) ≡ f m * f n

gcd-multʳ : ∀ k → Multiplicative (gcd k)
gcd-multʳ k {m} {n} coprime = sym (gcd-universality {k} {m * n} {gcd k m * gcd k n} forwards backwards)
  where
    open ∣-Reasoning
    forwards : ∀ {d} → d ∣ k × d ∣ m * n → d ∣ gcd k m * gcd k n
    forwards {d} (d∣k , d∣mn) = begin
      d
        ≡⟨ gcd-split m n d coprime d∣mn ⟩
      gcd d m * gcd d n
        ∣⟨ *-mono-∣ (gcd-monoˡ-∣ m d∣k) (gcd-monoˡ-∣ n d∣k) ⟩
      gcd k m * gcd k n
        ∎
    backwards : ∀ {d} → d ∣ gcd k m * gcd k n → d ∣ k × d ∣ m * n
    backwards d∣gg = ∣-trans d∣gg (gcd-split₁ m n k coprime) , ∣-trans d∣gg (*-mono-∣ (gcd[m,n]∣n k m) (gcd[m,n]∣n k n))

gcd-multˡ : ∀ k → Multiplicative (λ x → gcd x k)
gcd-multˡ k {m} {n} rewrite gcd-comm m k | gcd-comm n k | gcd-comm (m * n) k = gcd-multʳ k
