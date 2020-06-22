module Extra.Data.Nat.Binomial where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import Extra.Data.Nat.Properties
open import Extra.Data.Nat.Factorial

_C_ : ℕ → ℕ → ℕ
n C zero = 1
zero C suc k = 0
suc n C suc k = n C k + n C (suc k)

n<k⇒nCk≡0 : ∀ (n k : ℕ) → n < k → n C k ≡ 0
n<k⇒nCk≡0 zero (suc k) n<k = refl
n<k⇒nCk≡0 (suc n) (suc k) (s≤s n<k) rewrite n<k⇒nCk≡0 n k n<k | n<k⇒nCk≡0 n (suc k) (≤-step n<k) = refl

nC1+n≡0 : ∀ (n : ℕ) → n C (suc n) ≡ 0
nC1+n≡0 n = n<k⇒nCk≡0 n (suc n) (n<1+n n)

nCn≡1 : ∀ (n : ℕ) → n C n ≡ 1
nCn≡1 zero = refl
nCn≡1 (suc n) rewrite nCn≡1 n | nC1+n≡0 n = refl

nC1≡n : ∀ (n : ℕ) → n C 1 ≡ n
nC1≡n zero = refl
nC1≡n (suc n) rewrite nC1≡n n = refl

k≤n⇒nCk>0 : ∀ (n k : ℕ) → k ≤ n → n C k > 0
k≤n⇒nCk>0 n 0 z≤n = s≤s z≤n
k≤n⇒nCk>0 (suc n) (suc k) (s≤s k≤n) = ≤-trans (k≤n⇒nCk>0 n k k≤n) (m≤m+n (n C k) (n C suc k))

sCs : ∀ (n k : ℕ) → (suc n C suc k) * suc k ≡ suc n * (n C k)
sCs n zero rewrite nC1≡n n = refl
sCs zero (suc k) = refl
sCs (suc n) (suc k) = begin
  ((2 + n) C (2 + k)) * (2 + k)
    ≡⟨⟩
  ((1 + n) C (1 + k) + (1 + n) C (2 + k)) * (2 + k)
    ≡⟨ *-distribʳ-+ (2 + k) ((1 + n) C (1 + k)) ((1 + n) C (2 + k)) ⟩
  (1 + n) C (1 + k) * (2 + k) + (1 + n) C (2 + k) * (2 + k)
    ≡⟨ cong₂ _+_ (*-suc ((1 + n) C (1 + k)) (1 + k)) (sCs n (1 + k)) ⟩
  (1 + n) C (1 + k) + (1 + n) C (1 + k) * (1 + k) + (1 + n) * n C (1 + k)
    ≡⟨ cong (λ x → (1 + n) C (1 + k) + x + (1 + n) * n C (1 + k)) (sCs n k) ⟩
  (1 + n) C (1 + k) + (1 + n) * (n C k) + (1 + n) * n C (1 + k)
    ≡⟨ +-assoc ((1 + n) C (1 + k)) ((1 + n) * (n C k)) ((1 + n) * n C (1 + k)) ⟩
  (1 + n) C (1 + k) + ((1 + n) * (n C k) + (1 + n) * n C (1 + k))
    ≡˘⟨ cong ((1 + n) C (1 + k) +_) (*-distribˡ-+ (1 + n) (n C k) (n C (1 + k))) ⟩
  (1 + n) C (1 + k) + (1 + n) * ((n C k) + n C (1 + k))
    ≡⟨⟩
  (2 + n) * ((1 + n) C (1 + k))
    ∎
  where
    open ≡-Reasoning

C-! : ∀ (m n : ℕ) → (m + n) C m * m ! * n ! ≡ (m + n) !
C-! zero n = +-identityʳ (n !)
C-! (suc m) n = begin
  (1 + m + n) C (1 + m) * (1 + m) ! * n !
    ≡⟨⟩
  (1 + m + n) C (1 + m) * ((1 + m) * m !) * n !
    ≡˘⟨ cong (_* n !) (*-assoc ((1 + m + n) C (1 + m)) (1 + m) (m !)) ⟩
  (1 + m + n) C (1 + m) * (1 + m) * m ! * n !
    ≡⟨ cong (λ x → x * m ! * n !) (sCs (m + n) m) ⟩
  (1 + m + n) * ((m + n) C m) * m ! * n !
    ≡⟨ cong (_* n !) (*-assoc (1 + m + n) ((m + n) C m) (m !)) ⟩
  (1 + m + n) * ((m + n) C m * m !) * n !
    ≡⟨ *-assoc (1 + m + n) ((m + n) C m * m !) (n !) ⟩
  (1 + m + n) * (((m + n) C m) * m ! * n !)
    ≡⟨ cong ((1 + m + n) *_) (C-! m n) ⟩
  (1 + m + n) !
    ∎
  where
    open ≡-Reasoning

private
  m!*n!≢0 : ∀ (m n : ℕ) → (m !) * (n !) ≢ 0
  m!*n!≢0 m n = m≢0∧n≢0⇒m*n≢0 (n!≢0 m) (n!≢0 n)

  m!*n!≢0′ : ∀ (m n : ℕ) → False ((m !) * (n !) ≟ 0)
  m!*n!≢0′ m n = fromWitnessFalse (m!*n!≢0 m n)

  m*n%n≡0′ : ∀ (m n : ℕ) → (≢0 : n ≢ 0) → ((m * n) % n) {fromWitnessFalse ≢0} ≡ 0
  m*n%n≡0′ m zero n≢0 = contradiction refl n≢0
  m*n%n≡0′ m (suc n) n≢0 = m*n%n≡0 m n

C-!-div : ∀ (m n : ℕ) → (m + n) C m ≡ ((m + n) !) / (m ! * n !)
C-!-div m n rewrite sym (C-! m n) | *-assoc ((m + n) C m) (m !) (n !) = sym (m*n/n≡m ((m + n) C m) ((m !) * (n !)) {m!*n!≢0′ m n})

C-!-mod : ∀ (m n : ℕ) → ((m + n) !) % (m ! * n !) ≡ 0
C-!-mod m n rewrite sym (C-! m n) | *-assoc ((m + n) C m) (m !) (n !) = m*n%n≡0′ ((m + n) C m) ((m !) * (n !)) (m!*n!≢0 m n)

+-C-sym : ∀ (m n : ℕ) → (m + n) C n ≡ (m + n) C m
+-C-sym m zero rewrite +-identityʳ m = sym (nCn≡1 m)
+-C-sym zero n = nCn≡1 n
+-C-sym (suc m) (suc n) = begin
  (m + (1 + n)) C n + (m + (1 + n)) C (1 + n)
    ≡⟨ cong (λ x → x C n + ((m + (1 + n)) C (1 + n))) (+-suc m n) ⟩
  (1 + m + n) C n + (m + (1 + n)) C (1 + n)
    ≡⟨ cong₂ _+_ (+-C-sym (suc m) n) (+-C-sym m (suc n)) ⟩
  (1 + m + n) C (1 + m) + (m + (1 + n)) C m
    ≡˘⟨ cong (λ x → x C (1 + m) + (m + (1 + n)) C m) (+-suc m n) ⟩
  (m + (1 + n)) C (1 + m) + (m + (1 + n)) C m
    ≡⟨ +-comm ((m + (1 + n)) C (1 + m)) ((m + (1 + n)) C m) ⟩
  (m + (1 + n)) C m + (m + (1 + n)) C (1 + m)
    ∎
  where
    open ≡-Reasoning
