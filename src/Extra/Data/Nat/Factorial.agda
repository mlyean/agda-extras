module Extra.Data.Nat.Factorial where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Extra.Data.Nat.Properties

_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * (n !)

n!>0 : ∀ (n : ℕ) → n ! > 0
n!>0 zero = s≤s z≤n
n!>0 (suc n) = ≤-trans (n!>0 n) (m≤m+n (n !) (n * (n !)))

n!≢0 : ∀ (n : ℕ) → n ! ≢ 0
n!≢0 n = m<n⇒n≢0 (n!>0 n)

m≤‴n⇒m!∣n! : _! Preserves _≤‴_ ⟶ _∣_
m≤‴n⇒m!∣n! ≤‴-refl = ∣-refl
m≤‴n⇒m!∣n! {m} (≤‴-step x) = ∣-trans (n∣m*n (suc m)) (m≤‴n⇒m!∣n! x)

m≤n⇒m!∣n! : _! Preserves _≤_ ⟶ _∣_
m≤n⇒m!∣n! {m} {n} m≤n = m≤‴n⇒m!∣n! (≤″⇒≤‴ (≤⇒≤″ m≤n))

m≤n⇒m∣n! : ∀ (m n : ℕ) → m > 0 → m ≤ n → m ∣ n !
m≤n⇒m∣n! (suc m) n _ 1+m≤n = ∣-trans (m∣m*n (m !)) (m≤n⇒m!∣n! 1+m≤n)

!-mono-≤ : _! Preserves _≤_ ⟶ _≤_
!-mono-≤ {m} {n} m≤n with n ! | n!>0 n | m≤n⇒m!∣n! m≤n
... | (suc x) | _ | h = ∣⇒≤ {m !} {x} h

!-mono-< : ∀ {m n} → 1 ≤ m → m < n → m ! < n !
!-mono-< {1} {2} 1≤m (s≤s (s≤s z≤n)) = s≤s 1≤m
!-mono-< {1} {suc (suc (suc n))} 1≤m (s≤s (s≤s z≤n)) = begin-strict
  1
    <⟨ !-mono-< {1} {2 + n} 1≤m (s≤s (s≤s z≤n)) ⟩
  (2 + n) !
    ≤⟨ n≤m*n {3 + n} _ 0<1+n ⟩
  (3 + n) * (2 + n) !
    ≡⟨⟩
  (3 + n) !
    ∎
  where
    open ≤-Reasoning
!-mono-< {suc (suc m)} {(suc (suc (suc n)))} _ (s≤s (s≤s (s≤s m≤n))) =
  *-mono-< (s≤s (s≤s (s≤s m≤n))) (!-mono-< {1 + m} {2 + n} 0<1+n (s≤s (s≤s m≤n)))

n>1⇒n!>1 : ∀ {n} → n > 1 → n ! > 1
n>1⇒n!>1 {n} n>1 = !-mono-< {1} {n} ≤-refl n>1
