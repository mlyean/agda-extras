module Extra.Data.Nat.Factorial where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Relation.Binary

_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * (n !)

n!>0 : ∀ (n : ℕ) → n ! > 0
n!>0 zero = s≤s z≤n
n!>0 (suc n) = ≤-trans (n!>0 n) (m≤m+n (n !) (n * (n !)))

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
