module Extra.Data.Nat.Divisibility where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

*-mono-∣ : _*_ Preserves₂ _∣_ ⟶ _∣_ ⟶ _∣_
*-mono-∣ {m} {h} {n} {k} m∣h n∣k = ∣-trans (*-monoˡ-∣ n m∣h) (*-monoʳ-∣ h n∣k)

n∣m⇒n∣m%n : ∀ m n {≢0 : False (n ≟ 0)} → n ∣ m → n ∣ ((m % n) {≢0})
n∣m⇒n∣m%n m n@(suc n′) n∣m = m%n≡0⇒n∣m (m % n) n′ (trans (m%n%n≡m%n m n′) (n∣m⇒m%n≡0 m n′ n∣m))

n∣m%n⇒n∣m : ∀ m n {≢0 : False (n ≟ 0)} → n ∣ ((m % n) {≢0}) → n ∣ m
n∣m%n⇒n∣m m n@(suc n′) n∣m%n = m%n≡0⇒n∣m m n′ (trans (sym (m%n%n≡m%n m n′)) (n∣m⇒m%n≡0 (m % n) n′ n∣m%n))

∣m+n∣n⇒∣m : ∀ {i m n} → i ∣ m + n → i ∣ n → i ∣ m
∣m+n∣n⇒∣m {i} {m} {n} rewrite +-comm m n = ∣m+n∣m⇒∣n
