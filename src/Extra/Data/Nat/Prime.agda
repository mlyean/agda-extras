module Extra.Data.Nat.Prime where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Primality using (Prime; prime?)
open import Data.Nat.Divisibility
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.InfinitelyOften using (Inf)
import Data.Fin as Fin
import Data.Fin.Properties as Fin
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (¬?; contradiction; decidable-stable)

open import Extra.Data.Nat.Divisibility
open import Extra.Data.Nat.Factorial

-- Equivalent definitions of a prime

prime-div₁ : ∀ {p}
           → Prime p
           → ∀ {d} → d ∣ p → d ≡ 1 ⊎ d ≡ p
prime-div₁ {suc p-1} p-prime {0} d∣p = contradiction (0∣⇒≡0 d∣p) 1+n≢0
prime-div₁ {suc p-1} p-prime {1} d∣p = inj₁ refl
prime-div₁ {p@(suc (suc p′))} p-prime {d@(suc (suc d′))} d∣p = inj₂ (≤-antisym d≤p (≮⇒≥ d≮p))
  where
    d≮p : d ≮ p
    d≮p (s≤s (s≤s d′<p′)) = (p-prime (Fin.fromℕ< d′<p′)) (subst (λ x → suc (suc x) ∣ p) (sym (Fin.toℕ-fromℕ< d′<p′)) d∣p)
    d≤p : d ≤ p
    d≤p = ∣⇒≤ d∣p

prime-div₂ : ∀ {p}
           → p > 1
           → (∀ {d} → d ∣ p → d ≡ 1 ⊎ d ≡ p)
           → Prime p
prime-div₂ {suc (suc p′)} (s≤s _) hp i hi with hp hi
... | inj₂ (2+i≡p) = <-irrefl (suc-injective (suc-injective 2+i≡p)) (Fin.toℕ<n i)

-- Properties of prime numbers

p>1 : ∀ {p} → Prime p → p > 1
p>1 {suc (suc p)} _ = s≤s (s≤s z≤n)

p>0 : ∀ {p} → Prime p → p > 0
p>0 prime = <-trans (s≤s z≤n) (p>1 prime)

p∤1 : ∀ {p} → Prime p → p ∤ 1
p∤1 {p} prime p∣1 rewrite ∣1⇒≡1 p∣1 = prime

-- Definition of composite

Composite : ℕ → Set
Composite 0 = ⊥
Composite 1 = ⊥
Composite (suc (suc n)) = ∃[ d ] (2 + Fin.toℕ {n} d ∣ 2 + n)

module Composite where
  div : ∀ {n} → Composite n → ℕ
  div {suc (suc n)} composite = 2 + Fin.toℕ {n} (proj₁ composite)

  div∣n : ∀ {n} → (cn : Composite n) → div cn ∣ n
  div∣n {suc (suc n)} = proj₂

  div>1 : ∀ {n} → (cn : Composite n) → div cn > 1
  div>1 {suc (suc n)} cn = s≤s (s≤s z≤n)

  div<n : ∀ {n} → (cn : Composite n) → div cn < n
  div<n {suc (suc n)} cn = s≤s (s≤s (Fin.toℕ<n (proj₁ cn)))

open Composite

composite? : Decidable Composite
composite? 0 = no λ()
composite? 1 = no λ()
composite? (suc (suc n)) = Fin.any? (λ d → (2 + Fin.toℕ d) ∣? 2 + n)

prime⇒¬composite : ∀ {n} → Prime n → ¬ Composite n
prime⇒¬composite {suc (suc n)} prime (d , d∣n) = prime d d∣n

¬prime⇒composite : ∀ {n} → n > 1 → ¬ Prime n → Composite n
¬prime⇒composite {suc (suc n)} (s≤s _) prime with Fin.¬∀⟶∃¬ n _ (λ x → ¬? (_ ∣? _)) prime
... | d , d∣n = d , decidable-stable (_ ∣? _) d∣n

prime∨comp : ∀ {n} → n > 1 → Prime n ⊎ Composite n
prime∨comp {n} n>1 with prime? n
... | yes p = inj₁ p
... | no ¬p = inj₂ (¬prime⇒composite n>1 ¬p)

∃p∣n : ∀ {n} → n > 1 → ∃[ p ] (Prime p × p ∣ n)
∃p∣n {n} n>1 = ∃p∣n′ n>1 (<-wellFounded n)
  where
    ∃p∣n′ : ∀ {n} → n > 1 → Acc _<_ n → ∃[ p ] (Prime p × p ∣ n)
    ∃p∣n′ {n} n>1 (acc rec) with prime∨comp n>1
    ... | inj₁ prime = n , prime , ∣-refl
    ... | inj₂ comp with ∃p∣n′ (div>1 comp) (rec (div comp) (div<n comp))
    ... | p , p-prime , p∣d = p , p-prime , ∣-trans p∣d (div∣n comp)

inf-primes : Inf Prime
inf-primes (0 , h) = h 2 z≤n (λ ())
inf-primes (suc n , h) with ∃p∣n (s≤s (n!>0 n))
... | p , p-prime , p∣1+n! = h p (≰⇒> lem₃) p-prime
  where
    lem₁ : p ≤ n → p ∣ n !
    lem₁ p≤n = m≤n⇒m∣n! p n (p>0 p-prime) p≤n
    lem₂ : p ≤ n → p ∣ 1
    lem₂ p≤n = ∣m+n∣n⇒∣m p∣1+n! (lem₁ p≤n)
    lem₃ : p ≰ n
    lem₃ p≤n = p∤1 p-prime (lem₂ p≤n)
