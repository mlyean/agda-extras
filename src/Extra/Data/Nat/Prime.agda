module Extra.Data.Nat.Prime where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Primality
open import Data.Nat.Divisibility
open import Data.Nat.Induction
import Data.Fin as Fin
import Data.Fin.Properties as Fin
open import Data.Sum
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

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

-- Definition of composite

Composite : Pred ℕ _
Composite n = n > 1 × ¬ Prime n

composite? : Decidable Composite
composite? n with n >? 1 | prime? n
... | no ¬n>1 | _         = no (λ z → ¬n>1 (proj₁ z))
... | _       | yes prime = no (λ z → proj₂ z prime)
... | yes n>1 | no ¬prime = yes (n>1 , ¬prime)

-- Properties of composite numbers

composite-div : ∀ {n} → Composite n → ∃[ d ] (1 < d × d < n × d ∣ n)
composite-div {n@(suc (suc n′))} (s≤s (s≤s _) , n-comp)
  with Fin.¬∀⟶∃¬ n′ (λ i → suc (suc (Fin.toℕ i)) ∤ n) (λ i → ¬? (_∣?_ (suc (suc (Fin.toℕ i))) n)) n-comp
... | d′ , ¬¬d∣n = d , s≤s (s≤s z≤n) , s≤s (s≤s (Fin.toℕ<n d′)) , decidable-stable (_∣?_ d n) ¬¬d∣n
  where
    d : ℕ
    d = suc (suc (Fin.toℕ d′))

prime∨comp : ∀ {n} → n > 1 → Prime n ⊎ Composite n
prime∨comp {n} n>1 with prime? n
... | yes prime = inj₁ prime
... | no prime = inj₂ (n>1 , prime)

private
  ∃p∣n′ : ∀ {n} → n > 1 → Acc _<_ n → ∃[ p ] (Prime p × p ∣ n)
  ∃p∣n′ {n} n>1 (acc rec) with prime∨comp n>1
  ... | inj₁ prime = n , prime , ∣-refl
  ... | inj₂ comp with composite-div comp
  ... | d , 1<d , d<n , d∣n with ∃p∣n′ 1<d (rec d d<n)
  ... | p , p-prime , p∣d = p , p-prime , ∣-trans p∣d d∣n

∃p∣n : ∀ {n} → n > 1 → ∃[ p ] (Prime p × p ∣ n)
∃p∣n {n} n>1 = ∃p∣n′ n>1 (<-wellFounded n)
