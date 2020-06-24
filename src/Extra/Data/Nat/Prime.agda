module Extra.Data.Nat.Prime where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Primality
open import Data.Nat.Divisibility
open import Data.Fin using (fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Sum
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

prime-div₁ : ∀ {p d} → Prime p → d ∣ p → d ≡ 1 ⊎ d ≡ p
prime-div₁ {suc p-1} {0} p-prime d∣p = contradiction (0∣⇒≡0 d∣p) 1+n≢0
prime-div₁ {suc p-1} {1} p-prime d∣p = inj₁ refl
prime-div₁ {p@(suc (suc p′))} {d@(suc (suc d′))} p-prime d∣p = inj₂ (≤-antisym d≤p (≮⇒≥ d≮p))
  where
    d≮p : d ≮ p
    d≮p (s≤s (s≤s d′<p′)) = (p-prime (fromℕ< d′<p′)) (subst (λ x → suc (suc x) ∣ p) (sym (toℕ-fromℕ< d′<p′)) d∣p)
    d≤p : d ≤ p
    d≤p = ∣⇒≤ d∣p

prime-div₂ : ∀ {p} → p > 1 → (∀ {d} → d ∣ p → d ≡ 1 ⊎ d ≡ p) → Prime p
prime-div₂ {suc (suc p′)} (s≤s _) hp i hi with hp hi
... | inj₂ (2+i≡p) = <-irrefl (suc-injective (suc-injective 2+i≡p)) (toℕ<n i)
