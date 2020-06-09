module Extra.Data.Nat.Properties where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

^-monoˡ-≤ : ∀ k → (_^ k) Preserves _≤_ ⟶ _≤_
^-monoˡ-≤ zero _ = ≤-refl
^-monoˡ-≤ (suc k) m≤n = *-mono-≤ m≤n (^-monoˡ-≤ k m≤n)

^-monoˡ-< : ∀ k → (k > 0) → (_^ k) Preserves _<_ ⟶ _<_
^-monoˡ-< (suc zero) _ {m} {n} m<n rewrite *-identityʳ m | *-identityʳ n = m<n
^-monoˡ-< (suc (suc k)) _ m<n = *-mono-< m<n (^-monoˡ-< (suc k) 0<1+n m<n)

^-monoʳ-≤ : ∀ k → (k > 0) → (k ^_) Preserves _≤_ ⟶ _≤_
^-monoʳ-≤ (suc k) _ {0} {zero} z≤n = ≤-refl
^-monoʳ-≤ (suc k) _ {0} {suc n} z≤n = ≤-trans (^-monoʳ-≤ (suc k) 0<1+n {0} {n} z≤n) (m≤m+n (suc k ^ n) (k * (suc k ^ n)))
^-monoʳ-≤ (suc k) _ {suc m} {suc n} (s≤s m≤n) = *-monoʳ-≤ (suc k) (^-monoʳ-≤ (suc k) 0<1+n {m} {n} m≤n)

m^k≤n^k⇒m≤n : (k : ℕ) → (k > 0) → ∀ {m n : ℕ} → m ^ k ≤ n ^ k → m ≤ n
m^k≤n^k⇒m≤n k k>0 {m} {n} m^k≤n^k = ≮⇒≥ λ n<m → ≤⇒≯ m^k≤n^k (^-monoˡ-< k k>0 n<m)

m≢0∧n≢0⇒m*n≢0 : ∀ {m n : ℕ} → m ≢ 0 → n ≢ 0 → m * n ≢ 0
m≢0∧n≢0⇒m*n≢0 {m} m≢0 n≢0 m*n≡0 = [ m≢0 , n≢0 ] (m*n≡0⇒m≡0∨n≡0 m m*n≡0)
