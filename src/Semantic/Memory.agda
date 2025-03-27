module Semantic.Memory {n} where

open import Data.Empty
open import Data.Fin
  hiding (_+_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Function
open import Relation.Binary.PropositionalEquality 

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.VariableSet {n}

-- State of the memory at a certain program point for the bracketed program.
Memory : Set _
Memory = Vec ℕ n

-- Update the value of a variable in memory.
infixl 6 _[_↦_]
_[_↦_] : Memory → Fin n → ℕ → Memory
m [ name ↦ v ] = m [ name ]≔ v

-- Semantic evaluation of expressions.
⟦_⟧ₑ : ASTExpS → Memory → ℕ
⟦ IntVal n ⟧ₑ m = n
⟦ Var v ⟧ₑ m = lookup m v
⟦ Add exp₁ exp₂ ⟧ₑ m = ⟦ exp₁ ⟧ₑ m + ⟦ exp₂ ⟧ₑ m

-- State of the memory at a certain program point for the transformed program.
Memoryₜ : Set _
Memoryₜ = Vec (List ℕ) n

lookupOrDefault : ℕ → List ℕ → ℕ
lookupOrDefault _ [] = 0
lookupOrDefault 0 (x ∷ xs) = x
lookupOrDefault (suc n) (x ∷ xs) = lookupOrDefault n xs

safeListUpdate : List ℕ → ℕ → ℕ → List ℕ
safeListUpdate [] _ _ = []
safeListUpdate (x ∷ xs) 0 v = v ∷ xs
safeListUpdate (x ∷ xs) (suc n) v = x ∷ (safeListUpdate xs n v)

-- Update the value of a variable in memory of the transformed program.
infixl 6 _[_↦_]ₜ
_[_↦_]ₜ : Memoryₜ → TransVariable → ℕ → Memoryₜ
m [ var , index ↦ v ]ₜ = 
  m [ var ]≔ (safeListUpdate (lookup m var) index v)

-- Semantic evaluation of tranformed expressions.
⟦_⟧ₜ : ASTExp → Memoryₜ → ℕ
⟦ INTVAL n ⟧ₜ m = n
⟦ VAR (var , index) ⟧ₜ m = lookupOrDefault index (lookup m var)       
⟦ ADD exp₁ exp₂ ⟧ₜ m = ⟦ exp₁ ⟧ₜ m + ⟦ exp₂ ⟧ₜ m

-- Lookup of a variable in a transformed memory.
lookupₜ : Memoryₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ A x = lookupOrDefault (lookup A x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set (Definition 2).
_==ₘ_-_ : Memory → Memoryₜ → 𝒜 → Set
m ==ₘ mₜ - A = ∀ x → lookup m x ≡ lookupₜ mₜ A x

-- Equality between two memory projections on active sets.
_-_==ₘₜ_-_ : Memoryₜ → 𝒜 → Memoryₜ → 𝒜 → Set
mₜ - A ==ₘₜ mₜ' - A' = ∀ x → lookupₜ mₜ A x ≡ lookupₜ mₜ' A' x

-- Transitive property between ==ₘ and ==ₘₜ.
==ₘ-trans : {m : Memory} {mₜ mₜ' : Memoryₜ} {A A' : 𝒜}
  → m ==ₘ mₜ - A
  → mₜ - A ==ₘₜ mₜ' - A'
  → m ==ₘ mₜ' - A'
==ₘ-trans meq meq' var = trans (meq var) (meq' var)   

-- MEMORY LOOKUP PROPERTIES
lookupx∘changex : 
  {X : Set} {m : ℕ} {v : X} (index : Fin m) (vector : Vec X m) 
  → lookup (vector [ index ]≔ v) index ≡ v
lookupx∘changex zero (head ∷ tail) = refl
lookupx∘changex (suc m) (head ∷ tail) = lookupx∘changex m tail 

lookupy∘changex : 
  {X : Set} {m : ℕ} {v : X} (i₁ i₂ : Fin m) (vector : Vec X m)
  → i₂ ≢  i₁
  → lookup (vector [ i₁ ]≔ v) i₂ ≡ lookup vector i₂
lookupy∘changex zero zero _ i₂<>i₁ = ⊥-elim (i₂<>i₁ refl)
lookupy∘changex zero (suc _) (_ ∷ _) _ = refl
lookupy∘changex (suc _) zero (_ ∷ _) _ = refl
lookupy∘changex (suc i₁') (suc i₂') (_ ∷ tail) i₂<>i₁ = lookupy∘changex i₁' i₂' tail (i₂<>i₁ ∘ cong suc)  

listLookupx∘listUpdatex : 
  {v : ℕ} (index : ℕ) (list : List ℕ) 
  → index <ₙ length list
  → lookupOrDefault index (safeListUpdate list index v) ≡ v
listLookupx∘listUpdatex _ [] i<0 = ⊥-elim (n≮0 i<0)
listLookupx∘listUpdatex 0 (_ ∷ _) _ = refl
listLookupx∘listUpdatex (suc index) (_ ∷ tail) si<ll = listLookupx∘listUpdatex index tail (<-pred si<ll)

lookupₜx∘changeₜx : 
  {m v var : ℕ} (index : Fin m) (vector : Vec (List ℕ) m) 
  → var <ₙ length (lookup vector index)
  → lookupOrDefault var (lookup (vector [ index ]≔ (safeListUpdate (lookup vector index) var v)) index) ≡ v
lookupₜx∘changeₜx {var = var} zero (head ∷ _) v<lh = listLookupx∘listUpdatex var head v<lh
lookupₜx∘changeₜx (suc index) (_ ∷ tail) v<lvi = lookupₜx∘changeₜx index tail v<lvi

lookupₜy∘changeₜx : 
  {m v var₁ var₂ : ℕ} (i₁ i₂ : Fin m) (vector : Vec (List ℕ) m) 
  → i₂ ≢  i₁
  → lookupOrDefault var₁ (lookup (vector [ i₁ ]≔ (safeListUpdate (lookup vector i₁) var₂ v)) i₂) ≡ lookupOrDefault var₁ (lookup vector i₂)
lookupₜy∘changeₜx zero zero _ i₂<>i₁ = ⊥-elim (i₂<>i₁ refl)
lookupₜy∘changeₜx zero (suc _) (_ ∷ _) _ = refl
lookupₜy∘changeₜx (suc _) zero (_ ∷ _) _ = refl
lookupₜy∘changeₜx (suc i₁') (suc i₂') (_ ∷ tail) i₂<>i₁ = lookupₜy∘changeₜx i₁' i₂' tail (i₂<>i₁ ∘ cong suc)  
