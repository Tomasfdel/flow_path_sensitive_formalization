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
⟦ Var name ⟧ₑ m = lookup m name
⟦ Add exp exp' ⟧ₑ m = ⟦ exp ⟧ₑ m + ⟦ exp' ⟧ₑ m

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
m [ (name , index) ↦ v ]ₜ = 
  m [ name ]≔ (safeListUpdate (lookup m name) index v)

-- Semantic evaluation of tranformed expressions.
⟦_⟧ₜ : ASTExp → Memoryₜ → ℕ
⟦ INTVAL n ⟧ₜ m = n
⟦ VAR (name , index) ⟧ₜ m = lookupOrDefault index (lookup m name)       
⟦ ADD exp exp' ⟧ₜ m = ⟦ exp ⟧ₜ m + ⟦ exp' ⟧ₜ m

-- Lookup of a variable in a transformed memory.
lookupₜ : Memoryₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ active x = lookupOrDefault (lookup active x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set.
_==ₘ_-_ : Memory → Memoryₜ → 𝒜 → Set
m ==ₘ mₜ - active = ∀ x → lookup m x ≡ lookupₜ mₜ active x

-- Equality between two memory projections on active sets.
_-_==ₘₜ_-_ : Memoryₜ → 𝒜 → Memoryₜ → 𝒜 → Set
m1ₜ - a1 ==ₘₜ m2ₜ - a2 = ∀ x → lookupₜ m1ₜ a1 x ≡ lookupₜ m2ₜ a2 x

-- Transitive property between ==ₘ and ==ₘₜ .
==ₘ-trans : {m : Memory} {mₜ mₜ' : Memoryₜ} {a a' : 𝒜}
  → m ==ₘ mₜ - a
  → mₜ - a ==ₘₜ mₜ' - a'
  → m ==ₘ mₜ' - a'
==ₘ-trans meq meq2 var = trans (meq var) (meq2 var)   

-- MEMORY LOOKUP PROPERTIES
lookupx∘changex : 
  {A : Set} {m : ℕ} {v : A} (index : Fin m) (vector : Vec A m) 
  → lookup (vector [ index ]≔ v) index ≡ v
lookupx∘changex zero (head ∷ tail) = refl
lookupx∘changex (suc x) (head ∷ tail) = lookupx∘changex x tail 

lookupy∘changex : 
  {A : Set} {m : ℕ} {v : A} (i1 i2 : Fin m) (vector : Vec A m)
  → i2 ≢  i1
  → lookup (vector [ i1 ]≔ v) i2 ≡ lookup vector i2
lookupy∘changex zero zero vector i2!=i1 = ⊥-elim (i2!=i1 refl)
lookupy∘changex zero (suc x) (head ∷ tail) i2!=i1 = refl
lookupy∘changex (suc x) zero (head ∷ tail) i2!=i1 = refl
lookupy∘changex (suc x) (suc y) (head ∷ tail) i2!=i1 = lookupy∘changex x y tail (i2!=i1 ∘ cong suc)  

listLookupx∘listUpdatex : 
  {v : ℕ} (index : ℕ) (list : List ℕ) 
  → index <ₙ length list
  → lookupOrDefault index (safeListUpdate list index v) ≡ v
listLookupx∘listUpdatex index [] i<0 = ⊥-elim (n≮0 i<0)
listLookupx∘listUpdatex 0 (head ∷ tail) _ = refl
listLookupx∘listUpdatex (suc index) (head ∷ tail) si<ll = listLookupx∘listUpdatex index tail (<-pred si<ll)

lookupₜx∘changeₜx : 
  {m v activeVar : ℕ} (index : Fin m) (vector : Vec (List ℕ) m) 
  → activeVar <ₙ length (lookup vector index)
  → lookupOrDefault activeVar (lookup (vector [ index ]≔ (safeListUpdate (lookup vector index) activeVar v)) index) ≡ v
lookupₜx∘changeₜx {_} {_} {activeVar} zero (head ∷ tail) aV<lh = listLookupx∘listUpdatex activeVar head aV<lh
lookupₜx∘changeₜx (suc x) (head ∷ tail) aV<liv = lookupₜx∘changeₜx x tail aV<liv

lookupₜy∘changeₜx : 
  {m v activeVar activeVar2 : ℕ} (i1 i2 : Fin m) (vector : Vec (List ℕ) m) 
  → i2 ≢  i1
  → lookupOrDefault activeVar (lookup (vector [ i1 ]≔ (safeListUpdate (lookup vector i1) activeVar2 v)) i2) ≡ lookupOrDefault activeVar (lookup vector i2)
lookupₜy∘changeₜx zero zero vector i2!=i1 = ⊥-elim (i2!=i1 refl)
lookupₜy∘changeₜx zero (suc x) (head ∷ tail) i2!=i1 = refl
lookupₜy∘changeₜx (suc x) zero (head ∷ tail) i2!=i1 = refl
lookupₜy∘changeₜx (suc x) (suc y) (head ∷ tail) i2!=i1 = lookupₜy∘changeₜx x y tail (i2!=i1 ∘ cong suc)  
