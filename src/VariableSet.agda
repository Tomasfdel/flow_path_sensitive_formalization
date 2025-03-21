module VariableSet {n} where

open import Agda.Builtin.Nat
  renaming (_<_ to _<ₙ_)
open import Data.Bool.Base
open import Data.Nat
open import Data.Fin
open import Data.List.Base
open import Data.Product
open import Function.Base

TransVariable : Set _
TransVariable = Fin n × ℕ

VariableSet : Set _
VariableSet = List TransVariable

-- Variable equality.
_==ᵥ_ : TransVariable → TransVariable → Bool
(f1 , n1) ==ᵥ (f2 , n2) = (toℕ f1 == toℕ f2) ∧ (n1 == n2)

-- Element check.
_elemᵥₛ_ : TransVariable → VariableSet → Bool
_ elemᵥₛ [] = false
v1 elemᵥₛ (v2 ∷ vs) = (v1 ==ᵥ v2) ∨ (v1 elemᵥₛ vs) 

-- Conversion from and to lists.
fromListᵥₛ : List TransVariable → VariableSet
fromListᵥₛ = foldr (\elem vs → if elem elemᵥₛ vs then vs else elem ∷ vs) [] 

toListᵥₛ : VariableSet → List TransVariable
toListᵥₛ = id

-- Empty set.
emptyᵥₛ : VariableSet
emptyᵥₛ = fromListᵥₛ []

-- Basic set constructors.
sizeᵥₛ : VariableSet → ℕ
sizeᵥₛ = length 

singletonᵥₛ : TransVariable → VariableSet
singletonᵥₛ x = fromListᵥₛ (x ∷ [])

-- Element removal.
popᵥₛ : TransVariable → VariableSet → VariableSet
popᵥₛ _ [] = []
popᵥₛ v1 (v2 ∷ vs) = if v1 ==ᵥ v2 then vs else v2 ∷ (popᵥₛ v1 vs)

-- Operations between sets.
_unionᵥₛ_ : VariableSet → VariableSet → VariableSet
vs1 unionᵥₛ vs2 = fromListᵥₛ (toListᵥₛ vs1 ++ toListᵥₛ vs2)

_diffᵥₛ_ : VariableSet → VariableSet → VariableSet
vs diffᵥₛ [] = vs
vs diffᵥₛ (x ∷ xs) = (popᵥₛ x vs) diffᵥₛ xs

-- Set comparisons.
_subsetᵥₛ_ : VariableSet → VariableSet → Bool
[] subsetᵥₛ _ = true
(x ∷ xs) subsetᵥₛ ys = (x elemᵥₛ ys) ∧ (xs subsetᵥₛ ys)

_strictSubsetᵥₛ_ : VariableSet → VariableSet → Bool
x strictSubsetᵥₛ y = (sizeᵥₛ x <ₙ sizeᵥₛ y) ∧ (x subsetᵥₛ y)

_==ᵥₛ_ : VariableSet → VariableSet → Bool
x ==ᵥₛ y = (sizeᵥₛ x == sizeᵥₛ y) ∧ (x subsetᵥₛ y) 