module Transformation.VariableSet {n} where

open import Agda.Builtin.Nat
  renaming (_<_ to _<ₙ_ ; _==_ to _==ₙ_)
open import Data.Bool.Base
open import Data.Nat
open import Data.Fin
open import Data.List.Base
open import Data.Product
open import Function.Base

-- A variable in a transformed program consists of a variable name (represented by a Fin n)
-- and a natural number subindex indicating its version in the active set in a certain program point.
TransVariable : Set _
TransVariable = Fin n × ℕ

-- We represent sets of variables with lists without repeated elements.
VariableSet : Set _
VariableSet = List TransVariable

-- Variable equality test.
_==ᵥ_ : TransVariable → TransVariable → Bool
(v₁ , i₁) ==ᵥ (v₂ , i₂) = (toℕ v₁ ==ₙ toℕ v₂) ∧ (i₁ ==ₙ i₂)

-- Element check.
_elemᵥₛ_ : TransVariable → VariableSet → Bool
_ elemᵥₛ [] = false
v₁ elemᵥₛ (v₂ ∷ vs) = (v₁ ==ᵥ v₂) ∨ (v₁ elemᵥₛ vs) 

-- Conversion from and to lists.
fromListᵥₛ : List TransVariable → VariableSet
fromListᵥₛ = foldr (λ v vs → if v elemᵥₛ vs then vs else v ∷ vs) [] 

toListᵥₛ : VariableSet → List TransVariable
toListᵥₛ = id

-- Empty set.
emptyᵥₛ : VariableSet
emptyᵥₛ = fromListᵥₛ []

-- Set size.
sizeᵥₛ : VariableSet → ℕ
sizeᵥₛ = length 

-- Singleton set.
singletonᵥₛ : TransVariable → VariableSet
singletonᵥₛ v = fromListᵥₛ (v ∷ [])

-- Element removal.
popᵥₛ : TransVariable → VariableSet → VariableSet
popᵥₛ _ [] = []
popᵥₛ v₁ (v₂ ∷ vs) = if v₁ ==ᵥ v₂ then vs else v₂ ∷ (popᵥₛ v₁ vs)

-- Operations between sets.
_unionᵥₛ_ : VariableSet → VariableSet → VariableSet
vs₁ unionᵥₛ vs₂ = fromListᵥₛ (toListᵥₛ vs₁ ++ toListᵥₛ vs₂)

_diffᵥₛ_ : VariableSet → VariableSet → VariableSet
vs diffᵥₛ [] = vs
vs₁ diffᵥₛ (v ∷ vs₂) = (popᵥₛ v vs₁) diffᵥₛ vs₂

-- Set comparisons.
_subsetᵥₛ_ : VariableSet → VariableSet → Bool
[] subsetᵥₛ _ = true
(v ∷ vs₁) subsetᵥₛ vs₂ = (v elemᵥₛ vs₂) ∧ (vs₁ subsetᵥₛ vs₂)

_strictSubsetᵥₛ_ : VariableSet → VariableSet → Bool
vs₁ strictSubsetᵥₛ vs₂ = (sizeᵥₛ vs₁ <ₙ sizeᵥₛ vs₂) ∧ (vs₁ subsetᵥₛ vs₂)

_==ᵥₛ_ : VariableSet → VariableSet → Bool
vs₁ ==ᵥₛ vs₂ = (sizeᵥₛ vs₁ ==ₙ sizeᵥₛ vs₂) ∧ (vs₁ subsetᵥₛ vs₂) 