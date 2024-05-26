module VariableSet {n} where

open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Nat
open import Data.Fin
open import Data.List.Base
open import Data.Product
open import Function.Base

-- TODO(minor): Placeholder implementation with lists. I should try to implement it with AVL Sets later.

VariableSet : Set _
VariableSet = List (Fin n × ℕ)

_==ᵥ_ : Fin n × ℕ → Fin n × ℕ → Bool
(f1 , n1) ==ᵥ (f2 , n2) = (toℕ f1 == toℕ f2) ∧ (n1 == n2)

elemᵥₛ : Fin n × ℕ → VariableSet → Bool
elemᵥₛ _ [] = false
elemᵥₛ v1 (v2 ∷ vs) = (v1 ==ᵥ v2) ∨ (elemᵥₛ v1 vs) 

fromListᵥₛ : List (Fin n × ℕ) → VariableSet
fromListᵥₛ = foldr (\elem vs → if elemᵥₛ elem vs then vs else elem ∷ vs) [] 

toListᵥₛ : VariableSet → List (Fin n × ℕ)
toListᵥₛ = id

emptyᵥₛ : VariableSet
emptyᵥₛ = fromListᵥₛ []

_unionᵥₛ_ : VariableSet → VariableSet → VariableSet
vs1 unionᵥₛ vs2 = fromListᵥₛ (toListᵥₛ vs1 ++ toListᵥₛ vs2)

popᵥₛ : Fin n × ℕ → VariableSet → VariableSet
popᵥₛ _ [] = []
popᵥₛ v1 (v2 ∷ vs) = if v1 ==ᵥ v2 then vs else v2 ∷ (popᵥₛ v1 vs)

_diffᵥₛ_ : VariableSet → VariableSet → VariableSet
vs diffᵥₛ [] = vs
vs diffᵥₛ (x ∷ xs) = (popᵥₛ x vs) diffᵥₛ xs
