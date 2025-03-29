module TypeSystem.SecurityLabels {n} where

open import Data.List.Base
  hiding (lookup)
open import Data.Nat
open import Data.Product
open import Data.Vec.Base

open import Transformation.AST {n}
open import Transformation.VariableSet {n}

data SecurityLevel : Set where
    Low : SecurityLevel
    High : SecurityLevel

data SecurityLabel : Set where
    Label : SecurityLevel → SecurityLabel
    ExpTest : ASTExp → SecurityLabel → SecurityLabel → SecurityLabel
    Meet : SecurityLabel → SecurityLabel → SecurityLabel
    Join : SecurityLabel → SecurityLabel → SecurityLabel

-- Returns all the free variables of a SecurityLabel.
labelVariables : SecurityLabel → VariableSet
labelVariables (Label _) = emptyᵥₛ
labelVariables (ExpTest exp l₁ l₂) = 
    ((expressionVariables exp) unionᵥₛ (labelVariables l₁)) unionᵥₛ (labelVariables l₂)
labelVariables (Meet l₁ l₂) = (labelVariables l₁) unionᵥₛ (labelVariables l₂)
labelVariables (Join l₁ l₂) = (labelVariables l₁) unionᵥₛ (labelVariables l₂)

-- A TypingEnvironment is a mapping from TransVariables to SecurityLabels.
TypingEnvironment : Set _
TypingEnvironment = Vec (List SecurityLabel) n 

lookupLabel : List SecurityLabel → ℕ → SecurityLabel
lookupLabel [] _ = Label Low
lookupLabel (x ∷ xs) zero = x
lookupLabel (x ∷ xs) (suc n) = lookupLabel xs n

findType : TypingEnvironment → TransVariable → SecurityLabel
findType Γ (v , index) = lookupLabel (lookup Γ v) index