module TypeSystem.SecurityLabels {n} where

open import Data.List.Base
  hiding (lookup)
open import Data.Nat
open import Data.Product
open import Data.Vec.Base

open import Transformation.AST {n}
open import Transformation.VariableSet {n}

-- TODO(minor): Maybe implement this as a lattice later.
data SecurityLevel : Set where
    Low : SecurityLevel
    High : SecurityLevel

data SecurityLabel : Set where
    Label : SecurityLevel → SecurityLabel
    ExpTest : ASTExp → SecurityLabel → SecurityLabel → SecurityLabel
    Meet : SecurityLabel → SecurityLabel → SecurityLabel
    Join : SecurityLabel → SecurityLabel → SecurityLabel

labelVariables : SecurityLabel → VariableSet
labelVariables (Label _) = emptyᵥₛ
labelVariables (ExpTest exp l1 l2) = 
    ((expressionVariables exp) unionᵥₛ (labelVariables l1)) unionᵥₛ (labelVariables l2)
labelVariables (Meet l1 l2) = (labelVariables l1) unionᵥₛ (labelVariables l2)
labelVariables (Join l1 l2) = (labelVariables l1) unionᵥₛ (labelVariables l2)

TypingEnvironment : Set _
TypingEnvironment = Vec (List SecurityLabel) n 

lookupType : List SecurityLabel → ℕ → SecurityLabel
lookupType [] _ = Label Low
lookupType (x ∷ xs) zero = x
lookupType (x ∷ xs) (suc n) = lookupType xs n

findType : TypingEnvironment → TransVariable → SecurityLabel
findType Γ (v , index) = lookupType (lookup Γ v) index