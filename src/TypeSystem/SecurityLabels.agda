module TypeSystem.SecurityLabels {n} where

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

-- TODO(minor): This is not correct, for now I'm leaving it as is because I need a definition
-- but ideally this would be something like a Map from TransVariable to SecurityLabel.
TypingEnvironment : Set _
TypingEnvironment = SecurityLabel 

-- TODO(minor): Same as above
findType : TypingEnvironment → TransVariable → SecurityLabel
findType Γ _ = Γ