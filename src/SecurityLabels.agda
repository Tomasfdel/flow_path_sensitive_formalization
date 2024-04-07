module SecurityLabels {n} where

open import AST {n}

-- TODO: Implement this as a lattice later.
data SecurityLevel : Set where
    Low : SecurityLevel
    High : SecurityLevel

-- TODO: What are proper names for the operators?
data SecurityLabel : Set where
    Label : SecurityLevel → SecurityLabel
    ExpTest : ASTExp → SecurityLabel → SecurityLabel → SecurityLabel
    Meet : SecurityLabel → SecurityLabel → SecurityLabel
    Join : SecurityLabel → SecurityLabel → SecurityLabel

-- TODO: This is not correct, for now I'm leaving it as is because I need a definition
-- but ideally this would be something like a Map from Fin n × ℕ to SecurityLabel.
TypingEnvironment : Set _
TypingEnvironment = SecurityLabel 