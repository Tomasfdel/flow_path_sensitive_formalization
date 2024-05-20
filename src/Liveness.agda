module Liveness {n} where

open import Data.Fin 
open import Data.List.Base
open import Data.Nat
open import Data.Product 
open import Data.Vec.Base

open import AST {n}
open import NonRepeatingCollection
open import Transformation {n}

VariableSet : Set _
VariableSet = NonRepeatingCollection (Fin n × ℕ)

activeSetToNRC : 𝒜 → VariableSet
activeSetToNRC activeSet = listToNRC (toList (Data.Vec.Base.zip (Data.Vec.Base.allFin (Data.Vec.Base.length activeSet)) activeSet))

statementKill : {t : ℕ} → ASTStmId {t} → VariableSet
statementKill (ASSIGN variableName _ _) = listToNRC (variableName ∷ [])
statementKill _ = listToNRC []

-- TODO: This implementation is incomplete. I still need to add the set of free variables from the variable's security type
-- following the description from Figure 9 of the paper.
expressionGen : ASTExp → VariableSet
expressionGen (INTVAL _) = listToNRC []
expressionGen (VAR variableName) = listToNRC (variableName ∷ [])
expressionGen (ADD expression1 expression2) = unionNRC (expressionGen expression1) (expressionGen expression2)

-- This function takes a statement and calculates the liveIn set for it. For that, it takes a VariableSet
-- which holds the liveIn of its successors, which would correspond to the liveOut of the statement.
-- Also, it takes a vector of m VariableSet values, which at the end of the entire liveness analysis
-- should hold the liveOut of each of the m assignments in the original program. As a side effect of the
-- liveIn calculation of an assignment, the function updates the corresponding index in the vector. That
-- result will then be used in one of the rules of the typing system. 
livenessAnalysisAux : {t : ℕ} → ASTStmId {t} → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)
livenessAnalysisAux statement@(ASSIGN variableName assignId expression) nextLiveIn assignLiveOuts = 
    let liveIn = unionNRC (differenceNRC nextLiveIn (statementKill statement)) (expressionGen expression)
        newAssignLiveOuts = assignLiveOuts [ assignId ]≔ nextLiveIn
     in liveIn , newAssignLiveOuts
-- TODO: Check if, in this case, I only need to add (expressionGen condition) to the resulting liveIn
--  or if I also need to add the free variables from the types of the variables used in the expression.    
livenessAnalysisAux (IF0 condition statementT statementF) nextLiveIn assignLiveOuts = 
    let liveInT , assignLiveOutsT = livenessAnalysisAux statementT nextLiveIn assignLiveOuts
        liveInF , assignLiveOutsF = livenessAnalysisAux statementF nextLiveIn assignLiveOutsT
     in unionNRC (unionNRC liveInT liveInF) (expressionGen condition) , assignLiveOutsF
-- TODO: Here I have a problem that the liveIn for the condition and the statement are mutually dependant. 
-- How can I go about implementing this? Do we need some kind of fixed point iteration?
livenessAnalysisAux (WHILE condition statement) nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts
livenessAnalysisAux (SEQ statement1 statement2) nextLiveIn assignLiveOuts = 
    let nextLiveIn2 , assignLiveOuts2 = livenessAnalysisAux statement2 nextLiveIn assignLiveOuts
     in livenessAnalysisAux statement1 nextLiveIn2 assignLiveOuts2
livenessAnalysisAux SKIP nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts

livenessAnalysis : {t : ℕ} → ASTStmId {t} → 𝒜 → Vec VariableSet t
livenessAnalysis statement activeSet = 
    proj₂ (livenessAnalysisAux statement (activeSetToNRC activeSet) (Data.Vec.Base.replicate (listToNRC [])))
