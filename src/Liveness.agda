module Liveness {n} where

open import Data.Bool.Base
open import Data.List.Base
  hiding (allFin ; length ; replicate ; zip ) 
open import Data.Nat
open import Data.Product
  hiding (zip) 
open import Data.Vec.Base

open import AST {n}
open import VariableSet {n}
open import Transformation {n}

fromActiveSetᵥₛ : 𝒜 → VariableSet
fromActiveSetᵥₛ activeSet = fromListᵥₛ (toList (zip (allFin (length activeSet)) activeSet))

statementKill : {t : ℕ} → ASTStmId {t} → VariableSet
statementKill (ASSIGN variableName _ _) = fromListᵥₛ (variableName ∷ [])
statementKill _ = emptyᵥₛ

-- TODO(major): This implementation is incomplete. I still need to add the set of free variables from the variable's security type
-- following the description from Figure 9 of the paper.
expressionGen : ASTExp → VariableSet
expressionGen (INTVAL _) = emptyᵥₛ
expressionGen (VAR variableName) = fromListᵥₛ (variableName ∷ [])
expressionGen (ADD expression1 expression2) = (expressionGen expression1) unionᵥₛ (expressionGen expression2)

-- Uses an iterative method to calculate the liveIn set of a WHILE statement.
livenessIteration : {t : ℕ} → ASTExp → ASTStmId {t} → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)

-- This function takes a statement and calculates the liveIn set for it. For that, it takes a VariableSet
-- which holds the liveIn of its successors, which would correspond to the liveOut of the statement.
-- Also, it takes a vector of m VariableSet values, which at the end of the entire liveness analysis
-- should hold the liveOut of each of the m assignments in the original program. As a side effect of the
-- liveIn calculation of an assignment, the function updates the corresponding index in the vector. That
-- result will then be used in one of the rules of the typing system. 
livenessAnalysisAux : {t : ℕ} → ASTStmId {t} → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)
livenessAnalysisAux statement@(ASSIGN variableName assignId expression) nextLiveIn assignLiveOuts = 
    let liveIn = (nextLiveIn diffᵥₛ (statementKill statement)) unionᵥₛ (expressionGen expression)
        newAssignLiveOuts = assignLiveOuts [ assignId ]≔ nextLiveIn
     in liveIn , newAssignLiveOuts
-- TODO(medium): Check if, in this case, I only need to add (expressionGen condition) to the resulting liveIn
--  or if I also need to add the free variables from the types of the variables used in the expression.
-- This also applies to the condition of the while block.    
livenessAnalysisAux (IF0 condition statementT statementF) nextLiveIn assignLiveOuts = 
    let liveInT , assignLiveOutsT = livenessAnalysisAux statementT nextLiveIn assignLiveOuts
        liveInF , assignLiveOutsF = livenessAnalysisAux statementF nextLiveIn assignLiveOutsT
     in (liveInT unionᵥₛ liveInF) unionᵥₛ (expressionGen condition) , assignLiveOutsF
livenessAnalysisAux (WHILE condition statement) nextLiveIn assignLiveOuts = 
    livenessIteration condition statement nextLiveIn assignLiveOuts
livenessAnalysisAux (SEQ statement1 statement2) nextLiveIn assignLiveOuts = 
    let nextLiveIn2 , assignLiveOuts2 = livenessAnalysisAux statement2 nextLiveIn assignLiveOuts
     in livenessAnalysisAux statement1 nextLiveIn2 assignLiveOuts2
livenessAnalysisAux SKIP nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts

-- Uses an iterative method to calculate the liveIn set of a WHILE statement.
-- The way this works is that it starts by taking the liveIn set of the statement following the 
-- WHILE block (nextLiveIn) and joins it with the GEN set of the loop condition. That union will 
-- be used as the liveIn passed to the liveness analysis of the loop's body. Said analysis returns 
-- the liveIn set for the body. Then, if that result is a subset of the liveIn set passed as an 
-- argument, then we have finished iterating and have a final result. Otherwise, we take the union 
-- between those two sets and use that as the nextLiveIn for a new iteration of the function.
-- This process is guaranteed to finish because between iterations nextLiveIn can only grow in size
-- and the total number of possible variables is set for the program so there is an upper bound to
-- the resulting set size. 
-- TODO(major): See how to prove that this function terminates.
{-# TERMINATING #-}
livenessIteration condition body nextLiveIn assignLiveOuts = 
    let potentialLiveIn = (expressionGen condition) unionᵥₛ nextLiveIn
        bodyLiveIn , assignLiveOuts2 = livenessAnalysisAux body potentialLiveIn assignLiveOuts
        finalLiveIn = bodyLiveIn unionᵥₛ potentialLiveIn
     in if potentialLiveIn ==ᵥₛ finalLiveIn 
            then finalLiveIn , assignLiveOuts2
            else livenessIteration condition body finalLiveIn assignLiveOuts2

-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → ASTStmId {t} → 𝒜 → Vec VariableSet t
livenessAnalysis statement activeSet = 
    proj₂ (livenessAnalysisAux statement (fromActiveSetᵥₛ activeSet) (replicate emptyᵥₛ))
