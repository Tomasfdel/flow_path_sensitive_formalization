module Liveness {n} where

open import Data.Bool.Base
open import Data.List.Base
  hiding (allFin ; length ; replicate ; zip ) 
open import Data.Nat
open import Data.Product
  hiding (zip) 
open import Data.Vec.Base

open import ActiveSet {n}
open import AST {n}
open import SecurityLabels {n}
open import Transformation {n}
open import VariableSet {n}

fromActiveSetᵥₛ : 𝒜 → VariableSet
fromActiveSetᵥₛ activeSet = fromListᵥₛ (toList (zip (allFin (length activeSet)) activeSet))

-- Statement KILL function from Figure 9 of the paper.
statementKill : {t : ℕ} → ASTStmId t → VariableSet
statementKill (ASSIGN variableName _ _) = singletonᵥₛ variableName
statementKill _ = emptyᵥₛ

-- TODO(minor): I'll have to update the VAR case when I change the TypingEnvironment type definition.
-- Expression GEN function from Figure 9 of the paper.
expressionGen : ASTExp → TypingEnvironment → VariableSet
expressionGen (INTVAL _) _ = emptyᵥₛ
expressionGen (VAR variableName) typeEnv = 
    (singletonᵥₛ variableName) unionᵥₛ (labelVariables typeEnv)
expressionGen (ADD expression1 expression2) typeEnv = 
    (expressionGen expression1 typeEnv) unionᵥₛ (expressionGen expression2 typeEnv)

-- Uses an iterative method to calculate the liveIn set of a WHILE statement.
livenessIteration : {t : ℕ} → ℕ → ASTExp → ASTStmId t → TypingEnvironment → 𝒜 → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)

-- This function takes a statement and calculates the liveIn set for it. For that, it takes a VariableSet
-- which holds the liveIn of its successors, which would correspond to the liveOut of the statement.
-- Also, it takes a vector of m VariableSet values, which at the end of the entire liveness analysis
-- should hold the liveOut of each of the m assignments in the original program. As a side effect of the
-- liveIn calculation of an assignment, the function updates the corresponding index in the vector. That
-- result will then be used in one of the rules of the typing system. 
livenessAnalysisAux : {t : ℕ} → ASTStmId t → TypingEnvironment → 𝒜 → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)
livenessAnalysisAux statement@(ASSIGN variableName assignId expression) typeEnv _ nextLiveIn assignLiveOuts = 
    let liveIn = (nextLiveIn diffᵥₛ (statementKill statement)) unionᵥₛ (expressionGen expression typeEnv)
        newAssignLiveOuts = assignLiveOuts [ assignId ]≔ nextLiveIn
     in liveIn , newAssignLiveOuts
livenessAnalysisAux (IF0 condition statementT statementF) typeEnv activeSet nextLiveIn assignLiveOuts = 
    let liveInT , assignLiveOutsT = livenessAnalysisAux statementT typeEnv activeSet nextLiveIn assignLiveOuts
        liveInF , assignLiveOutsF = livenessAnalysisAux statementF typeEnv activeSet nextLiveIn assignLiveOutsT
     in (liveInT unionᵥₛ liveInF) unionᵥₛ (expressionGen condition typeEnv) , assignLiveOutsF
livenessAnalysisAux (WHILE condition statement) typeEnv activeSet nextLiveIn assignLiveOuts = 
    livenessIteration (𝒜varCount activeSet) condition statement typeEnv activeSet nextLiveIn assignLiveOuts
livenessAnalysisAux (SEQ statement1 statement2) typeEnv activeSet nextLiveIn assignLiveOuts = 
    let nextLiveIn2 , assignLiveOuts2 = livenessAnalysisAux statement2 typeEnv activeSet nextLiveIn assignLiveOuts
     in livenessAnalysisAux statement1 typeEnv activeSet nextLiveIn2 assignLiveOuts2
livenessAnalysisAux SKIP _ _ nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts

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
-- TODO(minor): See if I can find a cleaner to prove that this function terminates.
livenessIteration zero _ _ _ _ nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts
livenessIteration (suc iterCount) condition body typeEnv activeSet nextLiveIn assignLiveOuts = 
    let potentialLiveIn = (expressionGen condition typeEnv) unionᵥₛ nextLiveIn
        bodyLiveIn , assignLiveOuts2 = livenessAnalysisAux body typeEnv activeSet potentialLiveIn assignLiveOuts
        finalLiveIn = bodyLiveIn unionᵥₛ potentialLiveIn
     in if potentialLiveIn strictSubsetᵥₛ finalLiveIn 
            then livenessIteration iterCount condition body typeEnv activeSet finalLiveIn assignLiveOuts2
            else finalLiveIn , assignLiveOuts2

-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → ASTStmId t → 𝒜 → TypingEnvironment → Vec VariableSet t
livenessAnalysis {t} statement activeSet typeEnv = 
    proj₂ (livenessAnalysisAux statement typeEnv activeSet (fromActiveSetᵥₛ activeSet) (replicate t emptyᵥₛ))
