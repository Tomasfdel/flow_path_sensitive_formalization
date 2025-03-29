module TypeSystem.Liveness {n} where

open import Data.Bool.Base
open import Data.Nat
open import Data.Product
  hiding (zip) 
open import Data.Vec.Base

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}
open import TypeSystem.SecurityLabels {n}

-- Set of all active variables of an active set.
from𝒜ᵥₛ : 𝒜 → VariableSet
from𝒜ᵥₛ A = fromListᵥₛ (toList (zip (allFin n) A))

-- Statement KILL function from Figure 9.
stmKill : {t : ℕ} → ASTStmId t → VariableSet
stmKill (ASSIGN v _ _) = singletonᵥₛ v
stmKill _ = emptyᵥₛ

-- Expression GEN function from Figure 9.
expGen : ASTExp → TypingEnvironment → VariableSet
expGen (INTVAL _) _ = emptyᵥₛ
expGen (VAR v) Γ = (singletonᵥₛ v) unionᵥₛ (labelVariables (findType Γ v))
expGen (ADD exp₁ exp₂) Γ = (expGen exp₁ Γ) unionᵥₛ (expGen exp₂ Γ)

mutual 
  -- Uses an iterative method to calculate the liveIn set of a WHILE statement.
  -- It starts by taking the liveIn set of the statement following the WHILE block (nextLiveIn) 
  -- and joins it with the GEN set of the while condition. The result will be used as the liveIn 
  -- passed to the liveness analysis of the loop's body. Said analysis returns the liveIn set for the body. 
  -- Then, if that result is a subset of the liveIn set passed as an argument, then we have finished 
  -- iterating and have a final result. Otherwise, we take the union between those two sets and use that 
  -- as the nextLiveIn for a new iteration of the function.
  -- This process is guaranteed to finish because nextLiveIn can only grow in size between iterations
  -- and the total number of possible variables is set for the program so there is an upper bound to
  -- the resulting set size. 
  livenessIteration : {t : ℕ} → ℕ → ASTExp → ASTStmId t → TypingEnvironment → 𝒜 → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)
  livenessIteration zero _ _ _ _ nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts
  livenessIteration (suc iterCount) cond body Γ A nextLiveIn assignLiveOuts = 
    let potentialLiveIn = (expGen cond Γ) unionᵥₛ nextLiveIn
        bodyLiveIn , assignLiveOuts' = livenessAux body Γ A potentialLiveIn assignLiveOuts
        finalLiveIn = bodyLiveIn unionᵥₛ potentialLiveIn
     in if potentialLiveIn strictSubsetᵥₛ finalLiveIn 
           then livenessIteration iterCount cond body Γ A finalLiveIn assignLiveOuts'
           else finalLiveIn , assignLiveOuts'

  -- Calculates the liveIn set of a program by starting at its last statement and working backwards. 
  -- For that, it takes a VariableSet which holds the liveIn of a statement's successors, which corresponds to the liveOut of the statement.
  -- Also, it takes a vector of t VariableSet's, which at the end of the entire liveness analysis
  -- should hold the liveOut of each of the t assignments in the original program. As a side effect of the
  -- liveIn calculation of an assignment, the function updates its corresponding index in the vector.
  livenessAux : {t : ℕ} → ASTStmId t → TypingEnvironment → 𝒜 → VariableSet → Vec VariableSet t → VariableSet × (Vec VariableSet t)
  livenessAux SKIP _ _ nextLiveIn assignLiveOuts = nextLiveIn , assignLiveOuts
  livenessAux s@(ASSIGN _ id exp) Γ _ nextLiveIn assignLiveOuts = 
    let liveIn = (nextLiveIn diffᵥₛ (stmKill s)) unionᵥₛ (expGen exp Γ)
        assignLiveOuts' = assignLiveOuts [ id ]≔ nextLiveIn
     in liveIn , assignLiveOuts'
  livenessAux (SEQ s₁ s₂) Γ A nextLiveIn assignLiveOuts = 
    let nextLiveIn' , assignLiveOuts' = livenessAux s₂ Γ A nextLiveIn assignLiveOuts
     in livenessAux s₁ Γ A nextLiveIn' assignLiveOuts'
  livenessAux (IF cond sT sF) Γ A nextLiveIn assignLiveOuts = 
    let liveInT , assignLiveOutsT = livenessAux sT Γ A nextLiveIn assignLiveOuts
        liveInF , assignLiveOutsF = livenessAux sF Γ A nextLiveIn assignLiveOutsT
     in (liveInT unionᵥₛ liveInF) unionᵥₛ (expGen cond Γ) , assignLiveOutsF
  livenessAux (WHILE cond s) Γ A nextLiveIn assignLiveOuts = 
    livenessIteration (𝒜varCount A) cond s Γ A nextLiveIn assignLiveOuts

-- Given a program statement, returns a vector of variable sets so that the element in its n-th
-- position is the liveOut set of the n-th assignment of the program. 
livenessAnalysis : {t : ℕ} → ASTStmId t → 𝒜 → TypingEnvironment → Vec VariableSet t
livenessAnalysis {t} s A Γ = 
  proj₂ (livenessAux s Γ A (from𝒜ᵥₛ A) (replicate t emptyᵥₛ))
