module TypeSystem {n} where

open import Data.Bool.Base
open import Data.Bool.Properties
  hiding (≤-reflexive)
open import Data.Fin
  hiding (_≟_)
open import Data.List
  hiding (lookup ; replicate)
open import Data.Maybe.Base
open import Data.Nat
  hiding (_≟_)
open import Data.Nat.Properties
  hiding (_≟_)
open import Data.Product
open import Data.Vec.Base
  hiding (_++_ ; [_])
open import Function.Base
open import Relation.Binary.PropositionalEquality
  hiding ([_])
open import Relation.Nullary
  hiding (True)

open import AssignmentId {n}
open import AST {n}
open import Liveness {n}
open import Predicates {n}
open import SecurityLabels {n}
open import Transformation {n}
open import VariableSet {n}

-- Proof obligations created by the type system's assignment rules.
record ProofObligation : Set where
  constructor ⊨_⇒_⊑_
  field
    premise : Predicate
    subtype : SecurityLabel
    supertype : SecurityLabel

-- Typing rules for expressions.
data _⊦_-_ : TypingEnvironment → ASTExp → SecurityLabel → Set where
  CONST : {Γ : TypingEnvironment} {n : ℕ} 
    → Γ ⊦ INTVAL n - Label Low
  VAR : {Γ : TypingEnvironment} {v : Fin n × ℕ}
    → Γ ⊦ VAR v - findType Γ v
  OP : {Γ : TypingEnvironment} {e e' : ASTExp} {τ τ' : SecurityLabel}
    → Γ ⊦ e - τ
    → Γ ⊦ e' - τ'
    → Γ ⊦ ADD e e' - Join τ τ'

variableNotInFreeSets : Fin n × ℕ → TypingEnvironment → VariableSet → Set
variableNotInFreeSets varName Γ varSet = 
  any (\v → varName elemᵥₛ (labelVariables (findType Γ v))) (toListᵥₛ varSet) ≡ false

-- TODO(minor): I should look for a nicer way of building this type rather than the full list of commas at the end.
-- TODO(minor): If I use a dependent sum, I can add the list of proof obligations again to this type, which I think makes the type definition more proper.
-- Typing rules for statements.
data _,_⊦_,_,_ : {t : ℕ} → TypingEnvironment → SecurityLabel → ASTStmId {t} → Vec Predicate t → Vec VariableSet t → Set where
  SKIP : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {P : Vec Predicate t} {L : Vec VariableSet t} 
    → Γ , pc ⊦ SKIP {t} , P , L
  SEQ : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {s s' : ASTStmId {t}} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ , pc ⊦ s , P , L
    → Γ , pc ⊦ s' , P , L
    → Γ , pc ⊦ SEQ s s' , P , L
  IF : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {sT sF : ASTStmId {t}} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ sT , P , L
    → Γ , (Join τ pc) ⊦ sF , P , L
    → Γ , pc ⊦ IF0 cond sT sF , P , L
  ASSIGN : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {v : Fin n × ℕ} {id : Fin t} {e : ASTExp} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ e - τ
    → variableNotInFreeSets v Γ (lookup L id) 
    → Γ , pc ⊦ ASSIGN v id e , P , L
  WHILE : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {s : ASTStmId {t}} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ s , P , L
    → Γ , pc ⊦ WHILE cond s , P , L

-- Returns the type of a given expression and a proof the type calculation.   
typeExpression : (Γ : TypingEnvironment) (e : ASTExp) → ∃[ τ ] (Γ ⊦ e - τ)
typeExpression Γ (INTVAL n) = Label Low , CONST {Γ} {n}
typeExpression Γ (VAR v) = findType Γ v , VAR {Γ} {v}
typeExpression Γ (ADD e e') = 
  let τ , proof = typeExpression Γ e
      τ' , proof' = typeExpression Γ e'
   in Join τ τ' , OP proof proof'

typeStatementAux : {t : ℕ} (Γ : TypingEnvironment) (pc : SecurityLabel) (stm : ASTStmId {t}) (P : Vec Predicate t) (L : Vec VariableSet t)
  → Maybe ((Γ , pc ⊦ stm , P , L) × List ProofObligation)

typeStatementAux Γ pc (ASSIGN varName assId exp) P L 
  with (any (\v → varName elemᵥₛ (labelVariables (findType Γ v))) (toListᵥₛ (lookup L assId))) ≟ false
...          | yes varNotInFreeSets = 
                let τ , expType = typeExpression Γ exp
                    proofObligation = ⊨ lookup P assId ⇒ Join τ pc ⊑ findType Γ varName 
                 in just (ASSIGN expType varNotInFreeSets , [ proofObligation ])
...         | no _ = nothing

typeStatementAux Γ pc (IF0 cond sT sF) P L = 
  let τ , expType = typeExpression Γ cond
   in case typeStatementAux Γ (Join τ pc) sT P L of λ where
        nothing → nothing
        (just (sTType , proofsT)) → case typeStatementAux Γ (Join τ pc) sF P L of λ where
                                      nothing → nothing
                                      (just (sFType , proofsF)) → just (IF expType sTType sFType , proofsT ++ proofsF)

typeStatementAux Γ pc (WHILE cond stm) P L = 
  let τ , expType = typeExpression Γ cond
   in case typeStatementAux Γ (Join τ pc) stm P L of λ where
        nothing → nothing
        (just (stmType , proofs)) → just (WHILE expType stmType , proofs)

typeStatementAux Γ pc (SEQ stm stm') P L = 
  case typeStatementAux Γ pc stm P L of λ where
    nothing → nothing
    (just (stmType , proofs)) → case typeStatementAux Γ pc stm' P L of λ where
                                  nothing → nothing
                                  (just (stmType' , proofs')) → just (SEQ stmType stmType' , proofs ++ proofs')

typeStatementAux Γ pc SKIP P L = just (SKIP {_} {Γ} {pc} {P} {L} , [])

-- TODO(minor): The type definition is horribly long, how can I make it nicer?.
-- Maybe I can use dependent sums so that the values themselves are returned and the definition is much smaller.
-- Checks if the given program can be typed under the type system after applying the transformation.
-- In case it can, a proof with the typing rules applied is returned.
typeStatement : (stm : ASTStmS) 
  → Maybe ((Label Low) , (Label Low) ⊦ (identifyAssignmentsAux (proj₁ (transformProgram stm)) zero (≤-reflexive refl)) , (proj₂ (populatePredicateVector (identifyAssignmentsAux (proj₁ (transformProgram stm)) zero (≤-reflexive refl)) True (replicate (assignCount (proj₁ (transformProgram stm))) True))) , (proj₂ (livenessAnalysisAux (identifyAssignmentsAux (proj₁ (transformProgram stm)) zero (≤-reflexive refl)) (Label Low) (proj₂ (transformProgram stm)) (fromActiveSetᵥₛ (proj₂ (transformProgram stm))) (replicate (assignCount (proj₁ (transformProgram stm))) emptyᵥₛ))) × List ProofObligation)
typeStatement stm = 
  let stmTrans , active = transformProgram stm
      stmId = identifyAssignments stmTrans
      predicates = generatePredicates stmId
      liveSets = livenessAnalysis stmId active (Label Low) 
   in typeStatementAux (Label Low) (Label Low) stmId predicates liveSets
