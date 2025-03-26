module TypeSystem.TypeSystem {n} where

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

open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}
open import TypeSystem.AssignmentId {n}
open import TypeSystem.Liveness {n}
open import TypeSystem.Predicates {n}
open import TypeSystem.SecurityLabels {n}

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
  VAR : {Γ : TypingEnvironment} {v : TransVariable}
    → Γ ⊦ VAR v - findType Γ v
  OP : {Γ : TypingEnvironment} {e e' : ASTExp} {τ τ' : SecurityLabel}
    → Γ ⊦ e - τ
    → Γ ⊦ e' - τ'
    → Γ ⊦ ADD e e' - Join τ τ'

variableNotInFreeSets : TransVariable → TypingEnvironment → VariableSet → Set
variableNotInFreeSets varName Γ varSet = 
  any (\v → varName elemᵥₛ (labelVariables (findType Γ v))) (toListᵥₛ varSet) ≡ false

-- Typing rules for statements.
data _,_⊦_[_,_]-_ : {t : ℕ} → TypingEnvironment → SecurityLabel → ASTStmId t → Vec Predicate t → Vec VariableSet t → List ProofObligation → Set where
  SKIP : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {P : Vec Predicate t} {L : Vec VariableSet t} 
    → Γ , pc ⊦ SKIP [ P , L ]- []
  SEQ : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {s s' : ASTStmId t} {P : Vec Predicate t} {L : Vec VariableSet t} {proofs proofs' : List ProofObligation}
    → Γ , pc ⊦ s [ P , L ]- proofs
    → Γ , pc ⊦ s' [ P , L ]- proofs'
    → Γ , pc ⊦ SEQ s s' [ P , L ]- (proofs ++ proofs')
  IF : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {sT sF : ASTStmId t} {P : Vec Predicate t} {L : Vec VariableSet t} {proofs proofs' : List ProofObligation}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ sT [ P , L ]- proofs
    → Γ , (Join τ pc) ⊦ sF [ P , L ]- proofs'
    → Γ , pc ⊦ IF0 cond sT sF [ P , L ]- (proofs ++ proofs')
  ASSIGN : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {v : TransVariable} {id : Fin t} {e : ASTExp} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ e - τ
    → variableNotInFreeSets v Γ (lookup L id) 
    → Γ , pc ⊦ ASSIGN v id e [ P , L ]- [ ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ v ]
  WHILE : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {s : ASTStmId t} {P : Vec Predicate t} {L : Vec VariableSet t} {proofs : List ProofObligation}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ s [ P , L ]- proofs
    → Γ , pc ⊦ WHILE cond s [ P , L ]- proofs

-- Returns the type of a given expression and a proof the type calculation.   
typeExpression : (Γ : TypingEnvironment) (e : ASTExp) → ∃[ τ ] (Γ ⊦ e - τ)
typeExpression Γ (INTVAL n) = Label Low , CONST {Γ} {n}
typeExpression Γ (VAR v) = findType Γ v , VAR {Γ} {v}
typeExpression Γ (ADD e e') = 
  let τ , proof = typeExpression Γ e
      τ' , proof' = typeExpression Γ e'
   in Join τ τ' , OP proof proof'

typeStatementAux : {t : ℕ} (Γ : TypingEnvironment) (pc : SecurityLabel) (stm : ASTStmId t) (P : Vec Predicate t) (L : Vec VariableSet t)
  → Maybe (∃[ proofs ] (Γ , pc ⊦ stm [ P , L ]- proofs))

typeStatementAux Γ pc (ASSIGN varName assId exp) P L 
  with (any (\v → varName elemᵥₛ (labelVariables (findType Γ v))) (toListᵥₛ (lookup L assId))) ≟ false
...          | yes varNotInFreeSets = 
                let τ , expType = typeExpression Γ exp
                    proofObligation = ⊨ lookup P assId ⇒ Join τ pc ⊑ findType Γ varName 
                 in just ([ proofObligation ] , ASSIGN expType varNotInFreeSets)
...         | no _ = nothing

typeStatementAux Γ pc (IF0 cond sT sF) P L = 
  let τ , expType = typeExpression Γ cond
   in case typeStatementAux Γ (Join τ pc) sT P L of λ where
        nothing → nothing
        (just (proofsT , sTType)) → case typeStatementAux Γ (Join τ pc) sF P L of λ where
                                      nothing → nothing
                                      (just (proofsF , sFType)) → just (proofsT ++ proofsF , IF expType sTType sFType)

typeStatementAux Γ pc (WHILE cond stm) P L = 
  let τ , expType = typeExpression Γ cond
   in case typeStatementAux Γ (Join τ pc) stm P L of λ where
        nothing → nothing
        (just (proofs , stmType)) → just (proofs , WHILE expType stmType)

typeStatementAux Γ pc (SEQ stm stm') P L = 
  case typeStatementAux Γ pc stm P L of λ where
    nothing → nothing
    (just (proofs , stmType)) → case typeStatementAux Γ pc stm' P L of λ where
                                  nothing → nothing
                                  (just (proofs' , stmType')) → just (proofs ++ proofs' , SEQ stmType stmType')

typeStatementAux Γ pc SKIP P L = just ([] , SKIP {_} {Γ} {pc} {P} {L})

-- TODO(minor): The type definition is horribly long, how can I make it nicer?.
-- Maybe I can use dependent sums so that the values themselves are returned and the definition is much smaller.
-- Checks if the given program can be typed under the type system after applying the transformation.
-- In case it can, a proof with the typing rules applied is returned.
-- Maybe (∃[ proofs, P , L , s , a , b ] P , L ⊦ s [ a , b ] - proofs
-- Either that or I could return a record type.
typeStatement : (stm : ASTStmS) → (Γ : TypingEnvironment)
  → Maybe (∃[ proofs ] (Γ , (Label Low) ⊦ (identifyAssignmentsAux (proj₁ (transformProgram stm)) zero (≤-reflexive refl)) [ (proj₂ (populatePredicateVector (identifyAssignmentsAux (proj₁ (transformProgram stm)) zero (≤-reflexive refl)) True (replicate (assignCount (proj₁ (transformProgram stm))) True))) , (proj₂ (livenessAnalysisAux (identifyAssignmentsAux (proj₁ (transformProgram stm)) zero (≤-reflexive refl)) Γ (proj₂ (transformProgram stm)) (fromActiveSetᵥₛ (proj₂ (transformProgram stm))) (replicate (assignCount (proj₁ (transformProgram stm))) emptyᵥₛ))) ]- proofs))
typeStatement stm Γ = 
  let stmTrans , active = transformProgram stm
      stmId = identifyAssignments stmTrans
      predicates = generatePredicates stmId
      liveSets = livenessAnalysis stmId active Γ
   in typeStatementAux Γ (Label Low) stmId predicates liveSets
