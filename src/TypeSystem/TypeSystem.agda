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

-- Typing rules for expressions from Figure 10.
data _⊦_-_ : TypingEnvironment → ASTExp → SecurityLabel → Set where
  CONST : {Γ : TypingEnvironment} {n : ℕ} 
    → Γ ⊦ INTVAL n - Label Low
  VAR : {Γ : TypingEnvironment} {v : TransVariable}
    → Γ ⊦ VAR v - findType Γ v
  OP : {Γ : TypingEnvironment} {exp₁ exp₂ : ASTExp} {τ₁ τ₂ : SecurityLabel}
    → Γ ⊦ exp₁ - τ₁
    → Γ ⊦ exp₂ - τ₂
    → Γ ⊦ ADD exp₁ exp₂ - Join τ₁ τ₂

-- Property that a given variable does not belong to the security types
-- of any variable in a given set.
variableNotInFreeSets : TransVariable → TypingEnvironment → VariableSet → Set
variableNotInFreeSets varName Γ varSet = 
  any (λ v → varName elemᵥₛ (labelVariables (findType Γ v))) (toListᵥₛ varSet) ≡ false

-- Typing rules for statements from Figure 11.
data _,_⊦_[_,_]-_ : {t : ℕ} → TypingEnvironment → SecurityLabel → ASTStmId t → Vec Predicate t → Vec VariableSet t → List ProofObligation → Set where
  SKIP : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {P : Vec Predicate t} {L : Vec VariableSet t} 
    → Γ , pc ⊦ SKIP [ P , L ]- []
  ASSIGN : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {v : TransVariable} {id : Fin t} {exp : ASTExp} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ exp - τ
    → variableNotInFreeSets v Γ (lookup L id) 
    → Γ , pc ⊦ ASSIGN v id exp [ P , L ]- [ ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ v ]
  SEQ : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {s₁ s₂ : ASTStmId t} {P : Vec Predicate t} {L : Vec VariableSet t} {proofs₁ proofs₂ : List ProofObligation}
    → Γ , pc ⊦ s₁ [ P , L ]- proofs₁
    → Γ , pc ⊦ s₂ [ P , L ]- proofs₂
    → Γ , pc ⊦ SEQ s₁ s₂ [ P , L ]- (proofs₁ ++ proofs₂)
  IF : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {sT sF : ASTStmId t} {P : Vec Predicate t} {L : Vec VariableSet t} {proofsT proofsF : List ProofObligation}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ sT [ P , L ]- proofsT
    → Γ , (Join τ pc) ⊦ sF [ P , L ]- proofsF
    → Γ , pc ⊦ IF cond sT sF [ P , L ]- (proofsT ++ proofsF)
  WHILE : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {s : ASTStmId t} {P : Vec Predicate t} {L : Vec VariableSet t} {proofs : List ProofObligation}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ s [ P , L ]- proofs
    → Γ , pc ⊦ WHILE cond s [ P , L ]- proofs

-- Returns a type proof for the given expression.   
typeExp : (Γ : TypingEnvironment) (exp : ASTExp) → Σ[ τ ∈ SecurityLabel ] (Γ ⊦ exp - τ)
typeExp Γ (INTVAL _) = Label Low , CONST
typeExp Γ (VAR v) = findType Γ v , VAR
typeExp Γ (ADD exp₁ exp₂) = 
  let τ₁ , proof₁ = typeExp Γ exp₁
      τ₂ , proof₂ = typeExp Γ exp₂
   in Join τ₁ τ₂ , OP proof₁ proof₂

-- Returns a type proof for the given statement, if possible.
typeStm : {t : ℕ} (Γ : TypingEnvironment) (pc : SecurityLabel) (s : ASTStmId t) (P : Vec Predicate t) (L : Vec VariableSet t)
  → Maybe (Σ[ proofs ∈ List ProofObligation ] (Γ , pc ⊦ s [ P , L ]- proofs))
typeStm _ _ SKIP _ _ = just ([] , SKIP)  
typeStm Γ pc (ASSIGN varName id exp) P L 
  with (any (λ v → varName elemᵥₛ (labelVariables (findType Γ v))) (toListᵥₛ (lookup L id))) ≟ false
...          | yes varNotInFreeSets = 
                let τ , expType = typeExp Γ exp
                    proofObligation = ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ varName 
                 in just ([ proofObligation ] , ASSIGN expType varNotInFreeSets)
...         | no _ = nothing
typeStm Γ pc (SEQ s₁ s₂) P L = 
  typeStm Γ pc s₁ P L >>=
  λ (proofs₁ , s₁Type) → typeStm Γ pc s₂ P L >>=
  λ (proofs₂ , s₂Type) → just (proofs₁ ++ proofs₂ , SEQ s₁Type s₂Type)
typeStm Γ pc (IF cond sT sF) P L = 
  let τ , condType = typeExp Γ cond
   in typeStm Γ (Join τ pc) sT P L >>=
      λ (proofsT , sTType) → typeStm Γ (Join τ pc) sF P L >>=
      λ (proofsF , sFType) → just (proofsT ++ proofsF , IF condType sTType sFType)
typeStm Γ pc (WHILE cond s) P L = 
  let τ , expType = typeExp Γ cond
   in typeStm Γ (Join τ pc) s P L >>=
      λ (proofs , sType) → just (proofs , WHILE expType sType)

-- Type containing all the components necessary for determining the security type of a program,
-- as well as the proof for the typing result.
record TypingProof : Set where
  field
    typeEnv : TypingEnvironment
    pc : SecurityLabel
    t : ℕ
    stmId : ASTStmId t
    predicates : Vec Predicate t
    liveSets : Vec VariableSet t
    proofObligations : List ProofObligation
    proof : typeEnv , pc ⊦ stmId [ predicates , liveSets ]- proofObligations

-- Takes a bracketed program and a typing environment and returns the typing proof for it
-- after it is transformed to its non-bracketed version, if possible.
typeProgram : ASTStmS → TypingEnvironment → Maybe TypingProof
typeProgram stm Γ = 
  let stmTrans , A = transformProgram stm
      stmId = identifyAssignments stmTrans
      predicates = generatePredicates stmId
      liveSets = livenessAnalysis stmId A Γ
   in typeStm Γ (Label Low) stmId predicates liveSets >>=
      λ (proofs , stmType) → just record { typeEnv = Γ; 
                                           pc = Label Low; 
                                           stmId = stmId; 
                                           predicates = predicates; 
                                           liveSets = liveSets; 
                                           proofObligations = proofs; 
                                           proof = stmType
                                         }

