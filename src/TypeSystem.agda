module TypeSystem {n} where

open import Data.Bool.Base
open import Data.Fin
open import Data.List
  hiding (lookup)
open import Data.Nat
open import Data.Product
open import Data.Vec.Base
  hiding (_++_ ; [_])
open import Relation.Binary.PropositionalEquality
  hiding ([_])

open import AST {n}
open import Predicates {n}
open import SecurityLabels {n}
open import VariableSet {n}

record ProofObligation : Set where
  constructor ⊨_⇒_⊑_
  field
    premise : Predicate
    subtype : SecurityLabel
    supertype : SecurityLabel

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
data _,_⊦_,_,_,_ : {t : ℕ} → TypingEnvironment → SecurityLabel → ASTStmId {t} → List ProofObligation → Vec Predicate t → Vec VariableSet t → Set where
  SKIP : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {P : Vec Predicate t} {L : Vec VariableSet t} 
    → Γ , pc ⊦ SKIP {t} , [] , P , L
  SEQ : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {s s' : ASTStmId {t}} {p p' : List ProofObligation} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ , pc ⊦ s , p , P , L
    → Γ , pc ⊦ s' , p' , P , L
    → Γ , pc ⊦ SEQ s s' , (p ++ p') , P , L
  IF : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {sT sF : ASTStmId {t}} {pT pF : List ProofObligation} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ sT , pT , P , L
    → Γ , (Join τ pc) ⊦ sF , pF , P , L
    → Γ , pc ⊦ IF0 cond sT sF , (pT ++ pF) , P , L
  ASSIGN : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {v : Fin n × ℕ} {id : Fin t} {e : ASTExp} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ e - τ
    → variableNotInFreeSets v Γ (lookup L id) 
    → Γ , pc ⊦ ASSIGN v id e , [ ⊨ lookup P id ⇒ Join τ pc ⊑ findType Γ v ] , P , L
  WHILE : {t : ℕ} {Γ : TypingEnvironment} {pc : SecurityLabel} {τ : SecurityLabel} {cond : ASTExp} {s : ASTStmId {t}} {p : List ProofObligation} {P : Vec Predicate t} {L : Vec VariableSet t}
    → Γ ⊦ cond - τ
    → Γ , (Join τ pc) ⊦ s , p , P , L
    → Γ , pc ⊦ WHILE cond s , p , P , L

-- TODO(major): Should I implement some sort of function with type ASTStmId {t} → Maybe (_ , _ ⊦ _ , _ , _ ,_) ? This way it would do all the setup and run the type system in the given program.
