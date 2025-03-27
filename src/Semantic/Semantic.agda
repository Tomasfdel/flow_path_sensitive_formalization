module Semantic.Semantic {n} where

open import Data.Fin
open import Data.Nat 
open import Relation.Binary.PropositionalEquality 

open import Transformation.AST {n}
open import Transformation.VariableSet {n}
open import Semantic.Memory {n}

-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓_
data ⟨_,_⟩⇓_ : ASTStmS → Memory → Memory → Set where
  Skip : {m : Memory} → ⟨ Skip , m ⟩⇓ m
  Assign : {m : Memory} {v : Fin n} {e : ASTExpS} 
    → ⟨ v := e , m ⟩⇓ m [ v  ↦ ⟦ e ⟧ₑ m ]
  AssignBr : {m : Memory} {v : Fin n} {e : ASTExpS} 
    → ⟨ ⟦ v := e ⟧ , m ⟩⇓ m [ v  ↦ ⟦ e ⟧ₑ m ]
  Seq : {m m' m'' : Memory} {s₁ s₂ : ASTStmS}
    → ⟨ s₁ , m ⟩⇓ m'  
    → ⟨ s₂ , m' ⟩⇓ m'' 
    → ⟨ Seq s₁ s₂ , m ⟩⇓ m'' 
  IfT : {m m' : Memory} {cond : ASTExpS} {v : ℕ} {sT sF : ASTStmS}
    → ⟦ cond ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ sT , m ⟩⇓ m' 
    → ⟨ If cond sT sF , m ⟩⇓ m'  
  IfF : {m m' : Memory} {cond : ASTExpS} {sT sF : ASTStmS}
    → ⟦ cond ⟧ₑ m ≡ 0 
    → ⟨ sF , m ⟩⇓ m' 
    → ⟨ If cond sT sF , m ⟩⇓ m'  
  WhileT : {m m' m'' : Memory} {cond : ASTExpS} {v : ℕ} {s : ASTStmS}
    → ⟦ cond ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ s , m ⟩⇓ m'  
    → ⟨ While cond s , m' ⟩⇓ m'' 
    → ⟨ While cond s , m ⟩⇓ m''
  WhileF : {m : Memory} {cond : ASTExpS} {s : ASTStmS}
    → ⟦ cond ⟧ₑ m ≡ 0 
    → ⟨ While cond s , m ⟩⇓ m

-- Big step semantics of transformed statements.
infixl 5 ⟨_,_⟩⇓ₜ_
data ⟨_,_⟩⇓ₜ_ : ASTStm → Memoryₜ → Memoryₜ → Set where
  Skipₜ : {mₜ : Memoryₜ} → ⟨ SKIP , mₜ ⟩⇓ₜ mₜ
  Assignₜ : {mₜ : Memoryₜ} {v : TransVariable} {e : ASTExp} 
    → ⟨ ASSIGN v e , mₜ ⟩⇓ₜ mₜ [ v  ↦ ⟦ e ⟧ₜ mₜ ]ₜ
  Seqₜ : {mₜ mₜ' mₜ'' : Memoryₜ} {s₁ s₂ : ASTStm}
    → ⟨ s₁ , mₜ ⟩⇓ₜ mₜ'  
    → ⟨ s₂ , mₜ' ⟩⇓ₜ mₜ'' 
    → ⟨ SEQ s₁ s₂ , mₜ ⟩⇓ₜ mₜ'' 
  IfTₜ : {mₜ mₜ' : Memoryₜ} {cond : ASTExp} {v : ℕ} {sT sF : ASTStm}
    → ⟦ cond ⟧ₜ mₜ ≡ v
    → v ≢  0 
    → ⟨ sT , mₜ ⟩⇓ₜ mₜ' 
    → ⟨ IF cond sT sF , mₜ ⟩⇓ₜ mₜ'  
  IfFₜ : {mₜ mₜ' : Memoryₜ} {cond : ASTExp} {sT sF : ASTStm}
    → ⟦ cond ⟧ₜ mₜ ≡ 0 
    → ⟨ sF , mₜ ⟩⇓ₜ mₜ' 
    → ⟨ IF cond sT sF , mₜ ⟩⇓ₜ mₜ'  
  WhileTₜ : {mₜ mₜ' mₜ'' : Memoryₜ} {cond : ASTExp} {v : ℕ} {s : ASTStm}
    → ⟦ cond ⟧ₜ mₜ ≡ v
    → v ≢  0  
    → ⟨ s , mₜ ⟩⇓ₜ mₜ'  
    → ⟨ WHILE cond s , mₜ' ⟩⇓ₜ mₜ'' 
    → ⟨ WHILE cond s , mₜ ⟩⇓ₜ mₜ''
  WhileFₜ : {mₜ : Memoryₜ} {cond : ASTExp} {s : ASTStm}
    → ⟦ cond ⟧ₜ mₜ ≡ 0 
    → ⟨ WHILE cond s , mₜ ⟩⇓ₜ mₜ
