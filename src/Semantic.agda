module Semantic {n} where

open import Data.Empty
open import Data.Fin
  hiding (_+_)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
open import Data.Product 
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality 

open import AST {n}
open import Transformation {n}


-- BRACKETED LANGUAGE SEMANTICS
-- State of the memory at a certain program point for the bracketed program.
Memory : Set _
Memory = Vec ℕ n

-- Update the value of a variable in memory.
infixl 6 _[_↦_]
_[_↦_] : Memory → Fin n → ℕ → Memory
m [ name ↦ v ] = m [ name ]≔ v

-- Semantic evaluation of expressions.
-- TODO(minor): Add the rest of the arythmetic operations besides ADD to the ASTExp type.
⟦_⟧ : ASTExpS → Memory → ℕ
⟦ IntVal n ⟧ m = n
⟦ Var name ⟧ m = lookup m name
⟦ Add exp exp' ⟧ m = ⟦ exp ⟧ m + ⟦ exp' ⟧ m
  
-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓_
data ⟨_,_⟩⇓_ : ASTStmS → Memory → Memory → Set where
  Skip : {m : Memory} → ⟨ Skip , m ⟩⇓ m
  Seq : {m m' m'' : Memory}{s₁ s₂ : ASTStmS}
    → ⟨ s₁ , m ⟩⇓ m'  
    → ⟨ s₂ , m' ⟩⇓ m'' 
    → ⟨ Seq s₁ s₂ , m ⟩⇓ m'' 
  Assign : {m : Memory} {x : Fin n} {e : ASTExpS} 
    → ⟨ x := e , m ⟩⇓ m [ x  ↦ ⟦ e ⟧ m ]
  -- TODO(minor): How do I set the precedence for this to work properly using '⟦x := e⟧' instead of '⟦_:=_ x e⟧'  
  AssignBr : {m : Memory} {x : Fin n} {e : ASTExpS} 
    → ⟨ ⟦_:=_⟧ x e , m ⟩⇓ m [ x  ↦ ⟦ e ⟧ m ]
  IfT : {m m' : Memory} {e : ASTExpS} {v : ℕ} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ m ≡ v
    → v ≢  0 
    → ⟨ s₁ , m ⟩⇓ m' 
    → ⟨ If0 e s₁ s₂ , m ⟩⇓ m'  
  IfF : {m m' : Memory} {e : ASTExpS} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ m ≡ 0 
    → ⟨ s₂ , m ⟩⇓ m' 
    → ⟨ If0 e s₁ s₂ , m ⟩⇓ m'  
  WhileT : {m m' m'' : Memory} {e : ASTExpS} {s : ASTStmS}
    → ⟦ e ⟧ m ≢  0 
    → ⟨ s , m ⟩⇓ m'  
    → ⟨ While e s , m' ⟩⇓ m'' 
    → ⟨ While e s , m ⟩⇓ m''
  WhileF : {m : Memory} {e : ASTExpS} {s : ASTStmS}
    → ⟦ e ⟧ m ≡ 0 
    → ⟨ While e s , m ⟩⇓ m


-- TRANSFORMED LANGUAGE SEMANTICS
-- State of the memory at a certain program point for the transformed program.
Memoryₜ : Set _
Memoryₜ = Vec (List ℕ) n

-- TODO(minor): Dirty list lookup and update implementations, there's probably a cleaner way of doing this.
lookupOrDefault : ℕ → List ℕ → ℕ
lookupOrDefault _ [] = 0
lookupOrDefault 0 (x ∷ xs) = x
lookupOrDefault (suc n) (x ∷ xs) = lookupOrDefault n xs

safeListUpdate : List ℕ → ℕ → ℕ → List ℕ
safeListUpdate [] _ _ = []
safeListUpdate (x ∷ xs) 0 v = v ∷ xs
safeListUpdate (x ∷ xs) (suc n) v = x ∷ (safeListUpdate xs n v)

-- Update the value of a variable in memory of the transformed program.
infixl 6 _[_↦_]ₜ
_[_↦_]ₜ : Memoryₜ → Fin n × ℕ → ℕ → Memoryₜ
m [ (name , index) ↦ v ]ₜ = 
  m [ name ]≔ (safeListUpdate (lookup m name) index v)

-- Semantic evaluation of tranformed expressions.
-- TODO(minor): Add the rest of the arythmetic operations besides ADD to the ASTExp type.
⟦_⟧ₜ : ASTExp → Memoryₜ → ℕ
⟦ INTVAL n ⟧ₜ m = n
⟦ VAR (name , index) ⟧ₜ m = lookupOrDefault index (lookup m name)       
⟦ ADD exp exp' ⟧ₜ m = ⟦ exp ⟧ₜ m + ⟦ exp' ⟧ₜ m
  
-- Big step semantics of transformed statements.
infixl 5 ⟨_,_⟩⇓ₜ_
data ⟨_,_⟩⇓ₜ_ : ASTStm → Memoryₜ → Memoryₜ → Set where
  Skipₜ : {m : Memoryₜ} → ⟨ SKIP , m ⟩⇓ₜ m
  Seqₜ : {m m' m'' : Memoryₜ} {s₁ s₂ : ASTStm}
    → ⟨ s₁ , m ⟩⇓ₜ m'  
    → ⟨ s₂ , m' ⟩⇓ₜ m'' 
    → ⟨ SEQ s₁ s₂ , m ⟩⇓ₜ m'' 
  Assignₜ : {m : Memoryₜ} {x : Fin n × ℕ} {e : ASTExp} 
    → ⟨ ASSIGN x e , m ⟩⇓ₜ m [ x  ↦ ⟦ e ⟧ₜ m ]ₜ
  IfTₜ : {m m' : Memoryₜ} {e : ASTExp} {v : ℕ} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ₜ m ≡ v
    → v ≢  0 
    → ⟨ s₁ , m ⟩⇓ₜ m' 
    → ⟨ IF0 e s₁ s₂ , m ⟩⇓ₜ m'  
  IfFₜ : {m m' : Memoryₜ} {e : ASTExp} {s₁ s₂ : ASTStm}
    → ⟦ e ⟧ₜ m ≡ 0 
    → ⟨ s₂ , m ⟩⇓ₜ m' 
    → ⟨ IF0 e s₁ s₂ , m ⟩⇓ₜ m'  
  WhileTₜ : {m m' m'' : Memoryₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≢  0 
    → ⟨ s , m ⟩⇓ₜ m'  
    → ⟨ WHILE e s , m' ⟩⇓ₜ m'' 
    → ⟨ WHILE e s , m ⟩⇓ₜ m''
  WhileFₜ : {m : Memoryₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≡ 0 
    → ⟨ WHILE e s , m ⟩⇓ₜ m


-- CORRECTNESS PROOF

lookupₜ : Memoryₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ active x = lookupOrDefault (lookup active x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set.
_==ₘ_-_ : Memory → Memoryₜ → 𝒜 → Set
m ==ₘ mₜ - active = ∀ x → lookup m x ≡ lookupₜ mₜ active x

-- Semantic equality of expression and its transformed counterpart.
-- TODO(major): This only returns the first half of the thesis from the Lemma 3. I'll need to define the second half at some point.
expEquality : {e : ASTExpS} {m : Memory} {mₜ : Memoryₜ} {v v' : ℕ} {active : 𝒜}
  → m ==ₘ mₜ - active
  → ⟦ e ⟧ m ≡ v 
  → ⟦ transExp e active ⟧ₜ mₜ ≡ v' 
  → v ≡ v' 
expEquality {IntVal n} {m} {mₜ} {.(⟦ IntVal n ⟧ m)} {.(⟦ transExp (IntVal n) a ⟧ₜ mₜ)} {a} _ refl refl = refl
expEquality {Var x} {m} {mₜ} {.(⟦ Var x ⟧ m)} {.(⟦ transExp (Var x) a ⟧ₜ mₜ)} {a} m=mt refl refl = m=mt x
expEquality {Add e1 e2} {m} {mₜ} {.(⟦ Add e1 e2 ⟧ m)} {.(⟦ transExp (Add e1 e2) a ⟧ₜ mₜ)} {a} m=mt refl refl = 
  let expEq1 = expEquality {e1} {m} {mₜ} {⟦ e1 ⟧ m} {⟦ transExp e1 a ⟧ₜ mₜ} {a} m=mt refl refl
      expEq2 = expEquality {e2} {m} {mₜ} {⟦ e2 ⟧ m} {⟦ transExp e2 a ⟧ₜ mₜ} {a} m=mt refl refl
   in cong₂ _+_ expEq1 expEq2

-- Correctness of the program transformation.
-- TODO(major): Implement.
correctness : {s : ASTStmS} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {active : 𝒜}
  → ⟨ s , m ⟩⇓ m'
  → ⟨ proj₁ (transStm s active) , mₜ ⟩⇓ₜ mₜ'
  → m ==ₘ mₜ - active
  → m' ==ₘ mₜ' - (proj₂ (transStm s active))

correctness {x := e} {m} {.(m [ x ↦ ⟦ e ⟧ m ])} {mₜ} {.(mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  Assign
  Assignₜ 
  meq = {!   !}

correctness {⟦ x := e ⟧} {m} {.(m [ x ↦ ⟦ e ⟧ m ])} {mₜ} {.(mₜ [ x , suc (lookup a x) ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  AssignBr 
  Assignₜ 
  meq = {!   !}

-- TODO(major): Apparently, I'll also need Lemma 4 for the end of the proof.
correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {.sT} {.sF} em=v v<>0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {s₁} {s₂} em'=v' v'<>0 d') 
  meq = {! !}

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {_} {_} em=v v<>0 d) 
  (IfFₜ em'=0 d') 
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {v} {0} {a} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfF em=0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {_} {v} {_} {_} em'=v v<>0 d') 
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {0} {v} {a} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

correctness {If0 x s s₁} {m} {m'} {mₜ} {mₜ'} {a} (IfF x₁ d) (IfFₜ x₂ d') meq = {!   !}

correctness {While x s} {m} {m'} {mₜ} {mₜ'} {a} (WhileT x₁ d d₁) d' meq = {!  !}

correctness {While x s} {m} {.m} {mₜ} {mₜ'} {a} (WhileF x₁) d' meq = {!  !}

correctness {Seq s s₁} {m} {m'} {mₜ} {mₜ'} {a} 
  (Seq {m = .m} {m' = m2} {m'' = .m'} d d₁) 
  (Seqₜ {m = .mₜ} {m' = mt2} {m'' = .mₜ'} d' d'') 
  meq = 
    let h1 = correctness {s} {m} {m2} {mₜ} {mt2} d d' meq
     in correctness d₁ d'' h1

correctness {Skip} {m} {.m} {mₜ} {.mₜ} {a} Skip Skipₜ meq = meq
