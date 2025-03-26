module Transformation.Semantic {n} where

open import Data.Empty
open import Data.Fin
  hiding (_+_ ; pred)
  renaming (_≟_ to _≟f_)
open import Data.Fin.Properties
  hiding (≤∧≢⇒<)
open import Data.List
  hiding (lookup ; [_])
open import Data.Nat 
  renaming (_≟_ to _≟ₙ_ ; _<_ to _<ₙ_ ; _≤_ to _≤ₙ_ )
open import Data.Nat.Properties
  hiding (<⇒≢ )
open import Data.Product 
open import Data.Vec.Base
  hiding (length)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import Transformation.Transformation {n}
open import Transformation.VariableSet {n}


-- BRACKETED LANGUAGE SEMANTICS
-- State of the memory at a certain program point for the bracketed program.
Memory : Set _
Memory = Vec ℕ n

-- Update the value of a variable in memory.
infixl 6 _[_↦_]
_[_↦_] : Memory → Fin n → ℕ → Memory
m [ name ↦ v ] = m [ name ]≔ v

-- Semantic evaluation of expressions.
⟦_⟧ₑ : ASTExpS → Memory → ℕ
⟦ IntVal n ⟧ₑ m = n
⟦ Var name ⟧ₑ m = lookup m name
⟦ Add exp exp' ⟧ₑ m = ⟦ exp ⟧ₑ m + ⟦ exp' ⟧ₑ m
  
-- Big step semantics of statements.
infixl 5 ⟨_,_⟩⇓_
data ⟨_,_⟩⇓_ : ASTStmS → Memory → Memory → Set where
  Skip : {m : Memory} → ⟨ Skip , m ⟩⇓ m
  Seq : {m m' m'' : Memory}{s₁ s₂ : ASTStmS}
    → ⟨ s₁ , m ⟩⇓ m'  
    → ⟨ s₂ , m' ⟩⇓ m'' 
    → ⟨ Seq s₁ s₂ , m ⟩⇓ m'' 
  Assign : {m : Memory} {x : Fin n} {e : ASTExpS} 
    → ⟨ x := e , m ⟩⇓ m [ x  ↦ ⟦ e ⟧ₑ m ]
  AssignBr : {m : Memory} {x : Fin n} {e : ASTExpS} 
    → ⟨ ⟦ x := e ⟧ , m ⟩⇓ m [ x  ↦ ⟦ e ⟧ₑ m ]
  IfT : {m m' : Memory} {e : ASTExpS} {v : ℕ} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ s₁ , m ⟩⇓ m' 
    → ⟨ If0 e s₁ s₂ , m ⟩⇓ m'  
  IfF : {m m' : Memory} {e : ASTExpS} {s₁ s₂ : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ 0 
    → ⟨ s₂ , m ⟩⇓ m' 
    → ⟨ If0 e s₁ s₂ , m ⟩⇓ m'  
  WhileT : {m m' m'' : Memory} {e : ASTExpS} {v : ℕ} {s : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ v
    → v ≢  0 
    → ⟨ s , m ⟩⇓ m'  
    → ⟨ While e s , m' ⟩⇓ m'' 
    → ⟨ While e s , m ⟩⇓ m''
  WhileF : {m : Memory} {e : ASTExpS} {s : ASTStmS}
    → ⟦ e ⟧ₑ m ≡ 0 
    → ⟨ While e s , m ⟩⇓ m


-- TRANSFORMED LANGUAGE SEMANTICS
-- State of the memory at a certain program point for the transformed program.
Memoryₜ : Set _
Memoryₜ = Vec (List ℕ) n

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
_[_↦_]ₜ : Memoryₜ → TransVariable → ℕ → Memoryₜ
m [ (name , index) ↦ v ]ₜ = 
  m [ name ]≔ (safeListUpdate (lookup m name) index v)

-- Semantic evaluation of tranformed expressions.
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
  Assignₜ : {m : Memoryₜ} {x : TransVariable} {e : ASTExp} 
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
  WhileTₜ : {m m' m'' : Memoryₜ} {e : ASTExp} {v : ℕ} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≡ v
    → v ≢  0  
    → ⟨ s , m ⟩⇓ₜ m'  
    → ⟨ WHILE e s , m' ⟩⇓ₜ m'' 
    → ⟨ WHILE e s , m ⟩⇓ₜ m''
  WhileFₜ : {m : Memoryₜ} {e : ASTExp} {s : ASTStm}
    → ⟦ e ⟧ₜ m ≡ 0 
    → ⟨ WHILE e s , m ⟩⇓ₜ m


-- CORRECTNESS PROOF PRELIMINARY DEFINITIONS
-- Lookup of a variable in a transformed memory.
lookupₜ : Memoryₜ  → 𝒜 → Fin n → ℕ
lookupₜ mₜ active x = lookupOrDefault (lookup active x) (lookup mₜ x)

-- Equality between a memory and the projection of a transformed memory on an active set.
_==ₘ_-_ : Memory → Memoryₜ → 𝒜 → Set
m ==ₘ mₜ - active = ∀ x → lookup m x ≡ lookupₜ mₜ active x

-- Equality between two memory projections on active sets.
_-_==ₘₜ_-_ : Memoryₜ → 𝒜 → Memoryₜ → 𝒜 → Set
m1ₜ - a1 ==ₘₜ m2ₜ - a2 = ∀ x → lookupₜ m1ₜ a1 x ≡ lookupₜ m2ₜ a2 x

-- Transitive property between ==ₘ and ==ₘₜ .
==ₘ-trans : {m : Memory} {mₜ mₜ' : Memoryₜ} {a a' : 𝒜}
  → m ==ₘ mₜ - a
  → mₜ - a ==ₘₜ mₜ' - a'
  → m ==ₘ mₜ' - a'
==ₘ-trans meq meq2 var = trans (meq var) (meq2 var)   


wellFormed : Memoryₜ → 𝒜 → Set
wellFormed mₜ a = ∀ x → lookup a x <ₙ length (lookup mₜ x)

data wellFormedStm : ASTStmS → Memoryₜ → 𝒜 → Set where
  SkipWF : {m : Memoryₜ} {a : 𝒜}
    → wellFormed m a
    → wellFormedStm Skip m a
  SeqWF : {s s' : ASTStmS} {m : Memoryₜ} {a : 𝒜}
    → wellFormedStm s m a
    → wellFormedStm s' m (proj₂ (transStm s a))
    → wellFormedStm (Seq s s') m a
  AssignWF : {v : Fin n} {e : ASTExpS} {m : Memoryₜ} {a : 𝒜}
    → wellFormed m a
    → wellFormedStm (v := e) m a
  AssignBrWF : {v : Fin n} {e : ASTExpS} {m : Memoryₜ} {a : 𝒜}  
    → wellFormed m (proj₂ (transStm ⟦ v := e ⟧ a))
    → wellFormedStm ⟦ v := e ⟧ m a
  IfWF : {e : ASTExpS} {s s' : ASTStmS} {m : Memoryₜ} {a : 𝒜}
    → wellFormed m (proj₂ (transStm (If0 e s s') a))
    → wellFormedStm s m a
    → wellFormedStm s' m a
    → wellFormedStm (If0 e s s') m a
  WhileWF : {e : ASTExpS} {s : ASTStmS} {m : Memoryₜ} {a : 𝒜}
    → wellFormed m (merge𝒜 a (proj₂ (transStm s a)))
    → wellFormedStm s m (merge𝒜 a (proj₂ (transStm s a)))
    → wellFormedStm (While e s) m a

-- LEMMA 3 OF THE CORRECTNESS PROOF
-- Semantic equality of expression and its transformed counterpart.
expEquality : {e : ASTExpS} {m : Memory} {mₜ : Memoryₜ} {v v' : ℕ} {active : 𝒜}
  → m ==ₘ mₜ - active
  → ⟦ e ⟧ₑ m ≡ v 
  → ⟦ transExp e active ⟧ₜ mₜ ≡ v' 
  → v ≡ v' 
expEquality {IntVal n} {m} {mₜ} {.(⟦ IntVal n ⟧ₑ m)} {.(⟦ transExp (IntVal n) a ⟧ₜ mₜ)} {a} _ refl refl = refl
expEquality {Var x} {m} {mₜ} {.(⟦ Var x ⟧ₑ m)} {.(⟦ transExp (Var x) a ⟧ₜ mₜ)} {a} m=mt refl refl = m=mt x
expEquality {Add e1 e2} {m} {mₜ} {.(⟦ Add e1 e2 ⟧ₑ m)} {.(⟦ transExp (Add e1 e2) a ⟧ₜ mₜ)} {a} m=mt refl refl = 
  let expEq1 = expEquality {e1} {m} {mₜ} {⟦ e1 ⟧ₑ m} {⟦ transExp e1 a ⟧ₜ mₜ} {a} m=mt refl refl
      expEq2 = expEquality {e2} {m} {mₜ} {⟦ e2 ⟧ₑ m} {⟦ transExp e2 a ⟧ₜ mₜ} {a} m=mt refl refl
   in cong₂ _+_ expEq1 expEq2


-- MEMORY LOOKUP PROPERTIES
lookupx∘changex : 
  {A : Set} {m : ℕ} {v : A} (index : Fin m) (vector : Vec A m) 
  → lookup (vector [ index ]≔ v) index ≡ v
lookupx∘changex zero (head ∷ tail) = refl
lookupx∘changex (suc x) (head ∷ tail) = lookupx∘changex x tail 

lookupy∘changex : 
  {A : Set} {m : ℕ} {v : A} (i1 i2 : Fin m) (vector : Vec A m)
  → i2 ≢  i1
  → lookup (vector [ i1 ]≔ v) i2 ≡ lookup vector i2
lookupy∘changex zero zero vector i2!=i1 = ⊥-elim (i2!=i1 refl)
lookupy∘changex zero (suc x) (head ∷ tail) i2!=i1 = refl
lookupy∘changex (suc x) zero (head ∷ tail) i2!=i1 = refl
lookupy∘changex (suc x) (suc y) (head ∷ tail) i2!=i1 = lookupy∘changex x y tail (i2!=i1 ∘ cong suc)  

listLookupx∘listUpdatex : 
  {v : ℕ} (index : ℕ) (list : List ℕ) 
  → index <ₙ length list
  → lookupOrDefault index (safeListUpdate list index v) ≡ v
listLookupx∘listUpdatex index [] i<0 = ⊥-elim (n≮0 i<0)
listLookupx∘listUpdatex 0 (head ∷ tail) _ = refl
listLookupx∘listUpdatex (suc index) (head ∷ tail) si<ll = listLookupx∘listUpdatex index tail (<-pred si<ll)

lookupₜx∘changeₜx : 
  {m v activeVar : ℕ} (index : Fin m) (vector : Vec (List ℕ) m) 
  → activeVar <ₙ length (lookup vector index)
  → lookupOrDefault activeVar (lookup (vector [ index ]≔ (safeListUpdate (lookup vector index) activeVar v)) index) ≡ v
lookupₜx∘changeₜx {_} {_} {activeVar} zero (head ∷ tail) aV<lh = listLookupx∘listUpdatex activeVar head aV<lh
lookupₜx∘changeₜx (suc x) (head ∷ tail) aV<liv = lookupₜx∘changeₜx x tail aV<liv

lookupₜy∘changeₜx : 
  {m v activeVar activeVar2 : ℕ} (i1 i2 : Fin m) (vector : Vec (List ℕ) m) 
  → i2 ≢  i1
  → lookupOrDefault activeVar (lookup (vector [ i1 ]≔ (safeListUpdate (lookup vector i1) activeVar2 v)) i2) ≡ lookupOrDefault activeVar (lookup vector i2)
lookupₜy∘changeₜx zero zero vector i2!=i1 = ⊥-elim (i2!=i1 refl)
lookupₜy∘changeₜx zero (suc x) (head ∷ tail) i2!=i1 = refl
lookupₜy∘changeₜx (suc x) zero (head ∷ tail) i2!=i1 = refl
lookupₜy∘changeₜx (suc x) (suc y) (head ∷ tail) i2!=i1 = lookupₜy∘changeₜx x y tail (i2!=i1 ∘ cong suc)  

lengthUpdateL=lengthL : (list : List ℕ) → (index : ℕ) → (value : ℕ) 
  → length (safeListUpdate list index value) ≡ length list
lengthUpdateL=lengthL [] _ _ = refl
lengthUpdateL=lengthL (x ∷ xs) zero _ = refl
lengthUpdateL=lengthL (x ∷ xs) (suc index) value = cong suc (lengthUpdateL=lengthL xs index value)

wellFormed-trans : {s : ASTStm} {mₜ mₜ' : Memoryₜ} {a : 𝒜} 
  → wellFormed mₜ a 
  → ⟨ s , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ' a
wellFormed-trans wFmₜa Skipₜ = wFmₜa
wellFormed-trans {_} {mₜ} {mₜ'} {a} wFmₜa (Assignₜ {_} {x , index} {e}) varName with varName ≟f x
...   | yes vN=x = let -- lookup mt' x == (safeListUpdate ...)
                       lmₜ'x=lUmₜx = lookupx∘changex x mₜ
                       -- length (safeListUpdate (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)) ≡ length (lookup mₜ x)
                       lenlUmₜx=lenlmₜ'x = lengthUpdateL=lengthL (lookup mₜ x) index (⟦ e ⟧ₜ mₜ)
                       -- length (lookup (mₜ [ x ]≔ v) x) ≡ length (lookup mₜ x)
                       lenlmₜ'x=lenlmₜx = trans (cong length lmₜ'x=lUmₜx) lenlUmₜx=lenlmₜ'x
                       -- length (lookup (mₜ [ varName ]≔ v) varName) ≡ length (lookup mₜ varName)
                       lenlmₜ'vN=lenlmₜvN = subst (\v → length (lookup mₜ' v) ≡ length (lookup mₜ v)) (sym vN=x) lenlmₜ'x=lenlmₜx
                    in subst (\v → lookup a varName <ₙ v) (sym lenlmₜ'vN=lenlmₜvN) (wFmₜa varName)
...   | no vN<>x = subst (\v → lookup a varName <ₙ length v) (sym (lookupy∘changex x varName mₜ vN<>x)) (wFmₜa varName)
wellFormed-trans {_} {_} {_} {a} wFmₜa (Seqₜ d d') = 
  wellFormed-trans {_} {_} {_} {a} (wellFormed-trans {_} {_} {_} {a} wFmₜa d) d'
wellFormed-trans {_} {_} {_} {a} wFmₜa (IfTₜ _ _ d) = wellFormed-trans {_} {_} {_} {a} wFmₜa d
wellFormed-trans {_} {_} {_} {a} wFmₜa (IfFₜ _ d) = wellFormed-trans {_} {_} {_} {a} wFmₜa d
wellFormed-trans {_} {_} {_} {a} wFmₜa (WhileTₜ _ _ d d') = 
  wellFormed-trans {_} {_} {_} {a} (wellFormed-trans {_} {_} {_} {a} wFmₜa d) d'
wellFormed-trans wFmₜa (WhileFₜ _) = wFmₜa

wellFormedStmTransitive : {s : ASTStmS} {sₜ : ASTStm} {m m' : Memoryₜ} {a : 𝒜}
  → wellFormedStm s m a
  → ⟨ sₜ , m ⟩⇓ₜ m'
  → wellFormedStm s m' a
wellFormedStmTransitive {_} {_} {_} {_} {a} (SkipWF wFmₜa) d = 
  SkipWF (wellFormed-trans {_} {_} {_} {a} wFmₜa d)
wellFormedStmTransitive {_} {_} {_} {_} {a} (AssignWF wFmₜa) d = 
  AssignWF (wellFormed-trans {_} {_} {_} {a} wFmₜa d)
wellFormedStmTransitive (AssignBrWF {v} {e} {_} {a} wFmₜa') d = 
  AssignBrWF (wellFormed-trans {_} {_} {_} {proj₂ (transStm ⟦ v := e ⟧ a)} wFmₜa' d)
wellFormedStmTransitive (SeqWF wFsmₜa wFs'mₜa) d = 
  SeqWF (wellFormedStmTransitive wFsmₜa d) 
        (wellFormedStmTransitive wFs'mₜa d) 
wellFormedStmTransitive (IfWF {e} {s} {s'} {_} {a} wFmₜa' wFsmₜa wFs'mₜa) d = 
  IfWF (wellFormed-trans {_} {_} {_} {proj₂ (transStm (If0 e s s') a)} wFmₜa' d) 
       (wellFormedStmTransitive wFsmₜa d) 
       (wellFormedStmTransitive wFs'mₜa d) 
wellFormedStmTransitive (WhileWF {e} {s} {_} {a} wFmₜa' wFsmₜa') d = 
  WhileWF (wellFormed-trans {_} {_} {_} {merge𝒜 a (proj₂ (transStm s a))} wFmₜa' d) 
          (wellFormedStmTransitive wFsmₜa' d) 


-- LEMMA 4 OF THE CORRECTNESS PROOF
-- Equality of lookups of a variable in two memories after the active set assignment
-- for that variable has been executed. 
𝒜memEqPostVar : {currVar : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {a a' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ assignActiveSetAux currVar cV<n a a' , mₜ ⟩⇓ₜ mₜ'
  → currVar <ₙ toℕ varName
  → lookup mₜ varName ≡ lookup mₜ' varName

𝒜memEqPostVar {zero} {varName} {z<n} {a} {a'} {_} {_} _ _ with lookup a (fromℕ< z<n) ≟ₙ lookup a' (fromℕ< z<n)
𝒜memEqPostVar {zero} {varName} {_} {a} {a'} {mₜ} {.mₜ} Skipₜ _        | yes _ = refl
𝒜memEqPostVar {zero} {varName} {z<n} {a} {a'} {mₜ} {mₜ'} Assignₜ z<vN | no _ =
  let -- toℕ (fromℕ< z<n) ≡ 0
      toNz=0 = toℕ-fromℕ< z<n
      -- toℕ (fromℕ< z<n) <ₙ toℕ varName
      toNz<toNvN = subst (\x → x <ₙ toℕ varName) (sym toNz=0) z<vN
      -- (fromℕ< z<n) < varName
      z<vN = toℕ-cancel-< toNz<toNvN
      -- vN ≢  (fromℕ< z<n)
      vN<>z = ≢-sym (<⇒≢  z<vN)
   in sym (lookupy∘changex (fromℕ< z<n) varName mₜ vN<>z)

𝒜memEqPostVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {_} {_} _ _ with lookup a (fromℕ< cV<n) ≟ₙ lookup a' (fromℕ< cV<n)
𝒜memEqPostVar currVar@{suc currVar'} {varName} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) cV<vN    | yes _ = 
  𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
𝒜memEqPostVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {mₜ} {mₜ'} (Seqₜ Assignₜ d) cV<vN | no _ = 
  let -- toℕ (fromℕ< cV<n) ≡ currVar
      toNcV=cV = toℕ-fromℕ< cV<n
      -- toℕ (fromℕ< cV<n) <ₙ toℕ varName
      toNcV<toNvN = subst (\x → x <ₙ toℕ varName) (sym toNcV=cV) cV<vN
      -- (fromℕ< cV<n) < varName
      fNcV<vN = toℕ-cancel-< toNcV<toNvN
      -- varName ≢  (fromℕ< cV<n)
      vN<>fNcV = ≢-sym (<⇒≢  fNcV<vN)
      -- lookup mₜ varName ≡ lookup mₜ1 varName
      lmtvN=lmt1vN = sym (lookupy∘changex (fromℕ< cV<n) varName mₜ vN<>fNcV)
      -- lookup mₜ1 varName ≡ lookup mₜ' varName
      lmt1vN=lmt'vN = 𝒜memEqPostVar d (<-pred (m<n⇒m<1+n cV<vN))
   in trans lmtvN=lmt1vN lmt1vN=lmt'vN  

-- Equality of lookups of a variable in two memories before the active set assignment
-- for that variable has been executed. 
𝒜memEqPreVar : {currVar : ℕ} {varName : Fin n} {cV<n : currVar <ₙ n} {a a' : 𝒜} {mₜ mₜ' : Memoryₜ}
  → ⟨ assignActiveSetAux currVar cV<n a a' , mₜ ⟩⇓ₜ mₜ'
  → toℕ varName ≤ₙ currVar
  → wellFormed mₜ a
  → lookupₜ mₜ a' varName ≡ lookupₜ mₜ' a varName
𝒜memEqPreVar {zero} {zero} {_} {a} {a'} {_} {_} _ _ _ with lookup a zero ≟ₙ lookup a' zero
𝒜memEqPreVar {zero} {zero} {_} {_} {_} {mₜ} {.mₜ} Skipₜ _ _   | yes laz=la'z = 
  cong (\x → lookupOrDefault x (lookup mₜ zero)) (sym laz=la'z)
𝒜memEqPreVar {zero} {zero} {_} {a} {a'} {mₜ} {_} Assignₜ _ wFmₜa | no _ = 
  sym (lookupₜx∘changeₜx {n} {_} {lookup a zero} zero mₜ (wFmₜa zero))
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {_} {_} _ _ _ with toℕ varName ≟ₙ currVar | lookup a (fromℕ< cV<n) ≟ₙ lookup a' (fromℕ< cV<n)
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {_} {_} (Seqₜ Skipₜ d) _ _                     | yes vN=cV | yes lacV=la'cV = 
  let lmtvN=lmt'vN = 𝒜memEqPostVar d (subst (\x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      -- varName ≡ fromℕ< cV<n
      vN=cV = toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n)))
      lavN=la'vN = subst (\x → lookup a x ≡ lookup a' x) (sym vN=cV) lacV=la'cV
   in cong₂ (\x y → lookupOrDefault x y) (sym lavN=la'vN) lmtvN=lmt'vN
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {mₜ} {mₜ'} (Seqₜ {.mₜ} {mₜ1} {.mₜ'} Assignₜ d) _ wFmₜa | yes vN=cV | no _ = 
  let finCurrVar = fromℕ< cV<n
      -- lookup mt1 varName = lookup mt' varName
      lmt1vN=lmt'vN = 𝒜memEqPostVar d (subst (\x → currVar' <ₙ x) (sym vN=cV) (n<1+n currVar'))
      -- lookupOrDefault (lookup a finCurrVar) (lookup mt1 finCurrVar) == lookupOrDefault (lookup a' finCurrVar) (lookup mt finCurrVar)
      lamt1cV=la'mtcV = lookupₜx∘changeₜx {n} {_} {lookup a finCurrVar} finCurrVar mₜ (wFmₜa finCurrVar)
      -- fromℕ< cV<n ≡ varName
      cV=vN = sym (toℕ-injective (trans vN=cV (sym (toℕ-fromℕ< cV<n))))
      -- lookupOrDefault (lookup a varName) (lookup mt1 varName) == lookupOrDefault (lookup a' varName) (lookup mt varName)
      lamt1vN=la'mtvN = subst (\x → lookupₜ mₜ a' x ≡ lookupₜ mₜ1 a x) cV=vN (sym lamt1cV=la'mtcV)
   in subst (\x → lookupₜ mₜ a' varName ≡ lookupOrDefault (lookup a varName) x) lmt1vN=lmt'vN lamt1vN=la'mtvN
𝒜memEqPreVar currVar@{suc currVar'} {varName} {_} {a} {a'} {_} {_} (Seqₜ Skipₜ d) vN≤cV wFmₜa                     | no vN<>cV | yes _ = 
  𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV)) wFmₜa
𝒜memEqPreVar currVar@{suc currVar'} {varName} {cV<n} {a} {a'} {mₜ} {mₜ'} (Seqₜ assign@Assignₜ d) vN≤cV wFmₜa               | no vN<>cV | no _ =
  let -- varName <> fromℕ< cV<n
      vN<>fromN<cV = (\vN=fromN<cV → vN<>cV (subst (\x → toℕ x ≡ currVar) (sym vN=fromN<cV) (toℕ-fromℕ< cV<n))) 
      -- lookupₜ mₜ1 a' varName ≡ lookupₜ mₜ a' varName
      lmt1a'vN=lmta'vN = lookupₜy∘changeₜx (fromℕ< cV<n) varName mₜ vN<>fromN<cV
      -- lookupₜ mₜ1 a' varName ≡ lookupₜ mₜ' a varName
      lmt1a'vN=lmt'avN = 𝒜memEqPreVar d (m<1+n⇒m≤n (≤∧≢⇒< vN≤cV vN<>cV)) (wellFormed-trans {_} {_} {_} {a} wFmₜa assign)
   in trans (sym lmt1a'vN=lmta'vN) lmt1a'vN=lmt'avN

-- Memory equality after executing an active set assignment.
:=𝒜-memEq : {a a' : 𝒜} {mₜ mₜ' : Memoryₜ} 
  → ⟨ a' :=𝒜 a , mₜ ⟩⇓ₜ mₜ'
  → wellFormed mₜ a'
  → mₜ - a ==ₘₜ mₜ' - a'
:=𝒜-memEq {a} {a'} {mₜ} {mₜ'} d wFmₜa varName with n ≟ₙ zero 
...                                        | no n<>0 = let n' , n=sn' = 0<n=>n=sn' (n≢0⇒n>0 n<>0)
                                                        in 𝒜memEqPreVar d (subst (\x → toℕ varName ≤ₙ x) (cong pred n=sn') (toℕ≤pred[n] varName)) wFmₜa
:=𝒜-memEq {[]} {[]} {mₜ} {.mₜ} Skipₜ _ varName | yes _ = refl

-- CORRECTNESS PROOF
-- Correctness of the program transformation for the While case.
whileCorrectness : {e : ASTExpS} {s : ASTStmS} {e' : ASTExp} {s' : ASTStm} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {A A₁ A₂ : 𝒜}
  → ⟨ While e s , m ⟩⇓ m'
  → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
  → e' ≡ transExp e A₁
  → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
  → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
  → A₂ ≡ proj₂ (transStm s A₁)
  → wellFormedStm (While e s) mₜ A
  → m ==ₘ mₜ - A₁
  → m' ==ₘ mₜ' - A₁

-- Correctness of the program transformation.
correctness : {s : ASTStmS} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {active : 𝒜}
  → ⟨ s , m ⟩⇓ m'
  → ⟨ proj₁ (transStm s active) , mₜ ⟩⇓ₜ mₜ'
  → wellFormedStm s mₜ active
  → m ==ₘ mₜ - active
  → m' ==ₘ mₜ' - (proj₂ (transStm s active))

-- TODO(minor): Rewrite this using a let and type explanations for the difficult terms like I did in AssignmentId.
correctness s@{x := e} {m} {.(m [ x ↦ ⟦ e ⟧ₑ m ])} {mₜ} {.(mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ)} {a} 
  Assign
  Assignₜ
  (AssignWF wFmₜa)
  meq varName with varName ≟f x
...              | yes vN=x = trans 
                                -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v'
                                (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v
                                  (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === lookup (m [ varName ]≔ ⟦ e ⟧ₑ m) varName
                                    (sym (cong (λ y → lookup (m [ y ]≔ ⟦ e ⟧ₑ m) varName) vN=x))
                                  -- lookup (m [ varName ]≔ v) varName ≡ v
                                    (lookupx∘changex varName m)
                                  )
                                  -- v === v'
                                  (expEquality {e} {m} {mₜ} meq refl refl)
                                ) 
                                -- v' === lookup (mₜ [ x , lookup a x ↦ ⟦ transExp e a ⟧ₜ mₜ) varName
                                (trans 
                                  -- v' === lookupOrDefault activeVar (lookup (mₜ [ varName ]≔ (safeListUpdate (lookup mₜ varName) activeVar v)) varName)
                                  (sym (lookupₜx∘changeₜx varName mₜ (wFmₜa varName)))
                                  -- lookupOrDefault activeVar (lookup (mₜ [ varName ]≔ (safeListUpdate (lookup mₜ varName) activeVar v)) varName)
                                  -- ===
                                  -- lookupOrDefault activeVar (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (lookup a x) v)) varName)
                                  (cong (λ y → lookupOrDefault (lookup a varName) (lookup (mₜ [ y , lookup a y ↦ ⟦ transExp e a ⟧ₜ mₜ ]ₜ) varName)) vN=x)
                                )
...              | no vN!=x = trans 
                                (trans 
                                  (lookupy∘changex x varName m vN!=x)
                                  (meq varName)
                                ) 
                                (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))

-- TODO(minor): Same as above, rewrite this using a let and type explanations.
correctness s@{⟦ x := e ⟧} {m} {.(m [ x ↦ ⟦ e ⟧ₑ m ])} {mₜ} {mₜ'} {a} 
  AssignBr 
  Assignₜ 
  (AssignBrWF wFmₜa')
  meq varName with varName ≟f x
...              | yes vN=x = trans 
                                -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v'
                                (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === v
                                  (trans 
                                  -- lookup (m [ x ]≔ ⟦ e ⟧ₑ m) varName === lookup (m [ varName ]≔ ⟦ e ⟧ₑ m) varName
                                    (sym (cong (λ y → lookup (m [ y ]≔ ⟦ e ⟧ₑ m) varName) vN=x))
                                  -- lookup (m [ varName ]≔ v) varName ≡ v
                                    (lookupx∘changex varName m)
                                  )
                                  -- v === v'
                                  (expEquality {e} {m} {mₜ} meq refl refl)
                                )
                                -- v' ≡ lookupₜ mₜ' a' varName
                                (sym (trans
                                  -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) varName) (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')) varName)
                                  -- ===
                                  -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                  (trans
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) varName) (lookup (mₜ [ x , suc (lookup a x) ↦ v' ]ₜ) varName)
                                    -- ===
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    (trans 
                                      (cong (λ y → lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) y) (lookup (mₜ [ x ]≔ (safeListUpdate (lookup mₜ x) (suc (lookup a x)) (⟦ transExp e a ⟧ₜ mₜ))) y)) vN=x)
                                      (cong (λ y → lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) y) (lookupx∘changex x mₜ))
                                    )
                                    -- lookupOrDefault (lookup (a [ x ]≔ suc (lookup a x)) x) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    -- ===
                                    -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v')
                                    (cong (λ y → lookupOrDefault y (safeListUpdate (lookup mₜ x) (suc (lookup a x)) (⟦ transExp e a ⟧ₜ mₜ))) (lookupx∘changex x a))
                                  )
                                  -- lookupOrDefault (suc (lookup a x)) (safeListUpdate (lookup mₜ x) (suc (lookup a x)) v') ≡ v'
                                  (listLookupx∘listUpdatex (suc (lookup a x)) (lookup mₜ x) (subst (λ y → y <ₙ length (lookup mₜ x)) (lookupx∘changex x a) (wFmₜa' x)))
                                ))
...              | no vN!=x = trans 
                                -- lookup m' varName ≡ lookupₜ mₜ active varName
                                (trans 
                                  -- lookup m' varName ≡ lookup m varName
                                  (lookupy∘changex x varName m vN!=x)
                                  -- lookup m varName ≡ lookupₜ mₜ active varName
                                  (meq varName)
                                )
                                -- lookupₜ mₜ active varName ≡ lookupₜ mₜ' active' varName
                                (trans
                                  -- lookupₜ mₜ a varName ≡ lookupₜ mₜ' a varName
                                  (sym (lookupₜy∘changeₜx x varName mₜ vN!=x))
                                  -- lookupₜ mₜ' a varName ≡ lookupₜ mₜ' a' varName
                                  (cong (λ y → lookupOrDefault y (lookup mₜ' varName)) (sym (lookupy∘changex x varName a vN!=x)))  
                                )

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {.sT} {.sF} em=v v<>0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {v'} {sT'} {sF'} em'=v' v'<>0 (Seqₜ {m1} {m2} {m3} d' d''))
  (IfWF wFmₜa' wFsTmₜa _)
  meq = 
    let aT = proj₂ (transStm sT a)
        aF = proj₂ (transStm sF a)
        a' = merge𝒜 aT aF
        m1=mt1a' = correctness {sT} {m} {m'} {mₜ} {m2} {a} d d' wFsTmₜa meq 
        mt1a'=mt2a'' = :=𝒜-memEq {aT} {a'} d'' (wellFormed-trans {_} {_} {_} {a'} wFmₜa' d')
      in ==ₘ-trans {m'} {m2} {mₜ'} {aT} {a'} m1=mt1a' mt1a'=mt2a''

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfT {.m} {.m'} {.cond} {v} {_} {_} em=v v<>0 d) 
  (IfFₜ em'=0 d') 
  _
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {v} {0} {a} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a} 
  (IfF em=0 d) 
  (IfTₜ {.mₜ} {.mₜ'} {_} {v} {_} {_} em'=v v<>0 d') 
  _
  meq = 
    let em=em' = expEquality {cond} {m} {mₜ} {0} {v} {a} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

correctness {If0 cond sT sF} {m} {m'} {mₜ} {mₜ'} {a}
  (IfF {.m} {.m'} {.cond} {.sT} {.sF} em=0 d) 
  (IfFₜ {.mₜ} {.mₜ'} {.(transExp cond a)} {sT'} {sF'} em'=0 (Seqₜ {m1} {m2} {m3} d' d''))
  (IfWF wFmₜa' _ wFsTmₜa)
  meq = 
    let aT = proj₂ (transStm sT a)
        aF = proj₂ (transStm sF a)
        a' = merge𝒜 aT aF
        m1=mt1a' = correctness {sF} {m} {m'} {mₜ} {m2} {a} d d' wFsTmₜa meq
        mt1a'=mt2a'' = :=𝒜-memEq {aF} {a'} d'' (wellFormed-trans {_} {_} {_} {a'} wFmₜa' d')
      in ==ₘ-trans {m'} {m2} {mₜ'} {aF} {a'} m1=mt1a' mt1a'=mt2a''

correctness {While cond s} {m} {m'} {mₜ} {mₜ'} {active} d 
  (Seqₜ {.mₜ} {mₜ1} {.mₜ'} dₜ dₜ') 
  wF@(WhileWF wFmₜa₁ _)
  meq = 
    let A₁ = merge𝒜 active (proj₂ (transStm s active))
        mtA=mt1A1 = :=𝒜-memEq {active} {A₁} {mₜ} {mₜ1} dₜ wFmₜa₁
     in whileCorrectness d dₜ' refl refl refl refl (wellFormedStmTransitive wF dₜ) (==ₘ-trans {m} {mₜ} {mₜ1} {active} {A₁} meq mtA=mt1A1)

correctness {Seq s s₁} {m} {m'} {mₜ} {mₜ'} {a} 
  (Seq {.m} {m2} {.m'} d d₁) 
  (Seqₜ {.mₜ} {mt2} {.mₜ'} d' d'') 
  (SeqWF wFsmₜa wFs₁mₜa')
  meq = 
    let h1 = correctness {s} {m} {m2} {mₜ} {mt2} d d' wFsmₜa meq
        wFs₁mₜ2a' = wellFormedStmTransitive wFs₁mₜa' d'
     in correctness d₁ d'' wFs₁mₜ2a' h1

correctness {Skip} {m} {.m} {mₜ} {.mₜ} {a} Skip Skipₜ _ meq = meq

-- whileCorrectness : {e : ASTExpS} {s : ASTStmS} {e' : ASTExp} {s' : ASTStm} {m m' : Memory} {mₜ mₜ' : Memoryₜ} {A A₁ A₂ : 𝒜}
--   → ⟨ While e s , m ⟩⇓ m'
--   → ⟨ WHILE e' s' , mₜ ⟩⇓ₜ mₜ' 
--   → e' ≡ transExp e A₁
--   → s' ≡ SEQ (proj₁ (transStm s A₁)) (A₁ :=𝒜 A₂)
--   → A₁ ≡ merge𝒜 A (proj₂ (transStm s A))
--   → A₂ ≡ proj₂ (transStm s A₁)
--   → wellFormedStm (While e s) mₜ A
--   → m ==ₘ mₜ - A₁
--   → m' ==ₘ mₜ' - A₁

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileF em=0) 
  (WhileFₜ em'=0) 
  refl refl refl refl _
  meq = meq

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileF em=0) 
  (WhileTₜ {_} {_} {_} {_} {v} {_} em'=v v<>0 _ _)
  refl refl refl refl _
  meq = 
    let em=em' = expEquality {e} {m} {_} {0} {v} {_} meq em=0 em'=v
     in ⊥-elim (v<>0 (sym em=em'))

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileT {.m} {_} {_} {.e} {v} {_} em=v v<>0 _ _) 
  (WhileFₜ em'=0) 
  refl refl refl refl _
  meq = 
    let em=em' = expEquality {e} {m} {_} {v} {0} {_} meq em=v em'=0
     in ⊥-elim (v<>0 em=em')

whileCorrectness {e} {s} {e'} {s'} {m} {m'} {mₜ} {mₜ'} {A} {A₁} {A₂} 
  (WhileT {.m} {m1} {.m'} {.e} {_} {.s} _ _ d d') 
  (WhileTₜ {.mₜ} {mₜ2} {.mₜ'} {cond'} {_} {s'} _ _ dₜ@(Seqₜ {.mₜ} {mₜ1} {.mₜ2} dₜ' dₜ'') dₜ''')
  refl refl refl refl
  wF@(WhileWF wFmₜa₁ wFsmₜA₁)
  meq = 
    let -- m1 ==ₘ mₜ1 - A2
        h = correctness {s} {m} {m1} {mₜ} {mₜ1} {A₁} d dₜ' wFsmₜA₁ meq
        -- mt1 - A2 ==ₘₜ mt2 - A1
        mt1A2=mt2A1 = :=𝒜-memEq {A₂} {A₁} {mₜ1} {mₜ2} dₜ'' (wellFormed-trans {_} {_} {_} {A₁} wFmₜa₁ dₜ')
        -- m' ==ₘ mₜ' - A1
     in whileCorrectness d' dₜ''' refl refl refl refl (wellFormedStmTransitive wF dₜ) (==ₘ-trans {m1} {mₜ1} {mₜ2} {A₂} {A₁} h mt1A2=mt2A1)
