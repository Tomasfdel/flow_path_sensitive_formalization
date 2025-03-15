module Transformation {n} where

open import Agda.Builtin.Nat
open import Data.Bool.Base
open import Data.Fin 
  hiding (_≟_ ; _+_)
open import Data.Nat 
  renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties
open import Data.Product 
open import Data.Vec.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import AST {n}

-- Active Sets.
-- TODO(minor): Extract activeSet functions to a separate module?
-- Using a vector to represent a Fin n → ℕ .
𝒜 : Set _
𝒜 = Vec ℕ n

𝒜varCount : {m : ℕ} → Vec ℕ m → ℕ
𝒜varCount [] = 0
𝒜varCount (h1 ∷ t1) = suc h1 + 𝒜varCount t1

-- Active sets merge function from Figure 5 of the paper.
merge𝒜 : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
merge𝒜 [] [] = []
merge𝒜 (h1 ∷ t1) (h2 ∷ t2) =
   (if h1 == h2 then h1 else (suc (h1 ⊔ h2))) ∷ (merge𝒜 t1 t2)

activeSetVarAssignment : Fin n → 𝒜 → 𝒜 → ASTStm
activeSetVarAssignment hInd a a' with lookup a hInd ≟ lookup a' hInd 
...                             | yes _ = SKIP
...                             | no _  = ASSIGN (hInd , (lookup a hInd)) (VAR (hInd , (lookup a' hInd)))

-- TODO(minor): Use a let expression to simplify the last line a little bit.
assignActiveSetAux : {n' : ℕ} (m : ℕ) → m <ₙ n → 𝒜 → 𝒜 → n ≡ (suc n') → ASTStm
assignActiveSetAux zero z<n a a' n=sn' = activeSetVarAssignment (fromℕ< z<n) a a'
assignActiveSetAux (suc m) sm<n a a' n=sn' = SEQ (activeSetVarAssignment (fromℕ< sm<n) a a') 
                                                 (assignActiveSetAux m (subst (\x → m <ₙ x) (sym n=sn') (m<n⇒m<1+n(<-pred (subst (\x → suc m <ₙ x) n=sn' sm<n)))) a a' n=sn')

0<n=>n=sn' : {m : ℕ} → zero <ₙ m → Σ[ m' ∈ ℕ ] (m ≡ suc m')
0<n=>n=sn' (s≤s {zero} {n'} z≤n) = n' , refl

-- := definition for active sets from Figure 4 of the paper.
_:=𝒜_ : 𝒜 → 𝒜 → ASTStm
a :=𝒜 a' with n ≟ zero 
...    | no n<>0 = let n' , n=sn' = 0<n=>n=sn' (n≢0⇒n>0 n<>0)
                    in assignActiveSetAux {n'} n' (subst (\x → n' <ₙ x) (sym n=sn') (n<1+n n')) a a' n=sn'
...    | yes _ = SKIP

-- Expressions transformation.
transExp : ASTExpS → 𝒜 → ASTExp
transExp (IntVal n) _ = INTVAL n
transExp (Var v) active = VAR (v , lookup active v)
transExp (Add e1 e2) active = ADD (transExp e1 active) (transExp e2 active)

-- Program transformation from bracketed to non-bracketed statements,
-- following rules from figure 4 of the paper.
transStm : ASTStmS → 𝒜 → ASTStm × 𝒜
transStm Skip active = (SKIP , active)
transStm (v := e) active = (ASSIGN (v , lookup active v) (transExp e active) , active)
transStm ⟦ v := e ⟧ active = 
   let newIndex = suc (lookup active v) 
   in (ASSIGN (v , newIndex) (transExp e active) , (active [ v ]≔ newIndex) )
transStm (Seq s1 s2) active = 
   let (tS1 , active1) = transStm s1 active
       (tS2 , active2) = transStm s2 active1
   in (SEQ tS1 tS2 , active2)
transStm (If0 cond sT sF) active =
   let tCond = transExp cond active
       (tST , active1) = transStm sT active
       (tSF , active2) = transStm sF active
       active3 = merge𝒜 active1 active2
       trueBranch = SEQ tST (active3 :=𝒜 active1)
       falseBranch = SEQ tSF (active3 :=𝒜 active2)
   in (IF0 tCond trueBranch falseBranch , active3)
transStm (While cond s) active =
   let (_ , active1) = transStm s active
       active2 = merge𝒜 active active1
       (tS , active3) = transStm s active2
       tCond = transExp cond active2
   in (SEQ (active2 :=𝒜 active) 
                          (WHILE tCond 
                                 (SEQ tS (active2 :=𝒜 active3))) , active2)
